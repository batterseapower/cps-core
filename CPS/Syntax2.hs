{-# LANGUAGE PatternGuards #-}
module CPS.Syntax2 where

import GHC.Primitives

import Name
import Utilities

import qualified Data.Map as M
import qualified Data.Set as S


type CoType = [Type]

infixr 7 `FunTy`

data Type = IntHashTy
          | PtrTy
          | FunTy FunTyArg [CoType]
          deriving (Eq, Show)

data FunTyArg = BoxTy | NonBoxTy [Type]
              deriving (Eq, Show)

mkBoxTy :: [CoType] -> Type
mkBoxTy ntys = FunTy BoxTy ntys

mkNonBoxTy :: [Type] -> [CoType] -> Type
mkNonBoxTy tys ntys = FunTy (NonBoxTy tys) ntys

boolTy :: Type
boolTy = mkBoxTy [[], []]

intTy :: Type
intTy = mkBoxTy [[IntHashTy]]

-- x `subType` y if a variable of type x can be applied to a function with argument type y
-- NB: due to the presence of subtyping, types may "improve" during reduction, so we may be able
-- to improve types by reconstructing the types of let-bound arguments and pushing them down to application sites
subType :: Type -> Type -> Bool
IntHashTy      `subType` IntHashTy      = True
IntHashTy      `subType` _              = False
_              `subType` IntHashTy      = False
PtrTy          `subType` PtrTy          = True
PtrTy          `subType` _              = False
_              `subType` PtrTy          = True
FunTy a1 ntys1 `subType` FunTy a2 ntys2 = a2 `subFunTyArg` a1 && allR (allR subType) ntys1 ntys2

subFunTyArg :: FunTyArg -> FunTyArg -> Bool
BoxTy         `subFunTyArg` BoxTy         = True
BoxTy         `subFunTyArg` _             = False
_             `subFunTyArg` BoxTy         = False
NonBoxTy tys1 `subFunTyArg` NonBoxTy tys2 = allR subType tys1 tys2

allR :: (a -> b -> Bool) -> [a] -> [b] -> Bool
allR f = go
  where go []     []             = True
        go (x:xs) (y:ys) | f x y = go xs ys
        go _      _              = False


data Id = Id {
    idName :: Name,
    idType :: Type
  } deriving (Show)

instance Eq Id where (==) = (==) `on` getUnique
instance Ord Id where compare = compare `on` getUnique

data CoId = CoId {
    coIdName :: Name,
    coIdType :: CoType
  } deriving (Show)

instance Eq CoId where (==) = (==) `on` getUnique
instance Ord CoId where compare = compare `on` getUnique


-- Things which are available with literally zero computational effort
-- NB: do not include arithmetic operation applications since we may want to share them
data Trivial = IdOcc Id
             | Literal Literal
             | PrimOp PrimOp
             | Pun Trivial
             | Update [CoType] CoType [CoType]
             deriving (Show)
-- FIXME: add "blackhole"/"update-with-bh" primop (useful if moving update out of a thunk itself statically, as well as at runtime)

-- Interesting simplification rules:
--  * Call to something of boxy type with a single no-args cont can be simplified to a call to that cont
--  * No need to update things that are already values: perhaps we can do this by evaluating an update directly in the RHS of the updatee at compile time.
--    Note that if we start shifting updates around we can't just evaluate *any* update whenever we see an update to a let-bound thing, because there may
--    be two syntactically distinct updates to the same variable e.g. after simplifying (let x = case y of A -> B; B -> A in case x of A -> e1; B -> e2)
--  * Updating a pun can just be dropped (NB: check this makes sense)
--  * Continuations should be floated as far in as possible because that ensures they are syntactically nested within their dominators, which
--    can expose information available at all call sites
--  * We can do pun introduction: we can simplify x <> (\<x'>. e) to x <> (\<x'>. e[pun x'/x]). This is one of the rules where floating continuations
--    maximally in is useful.

-- FIXME: have a CoTrivial with a polymorphic "unreachable" as well as monotyped "halt"?

data Function = Function [Id] [CoId] Term | Box [CoType] [Trivial] [CoType]
              deriving (Show)

data Continuation = Continuation [Id] Term
                  deriving (Show)

data Term = Term [(Id, Function)] [(CoId, Continuation)] Transfer
          deriving (Show)

data Transfer = Return CoId [Trivial]
              | Call Trivial [Trivial] [CoId]
              deriving (Show)

instance Pretty Type where
    pPrintPrec level prec ty = case ty of
      IntHashTy    -> text "Int#"
      PtrTy        -> text "*"
      FunTy a ntys -> prettyParen (prec >= appPrec) $ pPrintPrec level appPrec a <+> text "->" <+> pPrintPrecAlty level noPrec [PrettyFunction $ \level prec -> pPrintPrecMulti level prec nty | nty <- ntys]

instance Pretty FunTyArg where
    pPrintPrec level prec a = case a of
      BoxTy         -> text "<!>"
      NonBoxTy tys  -> pPrintPrecMulti level prec tys

instance Pretty Id where
    pPrintPrec level prec = pPrintPrec level prec . idName

instance Pretty CoId where
    pPrintPrec level prec = pPrintPrec level prec . coIdName

instance Pretty Trivial where
    pPrintPrec level prec t = case t of
      IdOcc x               -> pPrintPrec level prec x
      Literal l             -> pPrintPrec level prec l
      PrimOp pop            -> pPrintPrec level prec pop
      Pun t                 -> pPrintPrec level prec t
      Update ntys1 nt ntys2 -> pPrintPrecFunny level prec (text "Update") ntys1 nt ntys2

instance Pretty Function where
    pPrintPrec level prec f = case f of
      Function xs us e   -> pPrintPrecLams level prec [PrettyFunction $ \level prec -> pPrintPrecMulti level prec xs, PrettyFunction $ \level prec -> pPrintPrecMulti level prec us] e
      Box ntys1 ts ntys2 -> pPrintPrecFunny level prec (text "Box") ntys1 ts ntys2

instance Pretty Continuation where
    pPrintPrec level prec (Continuation xs e) = pPrintPrecLams level prec [PrettyFunction $ \level prec -> pPrintPrecMulti level prec xs] e

instance Pretty Term where
    pPrintPrec level prec (Term xfs uks r) = pPrintPrecLetRec level prec ([(asPrettyFunction x, asPrettyFunction f) | (x, f) <- xfs] ++ [(asPrettyFunction u, asPrettyFunction k) | (u, k) <- uks]) r

instance Pretty Transfer where
    pPrintPrec level prec r = case r of
      Return u ts -> pPrintPrecApps level prec u ts
      Call t ts us -> pPrintPrecApps level prec t [PrettyFunction $ \level prec -> pPrintPrecMulti level prec ts, PrettyFunction $ \level prec -> pPrintPrecMulti level prec us]

pPrintPrecFunny :: (Pretty a, Pretty b, Pretty c, Pretty d) => PrettyLevel -> Rational -> a -> [[b]] -> [c] -> [[d]] -> Doc
pPrintPrecFunny level prec hd ntys1 ts ntys2 = pPrintPrecApps level prec hd [PrettyFunction $ \level prec -> pPrintPrecAlty level prec $ [PrettyFunction $ \level prec -> pPrintPrecMulti level prec nty | nty <- ntys1] ++
                                                                                                                                         [PrettyFunction $ \level prec -> text "!" <> pPrintPrecMulti level prec ts] ++
                                                                                                                                         [PrettyFunction $ \level prec -> pPrintPrecMulti level prec nty | nty <- ntys2]]

pPrintPrecMulti :: Pretty a => PrettyLevel -> Rational -> [a] -> Doc
pPrintPrecMulti level prec [x] = pPrintPrec level prec x
pPrintPrecMulti level prec xs  = prettyAngles (prec >= appPrec) $ hsep (punctuate (text ",") [pPrintPrec level noPrec x | x <- xs])
 -- Experimental pretty-printing change: skip the angle brackets if we can avoid it, so that True is (Box <|!>) rather than (Box <<>|!<>>).
 -- FIXME: as a consequence we do get (<> -> Int#,Int#) instead of (<> -> <Int#,Int#>), but maybe that is OK?

prettyAngles :: Bool -> Doc -> Doc
prettyAngles False = id
prettyAngles True  = angles

pPrintPrecAlty :: Pretty a => PrettyLevel -> Rational -> [a] -> Doc
pPrintPrecAlty level prec [x] = pPrintPrec level prec x
pPrintPrecAlty level _    xs  = angles (hcat (intersperse (text "|") [pPrintPrec level noPrec x | x <- xs]))

pPrintPrecLams :: (Pretty a, Pretty b) => PrettyLevel -> Rational -> [a] -> b -> Doc
pPrintPrecLams level prec xs e = prettyParen (prec > noPrec) $ text "\\" <> hsep [pPrintPrec level appPrec y | y <- xs] <+> text "->" <+> pPrintPrec level noPrec e


newtype LintM a = LintM { unLintM :: [Doc] -> ([Doc], a) }

instance Monad LintM where
    return x = LintM $ \doc -> (doc, x)
    mx >>= fxmy = LintM $ \doc -> case unLintM mx doc of (doc, x) -> unLintM (fxmy x) doc

runLintM :: LintM () -> [Doc]
runLintM mx = case unLintM mx [] of (docs, ()) -> docs

warnM :: [Doc] -> LintM ()
warnM xs = LintM $ \docs -> (xs ++ docs, ())

lintDistinct :: (Pretty a, Ord a) => Doc -> [a] -> LintM ()
lintDistinct what xs = warnM [what <+> text "not distinct: " <+> pPrint xs | allDistinct xs == False]

lintTerm :: UniqueMap Type -> UniqueMap CoType -> Term -> LintM ()
lintTerm x_tys u_ntys (Term xfs uks r) = do
    x_tys  <- lintIdBinders   x_tys  (map fst xfs)
    u_ntys <- lintCoIdBinders u_ntys (map fst uks)
    mapM_ (uncurry (lintFunction     x_tys))        xfs
    mapM_ (uncurry (lintContinuation x_tys u_ntys)) uks
    lintTransfer x_tys u_ntys r

lintIdBinders :: UniqueMap Type -> [Id] -> LintM (UniqueMap Type)
lintIdBinders x_tys xs = do
    lintDistinct (text "Id binders") xs
    return x_tys'
  where x_tys' = foldr (\x -> insertUniqueMap x (idType x)) x_tys xs

lintCoIdBinders :: UniqueMap CoType -> [CoId] -> LintM (UniqueMap CoType)
lintCoIdBinders u_ntys us = do
    lintDistinct (text "CoId binders") us
    return u_ntys'
  where u_ntys' = foldr (\u -> insertUniqueMap u (coIdType u)) u_ntys us

lintFunction :: UniqueMap Type -> Id -> Function -> LintM ()
lintFunction x_tys x f = do
    case f of Function xs us e -> do
                x_tys  <- lintIdBinders   x_tys          xs
                u_ntys <- lintCoIdBinders emptyUniqueMap us
                lintTerm x_tys u_ntys e
              Box _ ts _ -> mapM_ (lintTrivial x_tys) ts
    warnM [hang (pPrint x <+> text "RHS type incompatible") 2
            (text "Bound as:" <+> pPrint (idType x) $$
             text "RHS is:" <+> pPrint (functionType f))
          | not (functionType f `subType` idType x)]

lintContinuation :: UniqueMap Type -> UniqueMap CoType -> CoId -> Continuation -> LintM ()
lintContinuation x_tys u_ntys u k@(Continuation xs e) = do
    x_tys <- lintIdBinders x_tys xs
    lintTerm x_tys u_ntys e
    warnM [hang (pPrint u <+> text "RHS cotype incompatible") 2
            (text "Bound as:" <+> pPrint (coIdType u) $$
             text "RHS is:" <+> pPrint (continuationCoType k))
          | not (allR subType (coIdType u) (continuationCoType k))]

lintTransfer :: UniqueMap Type -> UniqueMap CoType -> Transfer -> LintM ()
lintTransfer x_tys u_ntys (Return u ts) = do
    lintCoId u_ntys u
    mapM_ (lintTrivial x_tys) ts
    warnM [hang (pPrint u <+> text "return type incompatible:") 2
            (text "Applied:" <+> pPrint ts <+> text "::" <+> pPrint (map trivialType ts) $$
             text "Expected:" <+> pPrint (coIdType u))
          | not (allR subType (map trivialType ts) (coIdType u))]
lintTransfer x_tys u_ntys (Call t ts us) = do
    lintTrivial x_tys t
    mapM_ (lintTrivial x_tys) ts
    mapM_ (lintCoId u_ntys) us
    ntys <- case trivialType t of
      FunTy BoxTy          ntys -> do
        warnM [pPrint t <+> text "unpack call with non-null value arguments" | not (null ts)]
        return ntys
      FunTy (NonBoxTy tys) ntys -> do
        warnM [hang (pPrint t <+> text "call arguments incompatible:") 2
                (text "Applied:" <+> pPrint ts <+> text "::" <+> pPrint (map trivialType ts) $$
                 text "Expected:" <+> pPrint tys)
              | not (allR subType (map trivialType ts) tys)]
        return ntys
    warnM [hang (pPrint t <+> text "call result incompatible:") 2
            (text "Applied:" <+> pPrint us <+> text "::" <+> pPrint (map coIdType us) $$
             text "Expected:" <+> pPrint ntys)
          | not (allR (allR subType) (map coIdType us) ntys)]

lintTrivial :: UniqueMap Type -> Trivial -> LintM ()
lintTrivial x_tys (IdOcc x) = case lookupUniqueMap x x_tys of
    Nothing   -> warnM [pPrint x <+> text "out of scope"]
    Just x_ty -> warnM [pPrint x <+> text "occurrence type not up to date" | x_ty /= idType x]
lintTrivial x_tys (Pun t) = lintTrivial x_tys t
lintTrivial _ (Literal _)    = return ()
lintTrivial _ (PrimOp _)     = return ()
lintTrivial _ (Update _ _ _) = return ()

lintCoId :: UniqueMap CoType -> CoId -> LintM ()
lintCoId u_ntys u = case lookupUniqueMap u u_ntys of
    Nothing   -> warnM [pPrint u <+> text "out of scope"]
    Just u_ty -> warnM [pPrint u <+> text "occurrence type not up to date" | u_ty /= coIdType u]


literalType :: Literal -> Type
literalType (Int _) = IntHashTy

primOpType :: PrimOp -> Type
primOpType pop
  | pop `elem` [Add, Subtract, Multiply, Divide, Modulo]
  = mkNonBoxTy [IntHashTy, IntHashTy] [[IntHashTy]]
  | pop `elem` [Equal, LessThan, LessThanEqual]
  = mkNonBoxTy [IntHashTy, IntHashTy] [[boolTy]] -- FIXME: it might be caller if primops return "unboxed bools" so we could use them in e.g. literal-case desugarings + optimize the boxing away?

trivialType :: Trivial -> Type
trivialType (IdOcc x)               = idType x
trivialType (Literal l)             = literalType l
trivialType (PrimOp pop)            = primOpType pop
trivialType (Pun t)                 = mkNonBoxTy [] [[trivialType t]] -- NB: Pun cannot be more general than this because there is no room to store which continuation to return down
trivialType (Update ntys1 nt ntys2) = mkNonBoxTy (thunk_ty:nt) [nt]   -- NB: this is generalised to update thunks with more than one continuation or continuations with more than one argument
  where thunk_ty = mkNonBoxTy [] (ntys1 ++ [nt] ++ ntys2)

functionType :: Function -> Type
functionType (Function xs us _)   = mkNonBoxTy (map idType xs) (map coIdType us)
functionType (Box ntys1 ts ntys2) = mkBoxTy (ntys1 ++ [map trivialType ts] ++ ntys2)

continuationCoType :: Continuation -> CoType
continuationCoType (Continuation xs _) = map idType xs


instance Uniqueable Id where
    getUnique = getUnique . idName

instance Uniqueable CoId where
    getUnique = getUnique . coIdName


newtype IdSubst = IdSubst { unIdSubst :: UniqueMap Trivial }

mkIdSubst :: S.Set Id -> IdSubst
mkIdSubst xs = IdSubst (M.fromList [(getUnique x, IdOcc x) | x <- S.toList xs])

newtype CoIdSubst = CoIdSubst { unCoIdSubst :: UniqueMap CoId }

mkCoIdSubst :: S.Set CoId -> CoIdSubst
mkCoIdSubst us = CoIdSubst (M.fromList [(getUnique u, u) | u <- S.toList us])

data Subst = Subst { idSubst :: IdSubst, coIdSubst :: CoIdSubst }

emptySubst :: Subst
emptySubst = Subst { idSubst = IdSubst M.empty, coIdSubst = CoIdSubst M.empty }

substFromIdSubst :: IdSubst -> Subst
substFromIdSubst idsubst = Subst { idSubst = idsubst, coIdSubst = CoIdSubst M.empty }

substFromCoIdSubst :: CoIdSubst -> Subst
substFromCoIdSubst coidsubst = Subst { idSubst = IdSubst M.empty, coIdSubst = coidsubst }


renameIdBinder' :: InScopeSet -> IdSubst -> Id -> (InScopeSet, IdSubst, Id)
renameIdBinder' iss idsubst x = (iss', IdSubst (insertUniqueMap n (IdOcc x') (unIdSubst idsubst)), x')
  where n = idName x
        (iss', n') = uniqAwayName iss n
        x' = x { idName = n' } -- NB: don't need to rename types

renameIdBinder :: InScopeSet -> Subst -> Id -> (InScopeSet, Subst, Id)
renameIdBinder iss subst x = (iss', subst { idSubst = idsubst' }, x')
  where (iss', idsubst', x') = renameIdBinder' iss (idSubst subst) x

renameCoIdBinder' :: InScopeSet -> CoIdSubst -> CoId -> (InScopeSet, CoIdSubst, CoId)
renameCoIdBinder' iss coidsubst u = (iss', CoIdSubst (insertUniqueMap n u' (unCoIdSubst coidsubst)), u')
  where n = coIdName u
        (iss', n') = uniqAwayName iss n
        u' = u { coIdName = n' } -- NB: don't need to rename types

renameCoIdBinder :: InScopeSet -> Subst -> CoId -> (InScopeSet, Subst, CoId)
renameCoIdBinder iss subst u = (iss', subst { coIdSubst = coidsubst' }, u')
  where (iss', coidsubst', u') = renameCoIdBinder' iss (coIdSubst subst) u

renameBinders :: (iss -> subst -> a -> (iss, subst, b))
              -> iss -> subst -> [a] -> (iss, subst, [b])
renameBinders rename = curry ((unnest .) . mapAccumL (\(ids, subst) -> nest . rename ids subst))
  where unnest ((a, b), c) = (a, b, c)
        nest (a, b, c) = ((a, b), c)

renameId :: IdSubst -> Id -> Trivial
renameId idsubst x = findUniqueWithDefault (error "renameId: out of scope") x (unIdSubst idsubst)

renameCoId :: CoIdSubst -> CoId -> CoId
renameCoId coidsubst u = findUniqueWithDefault (error "renameCoId: out of scope") u (unCoIdSubst coidsubst)

insertIdRenaming :: Id -> Trivial -> Subst -> Subst
insertIdRenaming x t' subst = subst { idSubst = IdSubst (insertUniqueMap x t' (unIdSubst (idSubst subst))) }

insertCoIdRenaming :: CoId -> CoId -> Subst -> Subst
insertCoIdRenaming u u' subst = subst { coIdSubst = CoIdSubst (insertUniqueMap u u' (unCoIdSubst (coIdSubst subst))) }

insertRenamings :: (a -> b -> Subst -> Subst)
                -> [a] -> [b] -> Subst -> Subst
insertRenamings insert xs ys subst = foldl' (\subst (x, y) -> insert x y subst) subst (xs `zip` ys)


renameTrivial :: IdSubst -> Trivial -> Trivial
renameTrivial idsubst (IdOcc x)               = renameId idsubst x
renameTrivial _       (Literal x)             = Literal x
renameTrivial _       (PrimOp pop)            = PrimOp pop
renameTrivial idsubst (Pun t)                 = Pun (renameTrivial idsubst t)
renameTrivial _       (Update ntys1 nt ntys2) = Update ntys1 nt ntys2


renameFunction :: InScopeSet -> IdSubst -> Function -> Function
renameFunction iss0 idsubst0 (Function xs us e) = Function xs' us' (renameTerm iss2 subst2 e)
  where (iss1, idsubst1, xs') = renameBinders renameIdBinder'  iss0                   idsubst0  xs
        (iss2, subst2,   us') = renameBinders renameCoIdBinder iss1 (substFromIdSubst idsubst1) us
renameFunction _    idsubst0 (Box tys0 ts tys1) = Box tys0 (map (renameTrivial idsubst0) ts) tys1

renameContinuation :: InScopeSet -> Subst -> Continuation -> Continuation
renameContinuation iss0 subst0 (Continuation xs e) = Continuation xs' (renameTerm iss1 subst1 e)
  where (iss1, subst1, xs') = renameBinders renameIdBinder iss0 subst0 xs

renameTerm :: InScopeSet -> Subst -> Term -> Term
renameTerm iss0 subst0 (Term xfs uks r) = Term (xs' `zip` map (renameFunction iss2 (idSubst subst2)) fs)
                                               (us' `zip` map (renameContinuation iss2 subst2) ks)
                                               (renameTransfer subst2 r)
  where (xs, fs) = unzip xfs
        (us, ks) = unzip uks
        (iss1, subst1, xs') = renameBinders renameIdBinder   iss0 subst0 xs
        (iss2, subst2, us') = renameBinders renameCoIdBinder iss1 subst1 us

renameTransfer :: Subst -> Transfer -> Transfer
renameTransfer subst (Return u ts)  = Return (renameCoId (coIdSubst subst) u) (map (renameTrivial (idSubst subst)) ts)
renameTransfer subst (Call t ts us) = Call (renameTrivial (idSubst subst) t) (map (renameTrivial (idSubst subst)) ts) (map (renameCoId (coIdSubst subst)) us)


trivialFreeIds :: Trivial -> S.Set Id
trivialFreeIds (IdOcc x)      = S.singleton x
trivialFreeIds (Literal _)    = S.empty
trivialFreeIds (PrimOp _)     = S.empty
trivialFreeIds (Update _ _ _) = S.empty
trivialFreeIds (Pun t)        = trivialFreeIds t


type Heap = M.Map Id (IdSubst, Function)

type Stack = [M.Map CoId (Subst, Continuation)]

stackLookup :: CoId -> Stack -> Maybe ((Subst, Continuation), Stack)
stackLookup _ []     = Nothing
stackLookup u (kf:k) = case M.lookup u kf of
    Just res -> Just (res, kf:k)
    Nothing  -> stackLookup u k

type State = (InScopeSet, Heap, (Subst, Term), Stack)

addFunction :: Id -> Function -> Term -> Term
addFunction x f (Term xfs uks r) = Term ((x, f) : xfs) uks r

addContinuation :: CoId -> Continuation -> Term -> Term
addContinuation u k (Term xfs uks r) = Term xfs ((u, k) : uks) r

stateToTerm :: State -> Term
stateToTerm (iss, h, (subst, e), k) = flip (foldr (\(x, (idsubst, f)) -> addFunction x (renameFunction iss idsubst f))) (M.toList h) $
                                      flip (foldr (\kf -> flip (foldr (\(u, (subst, k)) -> addContinuation u (renameContinuation iss subst k))) (M.toList kf))) k $
                                      renameTerm iss subst e

-- FIXME: blackholing. When we first enter we should blackhole the thunk: x |-> \<> k. blackhole <> <>

-- Principal: it's OK to error out if the term is badly typed, but not if some information is missing
-- NB: the output type is guaranteed to be a *subtype* of the input type. In representation-type systems
-- with subtyping reduction may improve the type e.g.:
--
-- let id :: forall a. a -> a = /\a. \(x :: a). x
--     f :: Int -> Int = id @Int
-- in id @(Int -> Int) f :: Int -> Int
--
-- let id :: * -> * = \(x :: *). x
--     f :: * -> * = id
-- in id f :: *
--
-- let id :: * -> * = \(x :: *). x
--     f :: * -> * = id
-- in f :: * -> *
step :: State -> Maybe State
step (iss0, h, (subst0, Term xfs uks r), k) = case renameTransfer subst2 r of
    Return u' ts'   -> return_step (iss2, h', (u', ts'), k')
    Call t' ts' us' -> case t' of
      IdOcc x' -> do
        (idsubst, f) <- M.lookup x' h'
        case f of Function ys vs e
                    -> return (iss2, h', (insertRenamings insertIdRenaming ys ts' (insertRenamings insertCoIdRenaming vs us' (substFromIdSubst idsubst)), e), k')
                  Box  tys ss _
                    | [] <- ts'
                    , Just u' <- us' `at` length tys
                    -> return_step (iss2, h', (u', map (renameTrivial idsubst) ss), k')
                    | otherwise
                    -> error "step: untypeable call to IdOcc?"
      Update ntys1 _ ntys2 | (IdOcc x':ts_update') <- ts', [u'] <- us' -> -- NB: updating anything other than IdOcc is impossible (Pun is the only type-correct one, but such a thing is guaranteed to be updated, and with self-update we won't encounter that) (FIXME: can be cleaner?)
        return_step (iss2, M.insert x' (mkIdSubst (S.unions (map trivialFreeIds ts_update')), Box ntys1 ts_update' ntys2) h', (u', ts_update'), k')
        -- NB: we *can* do update-in-place for thunks in general, but do we want to?
        -- In the common case where (length ts_update' == 1) and the thing updated with is a box, it is unambiguously good:
        -- any extra heap allocation can be eliminated by the GC when it collapses indirections (using punning). But if we do
        -- it in general then we risk overwriting several heap cells with the same Boxes!
        --
        -- One thing is clear: the compiler must be very careful when it introduces one of these boxes. Perhaps it should only
        -- do so when it is clear that the thunk will not in fact be updated (think about CPR).
      PrimOp pop | Just t' <- stepPrimOp pop ts', [u'] <- us' ->
        return_step (iss2, h', (u', [t']), k')
      Pun t' | [] <- ts', [u'] <- us' -> -- FIXME: this means that Puns could be a primop, right?
        return_step (iss2, h', (u', [t']), k')
      _ -> error "step: untypeable call to non-IdOcc?"
  where
    (xs, fs) = unzip xfs
    (us, ks) = unzip uks
    (iss1, subst1, xs') = renameBinders renameIdBinder   iss0 subst0 xs
    (iss2, subst2, us') = renameBinders renameCoIdBinder iss1 subst1 us
    h' = M.fromList (xs' `zip` map ((,) (idSubst subst2)) fs) `M.union` h
    k' = M.fromList (us' `zip` map ((,) subst2)           ks) : k

    return_step (iss, h, (u', ts'), k) = do
        ((subst, Continuation ys e), k) <- stackLookup u' k
        return (iss, h, (insertRenamings insertIdRenaming ys ts' subst, e), k)

stepPrimOp :: PrimOp -> [Trivial] -> Maybe Trivial
stepPrimOp pop = case pop of
    Add           -> int_int_int (+)
    Subtract      -> int_int_int (+)
    Multiply      -> int_int_int (*)
    Divide        -> int_int_int div
    Modulo        -> int_int_int mod
    Equal         -> int_int_bool (==)
    LessThan      -> int_int_bool (==)
    LessThanEqual -> int_int_bool (==)
  where
    int_int_int f [Literal (Int i1), Literal (Int i2)] = Just (Literal (Int (f i1 i2)))
    int_int_int _ _ = Nothing
    
    int_int_bool f [Literal (Int i1), Literal (Int i2)] = error "FIXME: stepPrimOp with Bool result" (f i1 i2)
    int_int_bool _ _ = Nothing
