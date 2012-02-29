{-# LANGUAGE PatternGuards #-}
module CPS.Syntax2 where

import GHC.Primitives

import Name
import Utilities

import qualified Data.Map as M
import qualified Data.Set as S


type CoType = [Type]

data Type = IntHashTy
          | PtrTy
          | FunTy FunTyArg [CoType]

data FunTyArg = BoxTy | NonBoxTy [Type]

mkBoxTy :: [CoType] -> Type
mkBoxTy ntys = FunTy BoxTy ntys

mkNonBoxTy :: [Type] -> [CoType] -> Type
mkNonBoxTy tys ntys = FunTy (NonBoxTy tys) ntys

boolTy :: Type
boolTy = mkBoxTy [[], []]

intTy :: Type
intTy = mkBoxTy [[IntHashTy]]


data Id = Id {
    idName :: Name,
    idType :: Type
  }

instance Eq Id where (==) = (==) `on` getUnique
instance Ord Id where compare = compare `on` getUnique

data CoId = CoId {
    coIdName :: Name,
    coIdType :: CoType
  }

instance Eq CoId where (==) = (==) `on` getUnique
instance Ord CoId where compare = compare `on` getUnique


-- Things which are available with literally zero computational effort
-- NB: do not include arithmetic operation applications since we may want to share them
data Trivial = IdOcc Id
             | Literal Literal
             | PrimOp PrimOp
             | Pun Trivial
             | Update [CoType] CoType [CoType]

-- NB: interesting simplification rule: call to something of boxed type with single no-args cont can be simplified to a call to that cont

-- FIXME: have a CoTrivial with a polymorphic "unreachable" and monotyped "halt"?

data Function = Function [Id] [CoId] Term | Box [CoType] [Trivial] [CoType]

data Continuation = Continuation [Id] Term

data Term = Term [(Id, Function)] [(CoId, Continuation)] Transfer

data Transfer = Return CoId [Trivial]
              | Call Trivial [Trivial] [CoId]


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


type UniqueMap a = M.Map Unique a

class Uniqueable k where
    getUnique :: k -> Unique

instance Uniqueable Unique where
    getUnique = id

instance Uniqueable Name where
    getUnique = nameUnique

instance Uniqueable Id where
    getUnique = getUnique . idName

instance Uniqueable CoId where
    getUnique = getUnique . coIdName

insertUniqueMap :: Uniqueable k => k -> a -> UniqueMap a -> UniqueMap a
insertUniqueMap k v = M.insert (getUnique k) v

lookupUniqueMap :: Uniqueable k => k -> UniqueMap a -> Maybe a
lookupUniqueMap k = M.lookup (getUnique k)

findUniqueWithDefault :: Uniqueable k => a -> k -> UniqueMap a -> a
findUniqueWithDefault def k = M.findWithDefault def (getUnique k)


newtype IdSubst = IdSubst { unIdSubst :: UniqueMap Trivial }

mkIdSubst :: S.Set Id -> IdSubst
mkIdSubst xs = IdSubst (M.fromList [(getUnique x, IdOcc x) | x <- S.toList xs])

newtype CoIdSubst = CoIdSubst { unCoIdSubst :: UniqueMap CoId }

data Subst = Subst { idSubst :: IdSubst, coIdSubst :: CoIdSubst }

emptySubst :: Subst
emptySubst = Subst { idSubst = IdSubst M.empty, coIdSubst = CoIdSubst M.empty }

substFromIdSubst :: IdSubst -> Subst
substFromIdSubst idsubst = Subst { idSubst = idsubst, coIdSubst = CoIdSubst M.empty }

newtype InScopeSet = ISS { unISS :: S.Set Unique }

uniqAway :: InScopeSet -> Unique -> (InScopeSet, Unique)
uniqAway (ISS iss) = go
  where go u | u `S.member` iss = go (bumpUnique u)
             | otherwise        = (ISS (S.insert u iss), u)

uniqAwayName :: InScopeSet -> Name -> (InScopeSet, Name)
uniqAwayName iss n = (iss', n { nameUnique = u' })
  where (iss', u') = uniqAway iss (nameUnique n)

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


type Heap = UniqueMap (IdSubst, Function)

type Stack = [UniqueMap (Subst, Continuation)]

stackLookup :: CoId -> Stack -> Maybe ((Subst, Continuation), Stack)
stackLookup _ []     = Nothing
stackLookup u (kf:k) = case lookupUniqueMap u kf of
    Just res -> Just (res, kf:k)
    Nothing  -> stackLookup u k

type State = (InScopeSet, Heap, (Subst, Term), Stack)

-- Principal: it's OK to error out if the term is badly typed, but not if some information is missing
step :: State -> Maybe State
step (iss0, h, (subst0, Term xfs uks r), k) = case renameTransfer subst2 r of
    Return u' ts'   -> return_step (iss2, h', (u', ts'), k')
    Call t' ts' us' -> case t' of
      IdOcc x' -> do
        (idsubst, f) <- lookupUniqueMap x' h
        case f of Function ys vs e
                    -> return (iss2, h', (insertRenamings insertIdRenaming ys ts' (insertRenamings insertCoIdRenaming vs us' (substFromIdSubst idsubst)), e), k')
                  Box  tys ss _
                    | [] <- ts'
                    , Just u' <- us' `at` length tys
                    -> return_step (iss2, h', (u', map (renameTrivial idsubst) ss), k')
                    | otherwise
                    -> error "step: untypeable call to IdOcc?"
      Update ntys1 _ ntys2 | (IdOcc x':ts_update') <- ts', [u'] <- us' -> -- NB: updating anything other than IdOcc is impossible (Pun is the only type-correct one, but such a thing is guaranteed to be updated, and with self-update we won't encounter that) (FIXME: can be cleaner?)
        return_step (iss2, insertUniqueMap x' (mkIdSubst (S.unions (map trivialFreeIds ts_update')), Box ntys1 ts_update' ntys2) h', (u', ts_update'), k')
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
    h' = M.fromList (map getUnique xs' `zip` map ((,) (idSubst subst2)) fs) `M.union` h
    k' = M.fromList (map getUnique us' `zip` map ((,) subst2)           ks) : k

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
