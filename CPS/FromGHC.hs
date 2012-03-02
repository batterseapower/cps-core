{-# LANGUAGE PatternGuards #-}
module CPS.FromGHC where

import CPS.Syntax hiding (Subst, renameIdBinder)

import qualified GHC.Data as G
import qualified GHC.Var as G
import qualified GHC.Syntax as G
import qualified GHC.Type as G
import qualified GHC.Kind as G
import GHC.Primitives

import Name
import Utilities

-- FIXME: it might be easier to just permit unboxed tuples everywhere, including inside other unboxed tuples and on the left-hand-side of function arrows.
--        The only wrinkle is that fromId may have to manufacture some fresh names.
-- FIXME: we can even permit unboxed tuples as e.g. arguments to (,)! Of course, you can't use such types as arguments to polymorphic functions (ill-kinded type application).
--        In GHC we would also have to be careful about what info tables such things get -- we can't reuse the polymorphic one (closure layout will change).


-- NB: the input type must be of a TypeKind kind
-- NB: the type returned is the *unlifted* version of the type
-- NB: may return multiple types for unboxed tuples
-- NB: do not look through newtypes here or we may produce an infinite type
fromType :: G.Type -> [Type]
fromType (G.ForAllTy _ ty) = fromType ty
fromType ty = case G.splitTyConAppTy_maybe ty of
    Just (tc, [_, _])
      | tc == G.funTyCon             -> [PtrTy]
      | Just _ <- G.isEqHashTyCon tc -> []
      | tc == G.pairTyCon            -> [PtrTy]
    Just (tc, [])
      | tc == G.boolTyCon    -> [PtrTy]
      | tc == G.intTyCon     -> [PtrTy]
      | tc == G.intHashTyCon -> [IntHashTy]
    Just (tc, tys)
      | Just n <- G.isUnboxedTupleTyCon_maybe tc
      , n == length tys
      -> concatMap fromTypeThunky tys -- NB: this does not actualy permit nested unboxed tuples, the list is needed if some components are void
    Just _ -> error "fromType: unrecognised explicit TyCon"
    Nothing -> case G.typeKind ty of
        G.LiftedTypeKind -> [PtrTy]
        _                -> error "fromType: non-TyCon non-lifted type"
        -- GHC currently has a bug where you can lambda-abstract over type variables of non-lifted kind.
        -- This is a serious problem because there is no way to reliably determine the representation of
        -- that type variable. This becomes explicit in our translation.
        --
        -- FIXME: we should allow such types in *result* positions (e.g. for error :: forall (a :: OPEN). a).
        -- In this case, we can return [] on the understanding that such functions can never return.

-- NB: the input type must be lifted
fromLiftedType :: G.Type -> Type
fromLiftedType ty = case fromType ty of
    [ty] -> ty
    _    -> error "fromLiftedType: non-unary input type - must be an unboxed tuple or void unlifted type"

-- NB: the input type must be lifted
fromLiftedTypeThunky :: G.Type -> Type
fromLiftedTypeThunky ty = case fromTypeThunky ty of
    [ty] -> ty
    _    -> error "fromLiftedTypeThunky: non-unary input type - must be an unboxed tuple or void unlifted type"

fromTypeThunky :: G.Type -> [Type]
fromTypeThunky ty
  | G.typeKind ty /= G.LiftedTypeKind = fromType ty
  | otherwise                         = [PtrTy]

-- We don't have to worry about occurrences of unboxed tuple Ids, but void Ids may occur
fromId :: G.Id -> [Id]
fromId x = case fromTypeThunky (G.idType x) of
    []   -> []
    [ty] -> [Id { idName = G.idName x, idType = ty }]
    _    -> error "fromId: unboxed tuple Ids are not present in the input"

-- NB: the type of the input Id must be lifted
fromLiftedId :: G.Id -> Id
fromLiftedId x = case fromId x of [x] -> x
                                  _   -> error "fromLiftedId: void input Id"

type Context = (UniqueSupply, InScopeSet)

type Subst = UniqueMap (Maybe Trivial)
type In a = (Subst, a)

instance Uniqueable G.Id where
    getUnique = getUnique . G.idName

rename :: Subst -> G.Id -> Maybe Trivial
rename subst x = findUniqueWithDefault (error "rename: out of scope") x subst

renameLifted :: Subst -> G.Id -> Trivial
renameLifted subst x = case rename subst x of
    Just t  -> t
    Nothing -> error "renameLifted: binding not lifted"

renameIdBinder :: Context -> Subst -> G.Id -> (Context, Subst, Maybe Id)
renameIdBinder ids subst x = (ids', insertUniqueMap x (fmap IdOcc mb_x') subst, mb_x')
  where
    (ids', mb_x') = renameIdBinder' ids x

    renameIdBinder' :: Context -> G.Id -> (Context, Maybe Id)
    renameIdBinder' (ids, iss) x = case fromTypeThunky (G.idType x) of
        []   -> ((ids, iss),  Nothing)
        [ty] -> ((ids, iss'), Just x')
          where n = G.idName x
                (iss', n') = uniqAwayName iss n
                x' = Id { idName = n', idType = ty } -- NB: don't need to rename types
        _ -> error "renameIdBinder': unboxed tuple binders are always dead"

--renameBinders :: Context -> Subst -> [G.Id] -> (Context, Subst, [Maybe Id])
--renameBinders ids subst = third3 catMaybes . mapAccumL (\(ids, subst) x -> case renameBinder ids subst x of (ids, subst, mb_x') -> ((ids, subst, mb_x'))) (ids, subst)


freshId :: Context -> String -> Type -> (Context, Id)
freshId (ids, iss) s ty = ((ids', iss'), Id { idName = n', idType = ty })
  where (ids', n) = freshName ids s
        (iss', n') = uniqAwayName iss n

freshCoId :: Context -> String -> CoType -> (Context, CoId)
freshCoId (ids, iss) s nty = ((ids', iss'), CoId { coIdName = n', coIdType = nty })
  where (ids', n) = freshName ids s
        (iss', n') = uniqAwayName iss n

freshs :: (Context -> String -> a -> (Context, b))
       -> Context -> String -> [a] -> (Context, [b])
freshs fresh ids s tys = mapAccumL (\ids ty -> fresh ids s ty) ids tys


-- fromTerm ids (subst, e) u
--
-- NB: 
--   fromType (termType e) `allR subType` coIdType u
--   FVs are available in the environment of the output with their *thunky* types
data Kont = Unknown CoId
          | Known [Type] (Context -> [Trivial] -> Term)

returnToKont :: Kont -> Context -> [Trivial] -> Term
returnToKont (Unknown u) _   ts = Term [] [] (Return u ts)
returnToKont (Known _ f) ids ts = f ids ts

bindKont :: Kont -> Context -> (Context -> CoId -> Term) -> Term
bindKont (Unknown u)   ids  nested =                      nested ids  u
bindKont (Known tys f) ids0 nested = addContinuation u k (nested ids2 u) -- FIXME: should tys come from bindCont caller? (Casts)
  where k = Continuation xs (f ids2 (map IdOcc xs))
        (ids1, u)  = freshCoId ids0 "u" (continuationCoType k)
        (ids2, xs) = freshs freshId ids1 "x" tys

fromTerm :: Context -> In G.Term -> Kont -> Term
fromTerm ids (subst, G.Var x) u
  | G.typeKind (G.idType x) /= G.LiftedTypeKind = returnToKont u ids (maybeToList (rename subst x))
  | otherwise                                   = bindKont u ids $ \_ u -> Term [] [] (Call (renameLifted subst x) (Enter []) [u])
fromTerm ids0 (subst, G.Value v) u = case v of
    G.Coercion _ -> returnToKont u ids0 []
    G.Lambda (G.ATyVar _) e -> fromTerm ids0 (subst, e) u
    G.Lambda (G.AnId x) e -> addFunction y f (returnToKont u ids1 [IdOcc y])
     where (ids1, y) = freshId ids0 "fun" PtrTy
           (ids2, subst', mb_x') = renameIdBinder ids1 subst x
           (ids3, w) = freshCoId ids2 "w" (fromType (G.termType e))
           f = Function (maybeToList mb_x') [w] (fromTerm ids3 (subst', e) (Unknown w))
    G.Data dc _ _ xs
      | Just _ <- G.isUnboxedTupleTyCon_maybe (G.dataConTyCon dc)
      -> returnToKont u ids0 (mapMaybe (rename subst) xs)
      | otherwise
      -> addFunction y f (returnToKont u ids1 [IdOcc y])
      where dcs = G.dataConFamily dc
            ListPoint tys_lefts _tys_here tys_rights = fmap (concatMap fromTypeThunky . G.dataConFields) $ locateListPoint (==dc) dcs
            f = Box tys_lefts (mapMaybe (rename subst) xs) tys_rights
            (ids1, y) = freshId ids0 "data" PtrTy
    G.Literal l -> returnToKont u ids0 [Literal l]
fromTerm ids (subst, G.App e x) u = fromTerm ids (subst, e) $ Known (fromType (G.termType e)) $ \ids [t] -> bindKont u ids $ \_ u -> Term [] [] (Call t (Enter (maybeToList (rename subst x))) [u])
fromTerm ids (subst, G.TyApp e _) u = fromTerm ids (subst, e) u
fromTerm ids (subst, G.PrimOp pop es) u = foldr (\e known ids ts -> fromTerm ids (subst, e) $ Known (fromType (G.termType e)) $ \ids extra_ts -> known ids (ts ++ extra_ts))
                                                (\ids ts -> bindKont u ids $ \_ u -> Term [] [] (Call (PrimOp pop) (Enter ts) [u])) es ids []
fromTerm ids0 (subst, G.Case e _ x alts) u
  | [(G.DataAlt dc _ xs, e_alt)] <- alts
  , Just _ <- G.isUnboxedTupleTyCon_maybe (G.dataConTyCon dc)
  , let combine []     [] = []
        combine (x:xs) ts = case fromTypeThunky (G.idType x) of
          []                 -> (x, Nothing) : combine xs ts
          [_] | (t:ts) <- ts -> (x, Just t)  : combine xs ts
          _ -> error "combine: binder, but no matching trivials"
        combine [] (_:_) = error "combine: not enough trivials"
  = fromTerm ids0 (subst, e) $ Known (fromType (G.idType x)) $ \ids0 ts -> fromTerm ids0 (foldr (uncurry insertUniqueMap) subst (combine xs ts), e_alt) u
    
  | otherwise
  = fromTerm ids0 (subst, e) $ Known (fromType (G.idType x)) $ \ids0 ts -> let subst' = insertUniqueMap x (if G.typeKind (G.idType x) /= G.LiftedTypeKind then listToMaybe ts else Just (case ts of [t] -> t)) subst in case alts of
      [(G.DefaultAlt, e)]                                             -> fromTerm ids0 (subst', e) u
      ((G.DefaultAlt, e_def):(G.DataAlt dc _ xs, e):alts) | [t] <- ts -> fromAlts (selectData t)    ids0 subst' (Just e_def) ((dc, (xs, e)):[(dc, (xs, e)) | (G.DataAlt dc _ xs, e) <- alts]) u
      ((G.DataAlt dc _ xs, e):alts)                       | [t] <- ts -> fromAlts (selectData t)    ids0 subst' Nothing      ((dc, (xs, e)):[(dc, (xs, e)) | (G.DataAlt dc _ xs, e) <- alts]) u
      ((G.DefaultAlt, e_def):(G.LiteralAlt l, e):alts)    | [t] <- ts -> fromAlts (selectLiteral t) ids0 subst' (Just e_def) ((l, ([], e)):[(l, ([], e)) | (G.LiteralAlt l, e) <- alts]) u
      ((G.LiteralAlt l, e):alts)                          | [t] <- ts -> fromAlts (selectLiteral t) ids0 subst' Nothing      ((l, ([], e)):[(l, ([], e)) | (G.LiteralAlt l, e) <- alts]) u
fromTerm ids0 (subst0, G.LetRec xes e) u = e'
  where (ids3, subst2, e') = foldr (\(x, e) (ids1, subst0, e') -> let (ids2, subst1, Just x') = renameIdBinder ids1 subst0 x
                                                                      ty = fromLiftedType (G.termType e)
                                                                      (ids3, w) = freshCoId ids2 "w" [ty]
                                                                  in (ids2, subst1, addFunction x' (Function [] [w] (fromTerm ids3 (subst2, e) (Known [ty] $ \_ [t] -> Term [] [] (Call (Update [] (coIdType w) []) (Enter [IdOcc x', t]) [w])))) e'))
                                   (ids0, subst0, fromTerm ids3 (subst2, e) u) xes
fromTerm ids (subst, G.Cast e _) u = fromTerm ids (subst, e) u
 -- FIXME: I'm a bit worried about the type-precision consequences of this -- dropping casts may kill typeability of the output!
 --
 -- Consider:
 --  \(y :: Int) -> let x :: F Int = (\(x :: Int) -> x) |> (co :: (Int -> Int) ~ F Int)
 --                 in x |> (sym co) y
 --
 -- Which would naively translate to:
 --  let x :: * = \(x :: *) -> x
 --  in x y
 --
 -- Which is ill typed.
 --
 -- How about in CPS-core? (NB: I'm using * to stand for the evaluated form of the lifted type Int)
 --  let x :: <> -> * = \<> (k :: *) -> let xv :: (<> -> *) -> * = \x k -> x <> k
 --                                     in k xv
 --      l :: (<> -> *) -> * = \(xv :: (<> -> *) -> *) -> xv y halt
 --  in x l
 --
 -- This is STILL ill typed -- look at the (x l) application, where l demands more than the x can supply.
 --
 -- Even worse, since x is hidden by a lambda:
 --  \(y :: Int) -> let x :: F Int = (\(x :: Int) -> x) |> (co :: (Int -> Int) ~ F Int)
 --                 in (\(x :: F Int) -> x |> (sym co) y) x
 --
 -- One other thing we have to be careful about is recursive types:
 --  f :: Rec = (\(x :: Int) -> f) |> (nt_ax :: (Int -> Rec) ~ Rec)
 --
 -- Translating to:
 --  f :: * = (\(x :: *) -> f) :: * -> *
 --
 -- From this, it is clear that we could -- but *should not* -- update let-binder types from the type of
 -- their RHSs, since we can iterate this forever and build infinite arbitrarily large types.

selectData :: Trivial -> CoId -> [(G.DataCon, CoId)] -> Term
selectData t u_def dcs_us = Term [] [] (Call t Unbox [lookup dc dcs_us `orElse` u_def | dc <- dc_family])
  where dc_family = G.dataConFamily (fst (head dcs_us))

selectLiteral :: Trivial -> CoId -> [(Literal, CoId)] -> Term
selectLiteral t = error "FIXME: selectLiteral (perhaps via a primitive Id we can call)" t

typeFromVar :: G.Var -> [Type]
typeFromVar (G.AnId x)   = fromTypeThunky (G.idType x)
typeFromVar (G.ATyVar _) = []

fromVar :: G.Var -> [Id]
fromVar (G.AnId x)   = fromId x
fromVar (G.ATyVar _) = []

fromAlts :: (CoId -> [(a, CoId)] -> Term)
         -> Context -> Subst -> Maybe G.Term -> [(a, ([G.Id], G.Term))] -> Kont -> Term
fromAlts select ids0 subst mb_def selectors_alts u = bindKont u ids0 fromAlts'
  where 
    fromAlts' ids0 u = e2
      where
        e0 = select (mb_def_u `orElse` error "FIXME: add an unreachable fallback") selector_us
        ((ids1, mb_def_u), e1) = case mb_def of
            Nothing -> ((ids0, Nothing), e0)
            Just e  -> ((ids1, Just w), addContinuation w (Continuation [] (fromTerm ids2 (subst, e) (Unknown u))) e0)
              where (ids1, w) = freshCoId ids0 "w" []
        ((ids2, e2), selector_us) = mapAccumL (\(ids1, e1) (selector, (xs, e)) -> let k = Continuation (catMaybes mb_ys) (fromTerm ids2 (subst', e) (Unknown u))
                                                                                      (ids2a, w)  = freshCoId ids1 "w" (continuationCoType k)
                                                                                      (ids2b, subst', mb_ys) = renameBinders renameIdBinder ids2a subst xs
                                                                                  in ((ids2b, addContinuation w k e1), (selector, w)))
                                              (ids1, e1) selectors_alts
