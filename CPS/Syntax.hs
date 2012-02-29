{-# LANGUAGE PatternGuards #-}
module CPS.Syntax where

import GHC.Coercion
import GHC.Kind
import GHC.Type
import GHC.Var
import GHC.Primitives
import qualified GHC.Syntax as S

import Name

import Control.Monad (guard)


type IsEvaluated = Bool

data TypeBinder = TyVarBinder TyVar
                | ValueBinder Type

-- Rube Goldberg type encoding machinery. This encoding carefully:
--  1. Preserves the binding structure of the original type
--  2. Creates a type which is valid according to the kinding rules
--
-- Note that it only works properly if there are no unboxed tuples in the
-- ValueBinders, which should be true in the output of the desugaring.
--
-- Note further that it is NOT a goal that uses of original type constructors
-- which originate from the input program (like (ty1 -> ty2) and Bool) get
-- split into appropriate (unthunked) CPS types. Instead, the relationship
-- between "old" types and "new" types is mediated by newtype coercions.
--
-- TODO: possible alternative is to use the on-demand normalisation stuff,
-- and have a cpsView_maybe or similar. Of course, with this approach unification
-- will never work, but do we really care? If we take this approach, we have
-- to be careful that the CPS (->) is easily distinguished from the original (->)

mkCPSFunTy :: [TypeBinder] -> IsEvaluated -> [[TypeBinder]] -> Type
mkCPSFunTy arg_binds is_evaluated kont_bindss
  = mk_binders arg_binds (mkEncodedTupleTy (mkEncodedBoolTy is_evaluated : map (\kont_binds -> mk_binders kont_binds intHashTy) kont_bindss))
  where mk_binders binds ty = foldr (\bind -> case bind of TyVarBinder a -> ForAllTy a; ValueBinder ty1 -> (ty1 `mkFunTy`)) ty binds

splitCPSFunTy_maybe :: Type -> Maybe ([TypeBinder], IsEvaluated, [[TypeBinder]])
splitCPSFunTy_maybe = collect_left []
  where
    collect_left args ty
      | Just tys <- splitEncodedTupleTy_maybe ty
      = do { (evaluated_ty:tys) <- return tys
           ; evaluated <- splitEncodedBoolTy_maybe evaluated_ty
           ; fmap ((,,) (reverse args) evaluated) $ mapM (collect_right []) tys }
      | ForAllTy a ty <- ty
      = collect_left (TyVarBinder a:args) ty
      | Just (ty1, ty2) <- splitFunTy_maybe ty
      = collect_left (ValueBinder ty1:args) ty2
      | otherwise
      = Nothing

    collect_right args ty
      | ty == intHashTy
      = Just (reverse args)
      | ForAllTy a ty <- ty
      = collect_right (TyVarBinder a:args) ty
      | Just (ty1, ty2) <- splitFunTy_maybe ty
      = collect_right (ValueBinder ty1:args) ty2
      | otherwise
      = Nothing

-- NB: there is no nullary unboxed tuple type, so we have to pad at the front
-- NB: none of the components of the tuple may themselves be unboxed tuples, so we have to add a leading arrow
mkEncodedTupleTy :: [Type] -> Type
mkEncodedTupleTy tys = mkTyConAppTy (unboxedTupleTyCon (1 + length tys)) (intHashTy:map (intHashTy `mkFunTy`) tys)

splitEncodedTupleTy_maybe :: Type -> Maybe [Type]
splitEncodedTupleTy_maybe ty
  | Just (tc, tys2) <- splitTyConAppTy_maybe ty
  , Just n <- isUnboxedTupleTyCon_maybe tc
  , length tys2 == n
  , (ty2:tys2) <- tys2
  , ty2 == intHashTy
  , Just tys2 <- mapM (\ty2 -> splitFunTy_maybe ty2 >>= \(ty2a, ty2b) -> guard (ty2a == intHashTy) >> return ty2b) tys2
  = Just tys2
  | otherwise
  = Nothing

mkEncodedBoolTy :: Bool -> Type
mkEncodedBoolTy b = if b then boolTy else intHashTy

splitEncodedBoolTy_maybe :: Type -> Maybe Bool
splitEncodedBoolTy_maybe ty
  | ty == boolTy    = Just True
  | ty == intHashTy = Just False
  | otherwise       = Nothing


data CoId = CoId {
    coIdName :: Name,
    coIdType :: [TypeBinder]
  }


type IsPun = Bool

data Trivial = Type Type
             | Literal Literal
             | Coercion Coercion
             | Var Id IsPun  -- If it is a pun, type cast from (<> -!> a) to (<> -> <> -!> a). NB: by the type system, puns can only be one level deep.

-- NB: all codes, even those than can only be generated inline (i.e. primops)
data Id' = Id' Id
         | PrimOp PrimOp
         | Update [Type] -- Update frame for thunk which evaluates to (<> -!> a). The type list is the particular a we have in mind, for type reconstruction.

data Function = Function [Var] [CoId] Term

data Continuation = Continuation [Var] Term

data Term = Term [(Id, Function)] [(CoId, Continuation)] Transfer

type Cast a = (Coercion, a)

data Transfer = Return (Cast CoId) [Trivial]
              | Call (Cast Id') [Trivial] [CoId]


newtype InScopeSet = ISS { unISS :: S.Set Unique }

uniqAwayName :: InScopeSet -> Name -> (InScopeSet, Name)
uniqAwayName (ISS iss) n = (ISS (S.insert u'), n { nameUnique = u' })
  where
    u' = go (nameUnique n)
    go u | u `S.member` iss = go (u + 1)
         | otherwise        = u

uniqAwayId :: InScopeSet -> Id -> (InScopeSet, Id)
uniqAwayId iss x = (iss', x { idName = n' })
  where (iss', n') = uniqAwayName iss (idName x)

uniqAwayTyVar :: InScopeSet -> TyVar -> (InScopeSet, TyVar)
uniqAwayTyVar iss a = (iss', x { tyVarName = a' })
  where (iss', n') = uniqAwayName iss (tyVarName a)


type In a = (Renaming, a)

data Renaming = Renaming {
    tyVarRenaming :: M.Map Unique Type,
    idRenaming    :: M.Map Unique Trivial,
    coIdRenaming  :: M.Map Unique CoId
  }

renameTyVar :: Renaming -> TyVar -> Type
renameTyVar rn a = M.findWithDefault (error "renameTyVar") (tyVarRenaming rn) (tyVarUnique (tyVarName a))

renameId :: Renaming -> Id -> Trivial
renameId rn x = M.findWithDefault (error "renameVar") (idRenaming rn) (nameUnique (idName x))


class Renameable a where
    rename :: InScopeSet -> Renaming -> a -> a

instance Renameable Type where
    rename ids rn ty = case ty of
        ?? -- FIXME

instance Renameable TyVar where
    rename _ _ a = a

instance Renameable CoId where
    rename ids rn q = q { coIdType = map (rename ids rn) (coIdType q) }

instance Renameable Id where
    rename ids rn x = x { idType = rename ids rn (idType x) }


renameTyVarBinder :: InScopeSet -> Renaming -> TyVar -> (InScopeSet, RenammkCPSing, TyVar)
renameTyVarBinder iss rn a = (iss', rn { tyVarRenaming = M.insert (nameUnique (tyVarName a)) (TyVarTy a') (tyVarRenaming rn) })
  where (iss', a') = uniqAwayTyVar iss (rename iss rn a)

renameIdBinder :: InScopeSet -> Renaming -> Id -> (InScopeSet, Renaming, Id)
renameIdBinder iss rn x = (iss', rn { idRenaming = M.insert (nameUnique (idName x)) (Var x' False) (idRenaming rn) })
  where (iss', x') = uniqAwayId iss (rename iss rn x)

renameCoVarBinder :: InScopeSet -> Renaming -> CoId -> (InScopeSet, Renaming, CoId)
renameCoIdBinder iss rn q = (iss', rn { coIdRenaming = M.insert (nameUnique (coIdName q)) q' (coIdRenaming rn) })
  where (iss', q') = uniqAwayCoId iss (rename iss rn q)


return_ :: Cast CoId' -> [Cast Trivial] -> Transfer

call :: Cast Id' -> [Cast Trivial] -> [Cast CoId] -> Transfer

uncast :: Id' -> Cast Id'
uncast = undefined -- FIXME

fromCore :: InScopeSet -> In S.Term -> CoId -> Term
fromCore iss (rn, S.Var x) q
    | isUnLiftedType (varType x) = Term [] [] (return_ (uncast q) [uncast t'])
    | otherwise                  = Term [] [] (call    (uncast (Id x False)) [] [uncast q])
  where t' = renameId rn x
fromCore iss0 (rn0, S.Value v) q = case v of
    Coercion co -> Term [] [] (return_ (uncast q) [uncast (Coercion (renameCoercion rn co))])
    Lambda x e -> Term [(y, Function [x'] [r] (fromCore iss''))] [] (return_ (uncast q) [uncast (Var y False)])
      where (iss1, _,   y)  = renameIdBinder iss0 rn0 (unfreshId "y" (mkCPS))
            (iss2, rn1, x') = renameIdBinder iss1 rn0 x
            (iss3, rn2, r)  = renameCoIdBinder iss2 rn1 (unfreshCoId "r" [idType x'])

