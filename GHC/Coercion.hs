module GHC.Coercion where

import GHC.Kind
import GHC.Var
import GHC.Type

import Utilities


data Coercion = CoVarCo CoVarId
              | ReflCo Type
              | AppCo Coercion Coercion
              | SymCo Coercion
              | TransCo Coercion Coercion
              | NthCo Int Coercion
              | ForAllCo TyVar Coercion
              | InstCo Coercion Type
              | UnsafeCo Type Type -- Also used for instantiated axioms
              deriving (Eq, Show)

instance Pretty Coercion where
    pPrint _ = text "co" -- FIXME


mkCoercionType :: Type -> Type -> Type
mkCoercionType ty1 ty2 = mkTyConAppTy (eqHashTyCon (typeKind ty1)) [ty1, ty2]

splitCoercionType :: Type -> (Type, Type)
splitCoercionType ty = case splitTyConAppTy_maybe ty of
    Just (tc, [ty1, ty2]) | tc == eqHashTyCon (typeKind ty1) -> (ty1, ty2)
    _ -> error "splitCoercionType"


coVarIdType' :: CoVarId -> (Type, Type)
coVarIdType' = splitCoercionType . idType

coercionType :: Coercion -> Type
coercionType = uncurry mkCoercionType . coercionType'

coercionType' :: Coercion -> (Type, Type)
coercionType' (CoVarCo x)     = coVarIdType' x
coercionType' (ReflCo ty)     = (ty, ty)
coercionType' (AppCo co1 co2) = (ty1a `AppTy` ty2a, ty1b `AppTy` ty2b)
  where (ty1a, ty1b) = coercionType' co1
        (ty2a, ty2b) = coercionType' co2
coercionType' (SymCo co) = (ty2, ty1)
  where (ty1, ty2) = coercionType' co
coercionType' (TransCo co1 co2) = (ty1a, ty2b)
  where (ty1a, _ty1b) = coercionType' co1
        (_ty2a, ty2b) = coercionType' co2
coercionType' (NthCo n co) = (f ty1, f ty2)
  where (ty1, ty2) = coercionType' co
        f ty = case splitTyConAppTy_maybe ty of
            Just (_, tys) | n < length tys -> tys !! n
            _ -> error "coercionType': NthCo"
coercionType' (ForAllCo a co) = (ForAllTy a ty1, ForAllTy a ty2)
  where (ty1, ty2) = coercionType' co
coercionType' (InstCo co ty) = (instTy ty1 ty, instTy ty2 ty)
  where (ty1, ty2) = coercionType' co
coercionType' (UnsafeCo ty1 ty2) = (ty1, ty2)
