module GHC.Type where

import GHC.Kind

import Name
import Utilities

import qualified Data.Set as S


data Type = TyVarTy TyVar
          | TyConTy TyCon
          | AppTy Type Type
          | ForAllTy TyVar Type
          deriving (Eq, Show)

instance Pretty Type where
    pPrintPrec level prec ty = case ty of
      TyVarTy a     -> pPrintPrec level prec a
      TyConTy tc    -> pPrintPrec level prec tc
      AppTy ty1 ty2 -> pPrintPrecApp level prec ty1 ty2
      ForAllTy a ty -> text "forall" <+> pPrintPrec level noPrec a <> text "." <+> pPrintPrec level noPrec ty

mkAppTys :: Type -> [Type] -> Type
mkAppTys = foldl AppTy

mkTyConAppTy :: TyCon -> [Type] -> Type
mkTyConAppTy = mkAppTys . TyConTy

splitTyConAppTy_maybe :: Type -> Maybe (TyCon, [Type])
splitTyConAppTy_maybe = go []
  where go args (AppTy ty1 ty2) = go (ty2:args) ty1
        go args (TyConTy tc)    = Just (tc, args)
        go _    _               = Nothing

infixr 7 `mkFunTy`

mkFunTy :: Type -> Type -> Type
mkFunTy ty1 ty2 = mkTyConAppTy funTyCon [ty1, ty2]

mkFunTys :: [Type] -> Type -> Type
mkFunTys tys ty = foldr mkFunTy ty tys

mkForAllTys :: [TyVar] -> Type -> Type
mkForAllTys tvs ty = foldr ForAllTy ty tvs

splitFunTy_maybe :: Type -> Maybe (Type, Type)
splitFunTy_maybe ty = case splitTyConAppTy_maybe ty of
    Just (tc, [ty1, ty2]) | tc == funTyCon -> Just (ty1, ty2)
    _                                      -> Nothing

funResTy :: Type -> Type
funResTy ty = case splitFunTy_maybe ty of
    Just (_, ty2) -> ty2
    _             -> error $ "funResTy: " ++ show ty

instTy :: Type -> Type -> Type
instTy (ForAllTy a ty_body) ty_a = renameType (mkInScopeSet (typeFreeVars ty_a)) (mkTypeSubst a ty_a) ty_body
instTy _ _ = error "mkInstTy"


newtype TypeSubst = TypeSubst { unTypeSubst :: UniqueMap Type }

mkTypeSubst :: TyVar -> Type -> TypeSubst
mkTypeSubst a ty = TypeSubst (insertUniqueMap a ty emptyUniqueMap)

renameTyVar :: TypeSubst -> TyVar -> Type
renameTyVar subst a = findUniqueWithDefault (error "renameTyVar: out of scope") a (unTypeSubst subst)

renameTypeBinder :: InScopeSet -> TypeSubst -> TyVar -> (InScopeSet, TypeSubst, TyVar)
renameTypeBinder iss subst a = (iss', TypeSubst (insertUniqueMap a (TyVarTy a') (unTypeSubst subst)), a')
  where n = tyVarName a
        (iss', n') = uniqAwayName iss n
        a' = a { tyVarName = n' } -- NB: don't need to rename types


typeFreeVars :: Type -> S.Set TyVar
typeFreeVars ty = case ty of
    TyVarTy a     -> S.singleton a
    TyConTy _     -> S.empty
    AppTy ty1 ty2 -> typeFreeVars ty1 `S.union` typeFreeVars ty2
    ForAllTy a ty -> S.delete a (typeFreeVars ty)


renameType :: InScopeSet -> TypeSubst -> Type -> Type
renameType iss subst ty = case ty of
    TyVarTy a     -> renameTyVar subst a
    TyConTy tc    -> TyConTy tc
    AppTy ty1 ty2 -> AppTy (renameType iss subst ty1) (renameType iss subst ty2)
    ForAllTy a ty -> ForAllTy a' (renameType iss' subst' ty)
      where (iss', subst', a') = renameTypeBinder iss subst a


intTy :: Type
intTy = TyConTy intTyCon

intHashTy :: Type
intHashTy = TyConTy intHashTyCon

boolTy :: Type 
boolTy = TyConTy boolTyCon


shadowyTyVarsTypes :: [(String, Kind)] -> ([TyVar], [Type])
shadowyTyVarsTypes xkinds = (tvs, map TyVarTy tvs)
  where tvs = shadowyTyVars xkinds


typeKind :: Type -> Kind
typeKind (TyVarTy a)     = tyVarKind a
typeKind (TyConTy tc)    = tyConKind tc
typeKind (AppTy ty1 _)   = arrowResKind (typeKind ty1)
typeKind (ForAllTy _ ty) = typeKind ty
