module GHC.Type where

import GHC.Kind

import Utilities


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

mkFunTy :: Type -> Type -> Type
mkFunTy ty1 ty2 = mkTyConAppTy funTyCon [ty1, ty2]

splitFunTy_maybe :: Type -> Maybe (Type, Type)
splitFunTy_maybe ty = case splitTyConAppTy_maybe ty of
    Just (tc, [ty1, ty2]) | tc == funTyCon -> Just (ty1, ty2)
    _                                      -> Nothing

funResTy :: Type -> Type
funResTy ty = case splitFunTy_maybe ty of
    Just (_, ty2) -> ty2
    _             -> error "funResTy"

instTy :: Type -> Type -> Type
instTy (ForAllTy a ty_body) ty_a = undefined -- FIXME: need renamings before I can do this
instTy _ _ = error "mkInstTy"


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
