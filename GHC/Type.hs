module GHC.Type where

import Name
import Utilities


data Kind = ArgTypeKind | OpenTypeKind | LiftedTypeKind | UnliftedTypeKind | UnboxedTupleTypeKind
          | ArrowKind Kind Kind
          deriving (Eq, Show)

arrowResKind :: Kind -> Kind
arrowResKind (ArrowKind _ k2) = k2
arrowResKind _ = error "arrowResKind"

isSubKind :: Kind -> Kind -> Bool
-- Otherwise-incomparable arrow elements:
isSubKind (ArrowKind k1a k2a)  (ArrowKind k1b k2b)  = k1b `isSubKind` k1a && k2a `isSubKind` k2b
isSubKind (ArrowKind _ _)      _                    = False
isSubKind _                    (ArrowKind _ _)      = False
-- The top element:
isSubKind _                    OpenTypeKind         = True
isSubKind OpenTypeKind         _                    = False
-- Various bottom elements:
isSubKind LiftedTypeKind       LiftedTypeKind       = True
isSubKind _                    LiftedTypeKind       = False
isSubKind UnliftedTypeKind     UnliftedTypeKind     = True
isSubKind _                    UnliftedTypeKind     = False
isSubKind UnboxedTupleTypeKind UnboxedTupleTypeKind = True
isSubKind _                    UnboxedTupleTypeKind = False
-- The intermediate element:
isSubKind _                    ArgTypeKind          = True


data TyCon = TyCon {
    tyConName :: String,
    tyConKind :: Kind
  } deriving (Show)

instance Eq TyCon where
    (==) = (==) `on` tyConName

instance Ord TyCon where
    compare = compare `on` tyConName

instance Pretty TyCon where
    pPrint = text . tyConName

funTyCon :: TyCon
funTyCon = TyCon {
    tyConName = "(->)",
    tyConKind = ArgTypeKind `ArrowKind` OpenTypeKind
  }

pairTyCon :: TyCon
pairTyCon = TyCon {
    tyConName = "(,)",
    tyConKind = LiftedTypeKind `ArrowKind` LiftedTypeKind `ArrowKind` LiftedTypeKind
  }

unboxedPairTyCon :: TyCon
unboxedPairTyCon = TyCon {
    tyConName = "(#,#)",
    tyConKind = ArgTypeKind `ArrowKind` ArgTypeKind `ArrowKind` UnboxedTupleTypeKind
  }

intHashTyCon :: TyCon
intHashTyCon = TyCon {
    tyConName = "Int#",
    tyConKind = UnliftedTypeKind
  }

eqHashTyCon :: Kind -> TyCon
eqHashTyCon k = TyCon {
    tyConName = "~#",
    tyConKind = k `ArrowKind` k `ArrowKind` UnliftedTypeKind
  }

intTyCon :: TyCon
intTyCon = TyCon {
    tyConName = "Int",
    tyConKind = LiftedTypeKind
  }

boolTyCon :: TyCon
boolTyCon = TyCon {
    tyConName = "Bool",
    tyConKind = LiftedTypeKind
  }


data TyVar = TyVar {
    tyVarName :: Name,
    tyVarKind :: Kind
  } deriving (Show)

instance Eq TyVar where
    (==) = (==) `on` tyVarName

instance Ord TyVar where
    compare = compare `on` tyVarName

instance Pretty TyVar where
    pPrintPrec level prec = pPrintPrec level prec . tyVarName


shadowyTyVars :: [(String, Kind)] -> ([TyVar], [Type])
shadowyTyVars xkinds = (tvs, map TyVarTy tvs)
  where (xs, kinds) = unzip xkinds
        ns = shadowyNames xs
        tvs = zipWith TyVar ns kinds


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


typeKind :: Type -> Kind
typeKind (TyVarTy a)     = tyVarKind a
typeKind (TyConTy tc)    = tyConKind tc
typeKind (AppTy ty1 _)   = arrowResKind (typeKind ty1)
typeKind (ForAllTy _ ty) = typeKind ty
