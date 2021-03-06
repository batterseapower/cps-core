{-# LANGUAGE PatternGuards #-}
module GHC.Kind where

import Name
import Utilities


infixr 7 `ArrowKind`

data Kind = ArgTypeKind | OpenTypeKind | LiftedTypeKind | UnliftedTypeKind | UnboxedTupleTypeKind
          | ArrowKind Kind Kind
          deriving (Eq, Show)

mkArrowKinds :: [Kind] -> Kind -> Kind
mkArrowKinds ks k = foldr ArrowKind k ks

splitArrowKinds :: Kind -> ([Kind], Kind)
splitArrowKinds (ArrowKind k1 k2) = first (k1:) $ splitArrowKinds k2
splitArrowKinds k                 = ([], k)

arrowResKind :: Kind -> Kind
arrowResKind (ArrowKind _ k2) = k2
arrowResKind k = error $ "arrowResKind: " ++ show k

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
    tyConKind = ArgTypeKind `ArrowKind` OpenTypeKind `ArrowKind` LiftedTypeKind
  }

pairTyCon :: TyCon
pairTyCon = TyCon {
    tyConName = "(,)",
    tyConKind = LiftedTypeKind `ArrowKind` LiftedTypeKind `ArrowKind` LiftedTypeKind
  }

unboxedTupleTyCon :: Int -> TyCon
unboxedTupleTyCon n = TyCon {
    tyConName = "(#" ++ replicate (n - 1) ',' ++ "#)",
    tyConKind = replicate n ArgTypeKind `mkArrowKinds` UnboxedTupleTypeKind
  }

isUnboxedTupleTyCon_maybe :: TyCon -> Maybe Int
isUnboxedTupleTyCon_maybe tc
  | k == UnboxedTupleTypeKind = Just (length ks)
  | otherwise                 = Nothing
  where (ks, k) = splitArrowKinds (tyConKind tc)

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

isEqHashTyCon :: TyCon -> Maybe Kind
isEqHashTyCon tc
  | tyConName tc == "~#"
  , k `ArrowKind` _ `ArrowKind` UnliftedTypeKind <- tyConKind tc
  = Just k
  | otherwise
  = Nothing

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

instance Uniqueable TyVar where
    getUnique = getUnique . tyVarName

instance Pretty TyVar where
    pPrintPrec level prec = pPrintPrec level prec . tyVarName


shadowyTyVars :: [(String, Kind)] -> [TyVar]
shadowyTyVars xkinds = zipWith TyVar ns kinds
  where (xs, kinds) = unzip xkinds
        ns = shadowyNames xs
