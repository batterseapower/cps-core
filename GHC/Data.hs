module GHC.Data where

import GHC.Kind
import GHC.Type

import Utilities


type Arity = Int
data DataCon = DataCon {
    dataConName       :: String,
    dataConUnivTyVars :: [TyVar],  -- Binders both universal..
    dataConExTyVars   :: [TyVar],  -- ..and existential..
    dataConFields     :: [Type],   -- ..scoping over these (including coercions for GADTs)..
    dataConTyCon      :: TyCon,    -- ..and this TyCon..
    dataConTyConArgs  :: [Type],   -- ..applied to these.
    dataConSiblings   :: [DataCon] -- Other DataCons belonging to this TyCon, excluding this one
  } deriving (Show)

instance Eq DataCon where
    (==) = (==) `on` dataConName

instance Ord DataCon where
    compare = compare `on` dataConName

instance Pretty DataCon where
    pPrint = text . dataConName

dataConType :: DataCon -> Type
dataConType dc = mkForAllTys (dataConUnivTyVars dc) (mkForAllTys (dataConExTyVars dc) (mkFunTys (dataConFields dc) (mkTyConAppTy (dataConTyCon dc) (dataConTyConArgs dc))))

-- All DataCons in the family, sorted into a consistent order suitable for e.g. deciding on a tagging
dataConFamily :: DataCon -> [DataCon]
dataConFamily dc = sortBy (compare `on` dataConName) (dc : dataConSiblings dc)


pairDataCon :: DataCon
pairDataCon = DataCon {
    dataConName       = "(,)",
    dataConUnivTyVars = [a_tv, b_tv],
    dataConExTyVars   = [],
    dataConFields     = [a_ty, b_ty],
    dataConTyCon      = pairTyCon,
    dataConTyConArgs  = [a_ty, b_ty],
    dataConSiblings   = []
  } where ([a_tv, b_tv], [a_ty, b_ty]) = shadowyTyVarsTypes [("a", LiftedTypeKind), ("b", LiftedTypeKind)]

unboxedTupleDataCon :: Int -> DataCon
unboxedTupleDataCon n = DataCon {
    dataConName       = "(#" ++ replicate (n - 1) ',' ++ "#)",
    dataConUnivTyVars = tvs,
    dataConExTyVars   = [],
    dataConFields     = tys,
    dataConTyCon      = unboxedTupleTyCon n,
    dataConTyConArgs  = tys,
    dataConSiblings   = []
  } where (tvs, tys) = shadowyTyVarsTypes [("a" ++ show n, OpenTypeKind) | n <- [1..n]]

iHashDataCon :: DataCon
iHashDataCon = DataCon {
    dataConName       = "I#",
    dataConUnivTyVars = [],
    dataConExTyVars   = [],
    dataConFields     = [intHashTy],
    dataConTyCon      = intTyCon,
    dataConTyConArgs  = [],
    dataConSiblings   = []
  }

trueDataCon, falseDataCon :: DataCon
trueDataCon = DataCon {
    dataConName       = "True",
    dataConUnivTyVars = [],
    dataConExTyVars   = [],
    dataConFields     = [],
    dataConTyCon      = boolTyCon,
    dataConTyConArgs  = [],
    dataConSiblings   = [falseDataCon]
  }
falseDataCon = DataCon {
    dataConName       = "False",
    dataConUnivTyVars = [],
    dataConExTyVars   = [],
    dataConFields     = [],
    dataConTyCon      = boolTyCon,
    dataConTyConArgs  = [],
    dataConSiblings   = [trueDataCon]
  }
