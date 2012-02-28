module GHC.Data where

import GHC.Kind
import GHC.Type
import GHC.Var

import Utilities


typefulId :: Type -> Id
typefulId = Id (error "typefulId: not meant to be used in a context where the Id name matters") -- FIXME?


type Arity = Int
data DataCon = DataCon {
    dataConName      :: String,
    dataConBinders   :: [Var], -- Mixture of TyVar and Id binders (including coercions for GADTs)..
    dataConTyCon     :: TyCon, -- ..scoping over this..
    dataConTyConArgs :: [Type] -- ..applied to these
  } deriving (Show)

instance Eq DataCon where
    (==) = (==) `on` dataConName

instance Ord DataCon where
    compare = compare `on` dataConName

instance Pretty DataCon where
    pPrint = text . dataConName

dataConType :: DataCon -> Type
dataConType dc = mkPiTys (dataConBinders dc) (mkTyConAppTy (dataConTyCon dc) (dataConTyConArgs dc))


pairDataCon :: DataCon
pairDataCon = DataCon {
    dataConName      = "(,)",
    dataConBinders   = [ATyVar a_tv, ATyVar b_tv, AnId (typefulId a_ty), AnId (typefulId b_ty)],
    dataConTyCon     = pairTyCon,
    dataConTyConArgs = [a_ty, b_ty]
  } where ([a_tv, b_tv], [a_ty, b_ty]) = shadowyTyVarsTypes [("a", LiftedTypeKind), ("b", LiftedTypeKind)]

unboxedTupleDataCon :: Int -> DataCon
unboxedTupleDataCon n = DataCon {
    dataConName      = "(#" ++ replicate (n - 1) ',' ++ "#)",
    dataConBinders   = map ATyVar tvs ++ map (AnId . typefulId) tys,
    dataConTyCon     = unboxedTupleTyCon n,
    dataConTyConArgs = tys
  } where (tvs, tys) = shadowyTyVarsTypes [("a" ++ show n, OpenTypeKind) | n <- [1..n]]

iHashDataCon :: DataCon
iHashDataCon = DataCon {
    dataConName      = "I#",
    dataConBinders   = [AnId (typefulId intHashTy)],
    dataConTyCon     = intTyCon,
    dataConTyConArgs = []
  }

trueDataCon, falseDataCon :: DataCon
trueDataCon = DataCon {
    dataConName      = "True",
    dataConBinders   = [],
    dataConTyCon     = boolTyCon,
    dataConTyConArgs = []
  }
falseDataCon = DataCon {
    dataConName      = "False",
    dataConBinders   = [],
    dataConTyCon     = boolTyCon,
    dataConTyConArgs = []
  }
