module GHC.Var where

import GHC.Kind
import GHC.Type

import Name
import Utilities


data Id = Id {
    idName :: Name,
    idType :: Type
  } deriving (Show)

instance Eq Id where
    (==) = (==) `on` idName

instance Ord Id where
    compare = compare `on` idName

instance Pretty Id where
    pPrintPrec level prec = pPrintPrec level prec . idName


type CoVarId = Id

data Var = AnId !Id | ATyVar !TyVar
         deriving (Eq, Ord, Show)

instance Pretty Var where
    pPrintPrec level prec (AnId x)   = pPrintPrec level prec x
    pPrintPrec level prec (ATyVar a) = pPrintPrec level prec a


mkPiTy :: Var -> Type -> Type
mkPiTy (AnId x)   = (idType x `mkFunTy`)
mkPiTy (ATyVar a) = (a `ForAllTy`)

mkPiTys :: [Var] -> Type -> Type
mkPiTys xs ty = foldr mkPiTy ty xs
