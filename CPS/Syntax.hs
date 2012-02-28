module CPS.Syntax where

import GHC.Kind
import GHC.Primitives

import Name


data PrimTyCon = IntHashTy

type IsEvaluated = Bool

data TypeBinder = TyVarBinder TyVar
                | ValueBinder Type

data Type = TyVarTy TyVar
          | TyConTy TyCon
          | AppTy Type Type
          | ForAllTy TyVar Type
          | FunTy [TypeBinder] IsEvaluated [[TypeBinder]]


data CoId = CoId {
    coIdName :: Name,
    coIdType :: [TypeBinder]
  }

data Id = Id {
    idName :: Name,
    idType :: Type
  }


data Var = AnId Id | ATyVar TyVar


type IsPun = Bool

data Trivial = Type Type
             | Literal Literal
             | Coercion Coercion
             | Var Id IsPun  -- If it is a pun, type cast from (<> -!> a) to (<> -> <> -!> a). NB: by the type system, puns can only be one level deep.

data CoId' = CoId' CoId
           | Halt

data Id' = Id' Id
         | PrimOp PrimOp
         | Update [Type] -- Update frame for thunk which evaluates to (<> -!> a). The type list is the particular a we have in mind, for type reconstruction.

data Function = Function [Var] [CoId] Term

data Continuation = Continuation [Var] Term

data Term = Term [(Id, Function)] [(CoId, Continuation)] Transfer

data Transfer = Return (Coercion, CoId') [Trivial]
              | Call (Coercion, Id') [Trivial] [CoId]
