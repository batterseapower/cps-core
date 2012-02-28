{-# LANGUAGE PatternGuards #-}
module CPS.Syntax where

import GHC.Coercion
import GHC.Kind
import GHC.Type
import GHC.Var
import GHC.Primitives

import Name

import Control.Monad (guard)


type IsEvaluated = Bool

data TypeBinder = TyVarBinder TyVar
                | ValueBinder Type

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
