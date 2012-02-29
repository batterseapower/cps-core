module Main where

import CPS.Syntax2
import CPS.FromGHC

import GHC.Var as G
import GHC.Kind as G
import GHC.Type as G
import GHC.Syntax as G
import GHC.Primitives

import Name
import UniqueSupply


example :: G.Term
example = G.Case (G.Value (G.Literal (Int 2))) intHashTy two [(G.DefaultAlt,
                G.LetRec [(id,  G.Value (G.Lambda (G.ATyVar a) (G.Value (G.Lambda (G.AnId x) (G.Var x))))),
                          (prim_id', G.Value (G.Lambda (G.AnId y) (G.Var y))),
                          (prim_id, G.Var id `G.App` prim_id')] $
                         G.PrimOp Add [G.Value (G.Literal (Int 1)), G.Var prim_id `G.App` two])]
  where [a_n, id_n, prim_id_n, prim_id_n', x_n, y_n, two_n] = shadowyNames ["a", "id", "prim_id", "prim_id'", "x", "y", "two"]
        a = G.TyVar { G.tyVarName = a_n, G.tyVarKind = G.LiftedTypeKind }
        id = G.Id { G.idName = id_n, G.idType = G.ForAllTy a (G.TyVarTy a `G.mkFunTy` G.TyVarTy a) }
        prim_id = G.Id { G.idName = prim_id_n, G.idType = intHashTy `G.mkFunTy` intHashTy }
        prim_id' = G.Id { G.idName = prim_id_n', G.idType = intHashTy `G.mkFunTy` intHashTy }
        x = G.Id { G.idName = x_n, G.idType = G.TyVarTy a }
        y = G.Id { G.idName = y_n, G.idType = intHashTy }
        two = G.Id { G.idName = two_n, G.idType = intHashTy }


main :: IO ()
main = do
    ids <- initUniqueSupply 'x'
    let (ids', halt_n) = freshName ids "halt"
    print $ fromTerm (ids', emptyInScopeSet) (emptyUniqueMap, example) (Unknown (CoId { coIdName = halt_n, coIdType = [IntHashTy] }))
