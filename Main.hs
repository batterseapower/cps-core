module Main where

import CPS.Syntax
import CPS.FromGHC

import GHC.Data as G
import GHC.Var as G
import GHC.Kind as G
import GHC.Type as G
import GHC.Syntax as G
import GHC.Primitives

import Name
import Utilities

import qualified Data.Set as S
import qualified Data.Map as M


functionExample :: G.Term
functionExample = G.Case (G.Value (G.Literal (Int 2))) intHashTy two [(G.DefaultAlt,
                    G.LetRec [(lifted_id,  G.Value (G.Lambda (G.ATyVar a) (G.Value (G.Lambda (G.AnId x) (G.Var x))))),
                              (prim_id', G.Value (G.Lambda (G.AnId y) (G.Var y))),
                              (prim_id, G.Var lifted_id `G.TyApp` G.idType prim_id' `G.App` prim_id')] $
                             G.PrimOp Add [G.PrimOp Add [G.Value (G.Literal (Int 1)), G.Var prim_id `G.App` two], G.Var prim_id `G.App` two])] -- Use prim_id twice to test thunk update works
  where
    [a_n, id_n, prim_id_n, prim_id_n', x_n, y_n, two_n] = shadowyNames ["a", "id", "prim_id", "prim_id'", "x", "y", "two"]
    a = G.TyVar { G.tyVarName = a_n, G.tyVarKind = G.LiftedTypeKind }
    lifted_id = G.Id { G.idName = id_n, G.idType = G.ForAllTy a (G.TyVarTy a `G.mkFunTy` G.TyVarTy a) }
    prim_id = G.Id { G.idName = prim_id_n, G.idType = intHashTy `G.mkFunTy` intHashTy }
    prim_id' = G.Id { G.idName = prim_id_n', G.idType = intHashTy `G.mkFunTy` intHashTy }
    x = G.Id { G.idName = x_n, G.idType = G.TyVarTy a }
    y = G.Id { G.idName = y_n, G.idType = intHashTy }
    two = G.Id { G.idName = two_n, G.idType = intHashTy }


dataExample :: G.Term
dataExample = G.Case (G.Value (G.Literal (Int 1))) intHashTy one [(G.DefaultAlt,
                G.Case (G.Value (G.Data G.trueDataCon [] [] [])) intHashTy true [
                  (G.DefaultAlt,                  G.Value (G.Literal (Int 1))),
                  (G.DataAlt G.trueDataCon [] [], G.LetRec [(unboxy_fun, G.Value (G.Lambda (G.AnId one) (G.Value (G.Data (G.unboxedTupleDataCon 2) [G.intHashTy, G.boolTy] [] [one, true]))))] $
                                                  G.Case (G.Var unboxy_fun `G.App` one) G.intHashTy unbx [
                                                                     (G.DataAlt (G.unboxedTupleDataCon 2) [] [x, y], G.Var x)])])]
  where
    [true_n, one_n, unbx_n, unboxy_fun_n, x_n, y_n] = shadowyNames ["true", "one", "unbx", "unboxy_fun", "x", "y"]
    true = G.Id { G.idName = true_n, G.idType = G.boolTy }
    one = G.Id { G.idName = one_n, G.idType = G.intHashTy }
    unbx = G.Id { G.idName = unbx_n, G.idType = G.mkTyConAppTy (G.unboxedTupleTyCon 2) [G.intHashTy, G.boolTy] }
    unboxy_fun = G.Id { G.idName = unboxy_fun_n, G.idType = G.mkFunTy G.intHashTy (G.idType unbx) }
    x = G.Id { G.idName = x_n, G.idType = G.intHashTy }
    y = G.Id { G.idName = y_n, G.idType = G.boolTy }

caseBoundFunctionExample :: G.Term
caseBoundFunctionExample = G.Case (G.Value (G.Lambda (G.ATyVar a) (G.Value (G.Lambda (G.AnId x) (G.Var x))))) intTy lifted_id [(G.DefaultAlt,
                             G.Case (G.Value (G.Literal (Int 1))) intTy one [(G.DefaultAlt,
                               G.LetRec [(boxed_one, G.Value (G.Data G.iHashDataCon [] [] [one]))] $
                               G.Var lifted_id `G.TyApp` intTy `G.App` boxed_one)])]
  where
    [a_n, one_n, boxed_one_n, lifted_id_n, x_n] = shadowyNames ["a", "one", "boxed_one", "lifted_id", "x"]
    a = G.TyVar { G.tyVarName = a_n, G.tyVarKind = G.LiftedTypeKind }
    one = G.Id { G.idName = one_n, G.idType = G.intHashTy }
    boxed_one = G.Id { G.idName = boxed_one_n, G.idType = G.intTy }
    lifted_id = G.Id { G.idName = lifted_id_n, G.idType = G.ForAllTy a (G.TyVarTy a `G.mkFunTy` G.TyVarTy a) }
    x = G.Id { G.idName = x_n, G.idType = G.TyVarTy a }


the_example :: G.Term
--the_example = functionExample
--the_example = dataExample
the_example = caseBoundFunctionExample


main :: IO ()
main = do
    ids <- initUniqueSupply 'x'
    let (ids', halt_n) = freshName ids "halt"
        halt = CoId { coIdName = halt_n, coIdType = [IntHashTy] }
        steps e = e : unfoldr (\s -> let e = stateToTerm s
                                     in case runLintM (lintTerm emptyUniqueMap (insertUniqueMap halt_n [IntHashTy] emptyUniqueMap) e) of
                                          []   -> fmap ((,) e) (step s)
                                          errs -> error (unlines (map pPrintRender errs))) s
          where s = (mkInScopeSet (S.singleton halt_n), M.empty, (substFromCoIdSubst (mkCoIdSubst (S.singleton halt)), e), [])
    putStrLn $ pPrintRender the_example
    mapM_ (putStrLn . pPrintRender) $ steps $ fromTerm (ids', emptyInScopeSet) (emptyUniqueMap, the_example) (Unknown halt)
