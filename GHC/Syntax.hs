{-# LANGUAGE PatternGuards, ViewPatterns, TypeSynonymInstances, FlexibleInstances, Rank2Types #-}
module GHC.Syntax where

import GHC.Coercion
import GHC.Data
import GHC.Type
import GHC.Primitives
import GHC.Var
import GHC.Kind

import Name
import Utilities


data AltCon = DataAlt DataCon [TyVar] [Id] | LiteralAlt Literal | DefaultAlt
            deriving (Eq, Show)

-- Note [Case wildcards]
-- ~~~~~~~~~~~~~~~~~~~~~
--
-- Simon thought that I should use the variable in the DefaultAlt to agressively rewrite occurences of a scrutinised variable.
-- The motivation is that this lets us do more inlining above the case. For example, take this code fragment from foldl':
--
--   let n' = c n y
--   in case n' of wild -> foldl' c n' ys
--
-- If we rewrite, n' becomes linear:
--
--   let n' = c n y
--   in case n' of wild -> foldl c wild ys
--
-- This lets us potentially inline n' directly into the scrutinee position (operationally, this prevent creation of a thunk for n').
-- However, I don't think that this particular form of improving linearity helps the supercompiler. We only want to inline n' in
-- somewhere if it meets some interesting context, with which it can cancel. But if we are creating an update frame for n' at all,
-- it is *probably* because we had no information about what it evaluated to.
--
-- An interesting exception is when n' binds a case expression:
--
--   let n' = case unk of T -> F; F -> T
--   in case (case n' of T -> F; F -> T) of
--        wild -> e[n']
--
-- You might think that we want n' to be linear so we can inline it into the case on it. However, the splitter will save us and produce:
--
--   case unk of
--     T -> let n' = F
--          in case (case n' of T -> F; F -> T) of wild -> e[n']
--     F -> let n' = T
--          in case (case n' of T -> F; F -> T) of wild -> e[n']
--
-- Since we now know the form of n', everything works out nicely.
--
-- Conclusion: I don't think rewriting to use the case wildcard buys us anything at all.

data Term = Var Id
          | Value Value
          | App Term Id
          | TyApp Term Type
          | PrimOp PrimOp [Term]
          | Case Term Type Id [Alt]
          | LetRec [(Id, Term)] Term
          | Cast Term Coercion
          deriving (Eq, Show)

type Alt = (AltCon, Term)

data Value = Coercion Coercion | Lambda Var Term | Data DataCon [Type] [Type] [Id] | Literal Literal
            deriving (Eq, Show)

instance Pretty Term where
    pPrintPrec level prec e = case e of
        LetRec xes e    -> pPrintPrecLetRec level prec xes e
        Var x           -> pPrintPrec level prec x
        Value v         -> pPrintPrec level prec v
        App e1 x2       -> pPrintPrecApp level prec e1 x2
        TyApp e1 ty2    -> pPrintPrecApp level prec e1 ty2
        PrimOp pop xs   -> pPrintPrecApps level prec pop xs
        Case e _ x alts -> pPrintPrecCase level prec e x alts
        Cast e co       -> pPrintPrecCast level prec e co

pPrintPrecCase :: (Pretty a, Pretty b, Pretty c, Pretty d) => PrettyLevel -> Rational -> a -> d -> [(b, c)] -> Doc
pPrintPrecCase level prec e x alts = prettyParen (prec > noPrec) $ hang (text "case" <+> pPrintPrec level noPrec e <> text "@" <> pPrintPrec level noPrec x <+> text "of") 2 $ vcat (map (pPrintPrecAlt level noPrec) alts)

pPrintPrecAlt :: (Pretty a, Pretty b) => PrettyLevel -> Rational -> (a, b) -> Doc
pPrintPrecAlt level _ (alt_con, alt_e) = hang (pPrintPrec level noPrec alt_con <+> text "->") 2 (pPrintPrec level noPrec alt_e)

pPrintPrecCast :: (Pretty a, Pretty b) => PrettyLevel -> Rational -> a -> b -> Doc
pPrintPrecCast level prec e co = prettyParen (prec >= appPrec) $ pPrintPrec level opPrec e <+> text "|>" <+> pPrintPrec level appPrec co

instance Pretty AltCon where
    pPrintPrec level prec altcon = case altcon of
        DataAlt dc xtys xs -> prettyParen (prec >= appPrec) $ pPrintPrec level noPrec dc <+> hsep (map (pPrintPrec level appPrec) xtys ++ map (pPrintPrec level appPrec) xs)
        LiteralAlt l       -> pPrint l
        DefaultAlt         -> text "_"

instance Pretty Value where
    pPrintPrec level prec v = case v of
        -- Unfortunately, this nicer pretty-printing doesn't work for general (TermF ann):
        --Lambda x e    -> pPrintPrecLam level prec (x:xs) e'
        --  where (xs, e') = collectLambdas e
        Lambda x e           -> pPrintPrecLams level prec [x] e
        Data dc utys xtys xs -> pPrintPrecApps level prec dc (map asPrettyFunction utys ++ map asPrettyFunction xtys ++ map asPrettyFunction xs)
        Literal l            -> pPrintPrec level prec l
        Coercion co          -> pPrintPrec level prec co

pPrintPrecLams :: Pretty a => PrettyLevel -> Rational -> [Var] -> a -> Doc
pPrintPrecLams level prec xs e = prettyParen (prec > noPrec) $ text "\\" <> hsep [pPrintPrec level appPrec y | y <- xs] <+> text "->" <+> pPrintPrec level noPrec e


termType :: Term -> Type
termType (Var x) = idType x
termType (Value v) = valueType v
termType (App e _) = funResTy (termType e)
termType (TyApp e ty) = instTy (termType e) ty
termType (PrimOp pop es) = case (pop, map termType es) of
    (pop, [ty1, ty2])
      | pop `elem` [Add, Subtract, Multiply, Divide, Modulo]
      , ty1 == intHashTy
      , ty2 == intHashTy
      -> intTy
      | pop `elem` [Equal, LessThan, LessThanEqual]
      , ty1 == intHashTy
      , ty2 == intHashTy
      -> boolTy
    _ -> error "termType: PrimOp"
termType (Case _ ty _ _) = ty
termType (LetRec _ e) = termType e
termType (Cast _ co) = snd $ coercionType' co

valueType :: Value -> Type
valueType (Coercion co)          = coercionType co
valueType (Lambda x e)           = mkPiTy x (termType e)
valueType (Data dc utys xtys xs) = nTimes (length xs) funResTy $ foldl' instTy (dataConType dc) (utys ++ xtys)
valueType (Literal l)            = literalType l

literalType :: Literal -> Type
literalType (Int _) = intHashTy


freshFloatId :: UniqueSupply -> String -> Term -> (UniqueSupply, Maybe (Id, Term), Id)
freshFloatId ids _ (Var x) = (ids,  Nothing,     x)
freshFloatId ids s e       = (ids', Just (y, e), y)
  where (ids', n) = freshName ids s
        y = Id n (termType e)

freshFloatIds :: UniqueSupply -> String -> [Term] -> (UniqueSupply, [(Id, Term)], [Id])
freshFloatIds ids s es = reassociate $ mapAccumL (\ids -> associate . freshFloatId ids s) ids es
  where reassociate (ids, unzip -> (mb_floats, xs)) = (ids, catMaybes mb_floats, xs)
        associate (ids, mb_float, x) = (ids, (mb_float, x))
