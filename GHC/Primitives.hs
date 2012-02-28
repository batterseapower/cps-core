module GHC.Primitives where

import Utilities


data PrimOp = Add | Subtract | Multiply | Divide | Modulo | Equal | LessThan | LessThanEqual
            deriving (Eq, Ord, Show)

data Literal = Int Integer
             deriving (Eq, Show)

instance Pretty PrimOp where
    pPrint Add           = text "(+)"
    pPrint Subtract      = text "(-)"
    pPrint Multiply      = text "(*)"
    pPrint Divide        = text "div"
    pPrint Modulo        = text "mod"
    pPrint Equal         = text "(==)"
    pPrint LessThan      = text "(<)"
    pPrint LessThanEqual = text "(<=)"

instance Pretty Literal where
    pPrintPrec level prec (Int i) | level == haskellLevel = prettyParen (prec >= appPrec) $ pPrintPrec level appPrec i <+> text ":: Int"
                                  | otherwise             = pPrintPrec level prec i
