module Name (
    Name(..),
    freshName, freshNames,
    shadowyNames
  ) where

import Utilities

import Data.Char
import Data.Ord

import System.IO.Unsafe (unsafePerformIO)


{-# NOINLINE shadowyNameUniques #-}
shadowyNameUniques :: UniqueSupply
shadowyNameUniques = unsafePerformIO (initUniqueSupply 'v')

shadowyNames :: [String] -> [Name]
shadowyNames = snd . freshNames shadowyNameUniques


data Name = Name {
    nameString :: String,
    nameUnique :: !Unique
  }

instance Show Name where
    show n = "(name " ++ show (show (pPrint n)) ++ ")"

instance Eq Name where
    (==) = (==) `on` nameUnique

instance Ord Name where
    compare = compare `on` nameUnique

instance Pretty Name where
    pPrintPrec level _ n = text (escape $ nameString n) <> text "_" <> text (show (nameUnique n))
      where escape | level == haskellLevel = concatMap escapeHaskellChar
                   | otherwise             = id
            escapeHaskellChar c
              | c == 'z'                             = "zz"
              | isAlphaNum c || c `elem` ['_', '\''] = [c]
              | otherwise                            = 'z' : show (ord c)

freshName :: UniqueSupply -> String -> (UniqueSupply, Name)
freshName us s = second (Name s) $ stepUniqueSupply us

freshNames :: UniqueSupply -> [String] -> (UniqueSupply, [Name])
freshNames = mapAccumL freshName
