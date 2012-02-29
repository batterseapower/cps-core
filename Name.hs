module Name (
    Name(..),
    freshName, freshNames,
    shadowyNames,

    InScopeSet,
    emptyInScopeSet, mkInScopeSet,
    uniqAway, uniqAwayName
  ) where

import Utilities

import Data.Char
import Data.Ord
import qualified Data.Set as S

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

instance Uniqueable Name where
    getUnique = nameUnique

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


newtype InScopeSet = ISS (S.Set Unique)

emptyInScopeSet :: InScopeSet
emptyInScopeSet = ISS S.empty

mkInScopeSet :: (Ord a, Uniqueable a) => S.Set a -> InScopeSet
mkInScopeSet = ISS . S.map getUnique

uniqAway :: InScopeSet -> Unique -> (InScopeSet, Unique)
uniqAway (ISS iss) = go
  where go u | u `S.member` iss = go (bumpUnique u)
             | otherwise        = (ISS (S.insert u iss), u)

uniqAwayName :: InScopeSet -> Name -> (InScopeSet, Name)
uniqAwayName iss n = (iss', n { nameUnique = u' })
  where (iss', u') = uniqAway iss (nameUnique n)
