{-# LANGUAGE MagicHash #-}

-- | This module provides splittable supplies for unique identifiers.
--   The main idea gows back to L. Augustsson, M. Rittri, and D. Synek
--   and is described in their paper 'On generating unique names'
--   (Journal of Functional Programming 4(1), 1994. pp. 117-123). The
--   implementation at hand is taken from the GHC sources and includes
--   bit fiddling to allow multiple supplies that generate unique
--   identifiers by prepending a character given at initialization.
--
--   This is a custom version of uniqueid-0.1.1 to resolve some bugs I
--   found in it.
module UniqueSupply (
    Unique, hashedUnique, UniqueSupply, initUniqueSupply, splitUniqueSupplyL, splitUniqueSupply, uniqueFromSupply
  ) where

import GHC.Exts
-- MCB: change to uniqueid-0.1.1: use GHC.IO rather than GHC.IOBase
import GHC.IO ( unsafeDupableInterleaveIO )

import Data.IORef
import System.IO.Unsafe ( unsafePerformIO )


-- | Unique identifiers are of type 'Unique' and can be hashed to an 'Int'
--   usning the function 'hashedUnique'.
newtype Unique = Unique { hashedUnique :: Int }

-- | Supplies for unique identifiers are of type 'UniqueSupply' and can be
--   split into two new supplies or yield a unique identifier.
data UniqueSupply = UniqueSupply Int# UniqueSupply UniqueSupply

-- | Generates a new supply of unique identifiers. The given character
--   is prepended to generated numbers.
initUniqueSupply :: Char -> IO UniqueSupply
initUniqueSupply (C# c) =
 case uncheckedIShiftL# (ord# c) (unboxedInt 24) of
  mask ->
   let mkSupply =
        unsafeDupableInterleaveIO (
         nextInt  >>= \ (I# u) ->
         mkSupply >>= \ l ->
         mkSupply >>= \ r ->
         return (UniqueSupply (word2Int# (or# (int2Word# mask) (int2Word# u))) l r))
    in mkSupply

-- | Splits a supply of unique identifiers to yield two of them.
splitUniqueSupply :: UniqueSupply -> (UniqueSupply,UniqueSupply)
splitUniqueSupply (UniqueSupply _ l r) = (l,r)

-- | Splits a supply of unique identifiers to yield an infinite list of them.
splitUniqueSupplyL :: UniqueSupply -> [UniqueSupply]
splitUniqueSupplyL ids = ids1 : splitUniqueSupplyL ids2
    where
      (ids1, ids2) = splitUniqueSupply ids

-- | Yields the unique identifier from a supply.
uniqueFromSupply :: UniqueSupply -> Unique
uniqueFromSupply (UniqueSupply n _ _) = Unique (I# n)

instance Eq Unique where Unique (I# x) == Unique (I# y) = x ==# y

instance Ord Unique
 where
  Unique (I# x) <  Unique (I# y) = x <#  y
  Unique (I# x) <= Unique (I# y) = x <=# y

  compare (Unique (I# x)) (Unique (I# y)) =
   if x ==# y then EQ else if x <# y then LT else GT

instance Show Unique
 where
  showsPrec _ i s = case unpackUnique i of (c,n) -> c:show n++s




unboxedInt :: Int -> Int#
unboxedInt (I# x) = x

-- MCB: change to uniqueid-0.1.1: ensure that the global IORef is not inlined!
{-# NOINLINE global #-}
global :: IORef Int
global = unsafePerformIO (newIORef 0)

-- MCB: change to uniqueid-0.1.1: prevent race conditions
nextInt :: IO Int
nextInt = atomicModifyIORef global (\n -> (succ n, succ n))

unpackUnique :: Unique -> (Char,Int)
unpackUnique (Unique (I# i)) =
 let tag = C# (chr# (uncheckedIShiftRL# i (unboxedInt 24)))
     num = I# (word2Int# (and# (int2Word# i)
                               (int2Word# (unboxedInt 16777215))))
  in (tag, num)