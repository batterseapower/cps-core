{-# LANGUAGE TupleSections, PatternGuards, ExistentialQuantification, DeriveFunctor, DeriveFoldable, DeriveTraversable, GeneralizedNewtypeDeriving,
             TypeSynonymInstances, FlexibleInstances, IncoherentInstances, OverlappingInstances, TypeOperators, CPP #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
module Utilities (
    module UniqueSupply,
    module Utilities,
    
    module Control.Arrow,
    module Control.Monad,
    
    module Data.Function,
    module Data.Maybe,
    module Data.List,
    
    module Debug.Trace,
    
    module Text.PrettyPrint.HughesPJClass
  ) where

import UniqueSupply

import Control.Arrow (first, second, (***), (&&&))
import Control.Monad hiding (join)

import Data.Function (on)
import Data.Maybe
import Data.Monoid
import Data.List
import qualified Data.IntMap as IM
import qualified Data.IntSet as IS
import qualified Data.Map as M
import qualified Data.Set as S
import Data.Tree
import qualified Data.Foldable as Foldable
import qualified Data.Traversable as Traversable

import Debug.Trace

import Text.PrettyPrint.HughesPJClass hiding (render, int, float, char)
import qualified Text.PrettyPrint.HughesPJClass as Pretty

import System.IO
import System.IO.Unsafe (unsafePerformIO)


-- | Copointed functors. The defining property is:
--
--   extract (fmap f a) == f (extract a)
class Functor f => Copointed f where
    extract :: f a -> a

instance Copointed ((,) a) where
    extract = snd


class Functor z => Zippable z where
    -- Naturality:
    --  fmap (first f)  (zip_ as bs) == zip_ (fmap f as) bs
    --  fmap (second f) (zip_ as bs) == zip_ as (fmap f bs)
    --
    -- Information preservation:
    --  fmap fst (zip_ as bs) == as
    --  fmap snd (zip_ as bs) == bs

    zip_ :: z a -> z b -> z (a, b)
    zip_ = zipWith_ (,)

    zipWith_ :: (a -> b -> c) -> z a -> z b -> z c
    zipWith_ f as bs = fmap (uncurry f) (zip_ as bs)


#ifdef MIN_VERSION_base
#if !(MIN_VERSION_base(4, 3, 0))

-- These instances are in base-4.3

instance Monad (Either a) where
    return = Right
    
    Left l  >>= _    = Left l
    Right x >>= fxmy = fxmy x

#endif
#endif


class Show1 f where
    showsPrec1 :: Show a => Int -> f a -> ShowS

instance (Show1 f, Show a) => Show (f a) where
    showsPrec = showsPrec1


class Eq1 f where
    eq1 :: Eq a => f a -> f a -> Bool

instance (Eq1 f, Eq a) => Eq (f a) where
    (==) = eq1


class Eq1 f => Ord1 f where
    compare1 :: Ord a => f a -> f a -> Ordering

instance (Ord1 f, Ord a) => Ord (f a) where
    compare = compare1


class Pretty1 f where
    pPrintPrec1 :: Pretty a => PrettyLevel -> Rational -> f a -> Doc

instance (Pretty1 f, Pretty a) => Pretty (f a) where
    pPrintPrec = pPrintPrec1


newtype (f :.: g) a = Comp { unComp :: f (g a) }

infixr 9 :.:

instance (Copointed f, Copointed g) => Copointed (f :.: g) where
    extract = extract . extract . unComp

instance (Show1 f, Show1 g) => Show1 (f :.: g) where
    showsPrec1 prec (Comp x) = showParen (prec >= appPrec) (showString "Comp" . showsPrec appPrec x)

instance (Eq1 f, Eq1 g) => Eq1 (f :.: g) where
    eq1 (Comp x1) (Comp x2) = x1 == x2

instance (Ord1 f, Ord1 g) => Ord1 (f :.: g) where
    compare1 (Comp x1) (Comp x2) = x1 `compare` x2

instance (Pretty1 f, Pretty1 g) => Pretty1 (f :.: g) where
    pPrintPrec1 level prec (Comp x) = pPrintPrec level prec x

instance (Functor f, Functor g) => Functor (f :.: g) where
    fmap f (Comp x) = Comp (fmap (fmap f) x)

instance (Foldable.Foldable f, Foldable.Foldable g) => Foldable.Foldable (f :.: g) where
    foldMap f = Foldable.foldMap (Foldable.foldMap f) . unComp

instance (Traversable.Traversable f, Traversable.Traversable g) => Traversable.Traversable (f :.: g) where
    traverse f = fmap Comp . Traversable.traverse (Traversable.traverse f) . unComp


newtype Down a = Down { unDown :: a } deriving (Eq)

instance Ord a => Ord (Down a) where
    Down a `compare` Down b = b `compare` a


-- | Natural numbers on the cheap (for efficiency reasons)
type Nat = Int


newtype Fin = Fin { unFin :: Int } deriving (Eq, Ord, Show, Pretty)
type FinSet = IS.IntSet
type FinMap = IM.IntMap


data Tag = TG { tagFin :: Fin, tagOccurrences :: Nat } deriving (Eq, Ord, Show)

instance Pretty Tag where
    pPrint (TG i occs) = pPrint i <> brackets (pPrint occs)

mkTag :: Int -> Tag
mkTag i = TG (Fin i) 1

injectTag :: Int -> Tag -> Tag
injectTag cls (TG (Fin i) occs) = TG (Fin (cls * i)) occs

tagInt :: Tag -> Int
tagInt = unFin . tagFin

data Tagged a = Tagged { tag :: !Tag, tagee :: !a }
              deriving (Functor, Foldable.Foldable, Traversable.Traversable)

instance Copointed Tagged where
    extract = tagee

instance Show1 Tagged where
    showsPrec1 prec (Tagged tg x) = showParen (prec >= appPrec) (showString "Tagged" . showsPrec appPrec tg . showsPrec appPrec x)

instance Eq1 Tagged where
    eq1 (Tagged tg1 x1) (Tagged tg2 x2) = tg1 == tg2 && x1 == x2

instance Ord1 Tagged where
    compare1 (Tagged tg1 x1) (Tagged tg2 x2) = (tg1, x1) `compare` (tg2, x2)

instance Pretty1 Tagged where
    pPrintPrec1 level prec (Tagged tg x) = braces (pPrint tg) <+> pPrintPrec level prec x


type Size = Int

data Sized a = Sized { size :: !Size, sizee :: !a }
             deriving (Functor, Foldable.Foldable, Traversable.Traversable)

instance Copointed Sized where
    extract = sizee

instance Show1 Sized where
    showsPrec1 prec (Sized sz x) = showParen (prec >= appPrec) (showString "Sized" . showsPrec appPrec sz . showsPrec appPrec x)

instance Eq1 Sized where
    eq1 (Sized sz1 x1) (Sized sz2 x2) = sz1 == sz2 && x1 == x2

instance Ord1 Sized where
    compare1 (Sized sz1 x1) (Sized sz2 x2) = (sz1, x1) `compare` (sz2, x2)

instance Pretty1 Sized where
    pPrintPrec1 level prec (Sized sz x) = bananas (text (show sz)) <> pPrintPrec level prec x


instance Show UniqueSupply where
    show = show . uniqueFromSupply


instance Pretty Doc where
    pPrint = id

instance Pretty Rational where
    pPrint = rational

instance Pretty Unique where
    pPrint = text . show

instance Pretty IS.IntSet where
    pPrint xs = braces $ hsep (punctuate comma (map pPrint $ IS.toList xs))

instance Pretty v => Pretty (IM.IntMap v) where
    pPrint m = brackets $ fsep (punctuate comma [pPrint k <+> text "|->" <+> pPrint v | (k, v) <- IM.toList m])

instance Pretty a => Pretty (S.Set a) where
    pPrint xs = braces $ hsep (punctuate comma (map pPrint $ S.toList xs))

instance (Pretty k, Pretty v) => Pretty (M.Map k v) where
    pPrint m = brackets $ fsep (punctuate comma [pPrint k <+> text "|->" <+> pPrint v | (k, v) <- M.toList m])

instance Pretty a => Pretty (Tree a) where
    pPrint = text . drawTree . fmap (show . pPrint)

deleteList :: Ord a => [a] -> S.Set a -> S.Set a
deleteList = flip $ foldr S.delete

deleteListMap :: Ord k => [k] -> M.Map k v -> M.Map k v
deleteListMap = flip $ foldr M.delete

fmapSet :: (Ord a, Ord b) => (a -> b) -> S.Set a -> S.Set b
fmapSet f = S.fromList . map f . S.toList

fmapMap :: (Ord a, Ord b) => (a -> b) -> M.Map a v -> M.Map b v
fmapMap f = M.fromList . map (first f) . M.toList

restrict :: Ord k => M.Map k v -> S.Set k -> M.Map k v
-- restrict m s
--   | M.size m < S.size s = M.filterWithKey (\k _ -> k `S.member` s) m                                                   -- O(m * log s)
--   | otherwise           = S.fold (\k out -> case M.lookup k m of Nothing -> out; Just v -> M.insert k v out) M.empty s -- O(s * log m)
restrict m s = M.fromDistinctAscList $ merge (M.toAscList m) (S.toAscList s)
  where
    -- Theoretically O(m + s), so should outperform previous algorithm...
    merge _              []       = []
    merge []             _        = []
    merge ((k_m, v):kvs) (k_s:ks) = case compare k_m k_s of
        LT ->          merge kvs            (k_s:ks)
        EQ -> (k_m, v):merge kvs            ks
        GT ->          merge ((k_m, v):kvs) ks

exclude :: Ord k => M.Map k v -> S.Set k -> M.Map k v
--exclude m s = M.filterWithKey (\k _ -> k `S.notMember` s) m -- O(m * log s)
exclude m s = M.fromDistinctAscList $ merge (M.toAscList m) (S.toAscList s)
  where
    -- Theoretically O(m + s), so should outperform previous algorithm...
    merge kvs            []       = kvs
    merge []             _        = []
    merge ((k_m, v):kvs) (k_s:ks) = case compare k_m k_s of
        LT -> (k_m, v):merge kvs            (k_s:ks)
        EQ ->          merge kvs            ks
        GT ->          merge ((k_m, v):kvs) ks

mapMaybeSet :: (Ord a, Ord b) => (a -> Maybe b) -> S.Set a -> S.Set b
mapMaybeSet f = S.fromList . mapMaybe f . S.toList

listToMap :: Ord k => v -> [k] -> M.Map k v
listToMap v = M.fromList . map (,v)

setToMap :: Ord k => v -> S.Set k -> M.Map k v
setToMap v = M.fromDistinctAscList . map (,v) . S.toAscList

-- Essentially XOR on sets. See <http://en.wikipedia.org/wiki/Symmetric_difference>
symmetricDifference :: Ord a => S.Set a -> S.Set a -> S.Set a
symmetricDifference a b = (a S.\\ b) `S.union` (b S.\\ a)


data Combining a b = LeftOnly a | Both a b | RightOnly b

{-# INLINE finishCombining #-}
finishCombining :: (a -> c) -> (b -> c) -> (a -> b -> c) -> Combining a b -> c
finishCombining l r both combining = case combining of
    LeftOnly x  -> l x
    Both x y    -> both x y
    RightOnly y -> r y

{-# INLINE combineMaps #-}
combineMaps :: Ord k
            => (a -> c) -> (b -> c) -> (a -> b -> c)
            -> M.Map k a -> M.Map k b -> M.Map k c
combineMaps l r both m1 m2 = M.map (finishCombining l r both) $ M.unionWith (\(LeftOnly x) (RightOnly y) -> Both x y) (M.map LeftOnly m1) (M.map RightOnly m2)

{-# INLINE combineIntMaps #-}
combineIntMaps :: (a -> c) -> (b -> c) -> (a -> b -> c)
               -> IM.IntMap a -> IM.IntMap b -> IM.IntMap c
combineIntMaps l r both im1 im2 = IM.map (finishCombining l r both) $ IM.unionWith (\(LeftOnly x) (RightOnly y) -> Both x y) (IM.map LeftOnly im1) (IM.map RightOnly im2)


{-# NOINLINE parseUniqueSupply #-}
parseUniqueSupply :: UniqueSupply
parseUniqueSupply = unsafePerformIO $ initUniqueSupply 'a'

{-# NOINLINE expandUniqueSupply #-}
expandUniqueSupply :: UniqueSupply
expandUniqueSupply = unsafePerformIO $ initUniqueSupply 'e'

{-# NOINLINE reduceUniqueSupply #-}
reduceUniqueSupply :: UniqueSupply
reduceUniqueSupply = unsafePerformIO $ initUniqueSupply 'u'

{-# NOINLINE tagUniqueSupply #-}
tagUniqueSupply :: UniqueSupply
tagUniqueSupply = unsafePerformIO $ initUniqueSupply 't'

{-# NOINLINE prettyUniqueSupply #-}
prettyUniqueSupply :: UniqueSupply
prettyUniqueSupply = unsafePerformIO $ initUniqueSupply 'p'

{-# NOINLINE prettifyUniqueSupply #-}
prettifyUniqueSupply :: UniqueSupply
prettifyUniqueSupply = unsafePerformIO $ initUniqueSupply 'r'

{-# NOINLINE matchUniqueSupply #-}
matchUniqueSupply :: UniqueSupply
matchUniqueSupply = unsafePerformIO $ initUniqueSupply 'm'

stepUniqueSupply :: UniqueSupply -> (UniqueSupply, Unique)
stepUniqueSupply = second uniqueFromSupply . splitUniqueSupply


data Train a b = Wagon a (Train a b)
               | Caboose b


appPrec, opPrec, noPrec :: Num a => a
appPrec = 2    -- Argument of a function application
opPrec  = 1    -- Argument of an infix operator
noPrec  = 0    -- Others

normalLevel, haskellLevel :: PrettyLevel
normalLevel = PrettyLevel 0
haskellLevel = PrettyLevel 1


pPrintPrecApp :: (Pretty a, Pretty b) => PrettyLevel -> Rational -> a -> b -> Doc
pPrintPrecApp level prec e1 e2 = prettyParen (prec >= appPrec) $ pPrintPrec level opPrec e1 <+> pPrintPrec level appPrec e2

pPrintPrecApps :: (Pretty a, Pretty b) => PrettyLevel -> Rational -> a -> [b] -> Doc
pPrintPrecApps level prec e1 es2 = prettyParen (not (null es2) && prec >= appPrec) $ pPrintPrec level opPrec e1 <+> hsep (map (pPrintPrec level appPrec) es2)


angles, coangles, bananas :: Doc -> Doc
angles d = Pretty.char '<' <> d <> Pretty.char '>'
coangles d = Pretty.char '>' <> d <> Pretty.char '<'
bananas d = text "(|" <> d <> text "|)"


pPrintPrec' :: Pretty a => a -> PrettyLevel -> Rational -> Doc
pPrintPrec' x level prec = pPrintPrec level prec x

-- NB: this render function is exported instead of the one from the library
render :: Doc -> String
render = renderStyle (style { lineLength = 120 })

pPrintRender :: Pretty a => a -> String
pPrintRender = render . pPrint

panic :: String -> Doc -> a
panic s d = error $ "PANIC!\n" ++ s ++ ": " ++ render d


traceRender :: Pretty a => a -> b -> b
traceRender x = trace (pPrintRender x)

traceRenderM :: (Pretty a, Monad m) => a -> m ()
traceRenderM x = traceRender x (return ())

assertRender :: Pretty a => a -> Bool -> b -> b
--assertRender _ _ x | not aSSERTIONS = x
assertRender _ True  x = x
assertRender a False _ = error (render $ text "ASSERT FAILED!" $$ pPrint a)

assertRenderM :: (Pretty a, Monad m) => a -> Bool -> m ()
assertRenderM a b = assertRender a b (return ())


removeOnes :: [a] -> [[a]]
removeOnes [] = []
removeOnes (x:xs) = xs : map (x:) (removeOnes xs)

listContexts :: [a] -> [([a], a, [a])]
listContexts xs = zipWith (\is (t:ts) -> (is, t, ts)) (inits xs) (init (tails xs))

bagContexts :: [a] -> [(a, [a])]
bagContexts xs = [(x, is ++ ts) | (is, x, ts) <- listContexts xs]

seperate :: Eq a => a -> [a] -> [[a]]
seperate c = go []
  where
    go sofar [] = [reverse sofar]
    go sofar (x:xs)
      | x == c    = reverse sofar : go [] xs
      | otherwise = go (x:sofar) xs


accumL :: (acc -> (acc, a)) -> acc -> Int -> (acc, [a])
accumL f = go
  where
    go acc n | n <= 0            = (acc, []) 
             | (acc, x) <- f acc = second (x:) (go acc (n - 1))


instance (Pretty a, Pretty b, Pretty c, Pretty d,
          Pretty e, Pretty f, Pretty g, Pretty h,
          Pretty i) => Pretty (a, b, c, d, e, f, g, h, i) where
    pPrint (a, b, c, d, e, f, g, h, i)
      = pPrintTuple [pPrint a, pPrint b, pPrint c, pPrint d,
                     pPrint e, pPrint f, pPrint g, pPrint h,
                     pPrint i]

instance (Pretty a, Pretty b, Pretty c, Pretty d,
          Pretty e, Pretty f, Pretty g, Pretty h,
          Pretty i, Pretty j) => Pretty (a, b, c, d, e, f, g, h, i, j) where
    pPrint (a, b, c, d, e, f, g, h, i, j)
      = pPrintTuple [pPrint a, pPrint b, pPrint c, pPrint d,
                     pPrint e, pPrint f, pPrint g, pPrint h,
                     pPrint i, pPrint j]

instance (Pretty a, Pretty b, Pretty c, Pretty d,
          Pretty e, Pretty f, Pretty g, Pretty h,
          Pretty i, Pretty j, Pretty k) => Pretty (a, b, c, d, e, f, g, h, i, j, k) where
    pPrint (a, b, c, d, e, f, g, h, i, j, k)
      = pPrintTuple [pPrint a, pPrint b, pPrint c, pPrint d,
                     pPrint e, pPrint f, pPrint g, pPrint h,
                     pPrint i, pPrint j, pPrint k]

instance (Pretty a, Pretty b, Pretty c, Pretty d,
          Pretty e, Pretty f, Pretty g, Pretty h,
          Pretty i, Pretty j, Pretty k, Pretty l) => Pretty (a, b, c, d, e, f, g, h, i, j, k, l) where
    pPrint (a, b, c, d, e, f, g, h, i, j, k, l)
      = pPrintTuple [pPrint a, pPrint b, pPrint c, pPrint d,
                     pPrint e, pPrint f, pPrint g, pPrint h,
                     pPrint i, pPrint j, pPrint k, pPrint l]

instance (Pretty a, Pretty b, Pretty c, Pretty d,
          Pretty e, Pretty f, Pretty g, Pretty h,
          Pretty i, Pretty j, Pretty k, Pretty l,
          Pretty m, Pretty n, Pretty o) => Pretty (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o) where
    pPrint (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o)
      = pPrintTuple [pPrint a, pPrint b, pPrint c, pPrint d,
                     pPrint e, pPrint f, pPrint g, pPrint h,
                     pPrint i, pPrint j, pPrint k, pPrint l,
                     pPrint m, pPrint n, pPrint o]

pPrintTuple :: [Doc] -> Doc
pPrintTuple ds = parens $ fsep $ punctuate comma ds


data SomePretty = forall a. Pretty a => SomePretty a

instance Pretty SomePretty where
    pPrintPrec level prec (SomePretty x) = pPrintPrec level prec x


newtype PrettyFunction = PrettyFunction (PrettyLevel -> Rational -> Doc)

instance Pretty PrettyFunction where
    pPrintPrec level prec (PrettyFunction f) = f level prec

asPrettyFunction :: Pretty a => a -> PrettyFunction
asPrettyFunction = PrettyFunction . pPrintPrec'


fst3 :: (a, b, c) -> a
fst3 (a, _, _) = a

snd3 :: (a, b, c) -> b
snd3 (_, b, _) = b

thd3 :: (a, b, c) -> c
thd3 (_, _, c) = c

first3 :: (a -> d) -> (a, b, c) -> (d, b, c)
first3 f (a, b, c) = (f a, b, c)

second3 :: (b -> d) -> (a, b, c) -> (a, d, c)
second3 f (a, b, c) = (a, f b, c)

third3 :: (c -> d) -> (a, b, c) -> (a, b, d)
third3 f (a, b, c) = (a, b, f c)

second4 :: (b -> e) -> (a, b, c, d) -> (a, e, c, d)
second4 f (a, b, c, d) = (a, f b, c, d)

third4 :: (c -> e) -> (a, b, c, d) -> (a, b, e, d)
third4 f (a, b, c, d) = (a, b, f c, d)

fourth4 :: (d -> e) -> (a, b, c, d) -> (a, b, c, e)
fourth4 f (a, b, c, d) = (a, b, c, f d)

secondM :: Monad m => (b -> m c) -> (a, b) -> m (a, c)
secondM f (a, b) = liftM (a,) $ f b


uncurry3 :: (a -> b -> c -> d) -> (a, b, c) -> d
uncurry3 f (a, b, c) = f a b c


splitBy :: [b] -> [a] -> ([a], [a])
splitBy []     xs     = ([], xs)
splitBy (_:ys) (x:xs) = first (x:) $ splitBy ys xs

splitByReverse :: [b] -> [a] -> ([a], [a])
splitByReverse ys xs = case splitBy ys (reverse xs) of (xs1, xs2) -> (reverse xs2, reverse xs1)

splitManyBy :: [[b]] -> [a] -> [[a]]
splitManyBy []       xs = [xs]
splitManyBy (ys:yss) xs = case splitBy ys xs of (xs1, xs2) -> xs1 : splitManyBy yss xs2

dropBy :: [b] -> [a] -> [a]
dropBy bs = snd . splitBy bs


dropLastWhile :: (a -> Bool) -> [a] -> [a]
dropLastWhile p = reverse . dropWhile p . reverse


orElse :: Maybe a -> a -> a
orElse = flip fromMaybe


takeFirst :: (a -> Bool) -> [a] -> (Maybe a, [a])
takeFirst p = takeFirstJust (\x -> guard (p x) >> return x)

takeFirstJust :: (a -> Maybe b) -> [a] -> (Maybe b, [a])
takeFirstJust p = go
  where
    go [] = (Nothing, [])
    go (x:xs)
      | Just y <- p x = (Just y, xs)
      | otherwise     = second (x:) $ go xs

extractJusts :: (a -> Maybe b) -> [a] -> ([b], [a])
extractJusts p = foldr step ([], [])
  where step x rest | Just y <- p x = first  (y:) rest
                    | otherwise     = second (x:) rest

expectJust :: String -> Maybe a -> a
expectJust _ (Just x) = x
expectJust s Nothing  = error $ "expectJust: " ++ s

safeFromLeft :: Either a b -> Maybe a
safeFromLeft (Left x) = Just x
safeFromLeft _        = Nothing

fmapEither :: (a -> b) -> (c -> d) -> Either a c -> Either b d
fmapEither f g = either (Left . f) (Right . g)

safeHead :: [a] -> Maybe a
safeHead []    = Nothing
safeHead (x:_) = Just x

expectHead :: String -> [a] -> a
expectHead s = expectJust s . safeHead

uncons :: [a] -> Maybe (a, [a])
uncons []     = Nothing
uncons (x:xs) = Just (x, xs)

at :: [a] -> Int -> Maybe a
at _ n | n < 0 = error "at: negative argument"
at []     _ = Nothing
at (x:_)  0 = Just x
at (_:xs) n = at xs (n - 1)

listSelectors :: [[a] -> a]
listSelectors = iterate (\f xs -> f (tail xs)) head

fixpoint :: Eq a => (a -> a) -> a -> a
fixpoint f x
   | x' == x   = x
   | otherwise = fixpoint f x'
  where x' = f x

zipWithEqualM :: Monad m => (a -> b -> m c) -> [a] -> [b] -> m [c]
zipWithEqualM _ []     []     = return []
zipWithEqualM f (x:xs) (y:ys) = liftM2 (:) (f x y) (zipWithEqualM f xs ys)
zipWithEqualM _ _ _ = fail "zipWithEqualM"

zipWithEqualM_ :: Monad m => (a -> b -> m ()) -> [a] -> [b] -> m ()
zipWithEqualM_ _ []     []     = return ()
zipWithEqualM_ f (x:xs) (y:ys) = f x y >> zipWithEqualM_ f xs ys
zipWithEqualM_ _ _ _ = fail "zipWithEqualM_"

zipEqual :: [a] -> [b] -> Maybe [(a, b)]
zipEqual = zipWithEqual (,)

zipWithEqual :: (a -> b -> c) -> [a] -> [b] -> Maybe [c]
zipWithEqual _ []     []     = Just []
zipWithEqual f (x:xs) (y:ys) = fmap (f x y :) $ zipWithEqual f xs ys
zipWithEqual _ _ _ = fail "zipWithEqual"

implies :: Bool -> Bool -> Bool
implies cond consq = not cond || consq


mapAccumM :: (Traversable.Traversable t, Monoid m) => (a -> (m, b)) -> t a -> (m, t b)
mapAccumM f ta = Traversable.mapAccumL (\m a -> case f a of (m', b) -> (m `mappend` m', b)) mempty ta


newtype Identity a = I { unI :: a }
                   deriving (Functor, Foldable.Foldable, Traversable.Traversable)

instance Show1 Identity where
    showsPrec1 prec (I x) = showParen (prec >= appPrec) (showString "Identity" . showsPrec appPrec x)

instance Eq1 Identity where
    eq1 (I x1) (I x2) = x1 == x2

instance Ord1 Identity where
    compare1 (I x1) (I x2) = x1 `compare` x2

instance Pretty1 Identity where
    pPrintPrec1 level prec (I x) = pPrintPrec level prec x

instance Copointed Identity where
    extract = unI

instance Monad Identity where
    return = I
    mx >>= fxmy = fxmy (unI mx)


sumMap :: (Foldable.Foldable f, Num b) => (a -> b) -> f a -> b
sumMap f = Foldable.foldr (\x n -> f x + n) 0


class (Functor t, Foldable.Foldable t) => Accumulatable t where
    mapAccumT  ::            (acc -> x ->   (acc, y)) -> acc -> t x ->   (acc, t y)
    mapAccumTM :: Monad m => (acc -> x -> m (acc, y)) -> acc -> t x -> m (acc, t y)
    
    mapAccumT f acc x = unI (mapAccumTM (\acc' x' -> I (f acc' x')) acc x)

fmapDefault :: (Accumulatable t) => (a -> b) -> t a -> t b
fmapDefault f = snd . mapAccumT (\() x -> ((), f x)) ()

foldMapDefault :: (Accumulatable t, Monoid m) => (a -> m) -> t a -> m
foldMapDefault f = fst . mapAccumT (\acc x -> (f x `mappend` acc, ())) mempty

instance Accumulatable [] where
    mapAccumT  = mapAccumL
    mapAccumTM = mapAccumLM

mapAccumLM :: Monad m => (acc -> x -> m (acc, y)) -> acc -> [x] -> m (acc, [y])
mapAccumLM f = go []
  where
    go ys acc []     = return (acc, reverse ys)
    go ys acc (x:xs) = do
      (acc, y) <- f acc x
      go (y:ys) acc xs

concatMapM :: Monad m => (a -> m [b]) -> [a] -> m [b]
concatMapM f = go
  where
    go [] = return []
    go (x:xs) = do
        ys <- f x
        liftM (ys ++) $ go xs

instance Ord k => Accumulatable (M.Map k) where
    mapAccumTM f acc = liftM (second M.fromList) . mapAccumTM (\acc (k, x) -> liftM (second (k,)) (f acc x)) acc . M.toList


type Bytes = Integer

fileSize :: FilePath -> IO Bytes
fileSize file = withFile file ReadMode hFileSize


data ListPoint a = ListPoint [a] a [a]

instance Functor ListPoint where
    fmap f (ListPoint xs y zs) = ListPoint (map f xs) (f y) (map f zs)

locateListPoint :: (a -> Bool) -> [a] -> ListPoint a
locateListPoint p = go []
  where go left [] = error "locateListPoint: no match"
        go left (here:right)
          | p here    = ListPoint (reverse left) here right
          | otherwise = go (here:left) right
