{-# OPTIONS_GHC -Wno-orphans #-}

module Data.Bag.Def where

import Prelude hiding (null, filter, lookup, map, concatMap)
import Data.Bag.Quotient (Bag, foldBag, singleton)
import Data.Monoid.Extra (Conj(MkConj, getConj), Disj(MkDisj, getDisj), Sum'(MkSum, getSum'))
import Data.Monoid.Refinement ()



import Control.Monad (guard, MonadPlus)
import Control.Applicative (Alternative (..))

{-|
Test whether the 'Bag' is empty, 'Monoid' version.
-}
mnull :: Bag a -> Conj
mnull = foldBag (\ _ -> MkConj False)

{-|
Is the given 'Bag' empty?
-}
null :: Bag a -> Bool
null = (\ r -> getConj r) . mnull

{-|
Union of all items from the two argument 'Bag's.
Synonym for '(<>)'.
-}
union :: Bag a -> Bag a -> Bag a
union = (<>)

{-|
Construct a 'Bag' that may be empty or contains a single item.
-}
fromMaybe :: Maybe a -> Bag a
fromMaybe Nothing = mempty
fromMaybe (Just x) = singleton x

{-|
The number of items in the Bag, Monoid version
-}
msize :: Bag a -> Sum' Int
msize = foldBag (\ _ -> MkSum 1)

{-|
The number of items in the Bag.
-}
size :: Bag a -> Int
size = (\ r -> getSum' r) . msize

{-|
Apply a function to all items in the 'Bag'
and take the 'union' of the results.
-}
concatMap :: (a -> Bag b) -> Bag a -> Bag b
concatMap = foldBag

{-|
Apply a function to all items in the 'Bag'.
-}
map :: (a -> b) -> Bag a -> Bag b
map f = concatMap (singleton . f)

{-|
Construct a 'Bag' with the same items as the given list.
-}
fromList :: [a] -> Bag a
fromList = foldMap singleton

instance Functor Bag where
    fmap = map

instance Monad Bag where
    (>>=) = flip concatMap

instance Alternative Bag where
    empty = mempty
    (<|>) = (<>)

-- Workaround instance for issue in Agda2hs.
-- Issue: Definitions of `pure` and `<*>` are duplicated for some reason.
instance Applicative Bag where
  pure = singleton
  fs <*> xs = concatMap (\ f -> map f xs) fs

-- Workaround instance for issue in Agda2hs
instance MonadPlus Bag

{-|
Keep those elements that satisfy a predicate.
-}
filter :: (a -> Bool) -> Bag a -> Bag a
filter p xs
  = do x <- xs
       guard (p x)
       pure x

{-|
Count the number of times that an item is contained in the 'Bag'.
-}
count :: Eq a => a -> Bag a -> Int
count x = size . filter (x ==)

{-|
Test whether an item is contained in the 'Bag' at least once,
'Monoid' version.
-}
mmember :: Eq a => a -> Bag a -> Disj
mmember x = foldBag (\ y -> if x == y then MkDisj True else mempty)

{-|
Is the given item contain in the 'Bag' at least once?
-}
member :: Eq a => a -> Bag a -> Bool
member x = (\ r -> getDisj r) . mmember x

{-|
Construct the 'Bag' containing all possible pairs of items.
-}
cartesianProduct :: Bag a -> Bag b -> Bag (a, b)
cartesianProduct xs ys
  = do x <- xs
       y <- ys
       pure (x, y)

{-|
Construct the 'Bag' containing all possible pairs of items where
the functions yield the same result.
-}
equijoin ::
           Eq k => (a -> k) -> (b -> k) -> Bag a -> Bag b -> Bag (a, b)
equijoin f g xs ys
  = do x <- xs
       y <- ys
       guard (f x == g y)
       pure (x, y)

