module Data.Bag.Raw where

import Prelude hiding (null, filter, map, concatMap)

data Bag a = Single a
           | Empty
           | Union (Bag a) (Bag a)

singleton :: a -> Bag a
singleton = Single

empty :: Bag a
empty = Empty

union :: Bag a -> Bag a -> Bag a
union Empty ys = ys
union xs Empty = xs
union xs ys = Union xs ys

foldBag :: Monoid b => (a -> b) -> Bag a -> b
foldBag _ Empty = mempty
foldBag f (Single x) = f x
foldBag f (Union xs ys) = foldBag f xs <> foldBag f ys

