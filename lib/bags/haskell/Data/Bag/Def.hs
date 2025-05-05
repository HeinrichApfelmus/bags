{-# OPTIONS_GHC -Wno-orphans #-}

module Data.Bag.Def where

import Prelude hiding (null, filter, map, concatMap)
import Data.Bag.Quotient (Bag, foldBag, singleton)



import Control.Monad (guard, MonadPlus)
import Control.Applicative (Alternative (..))

union :: Bag a -> Bag a -> Bag a
union = (<>)

fromMaybe :: Maybe a -> Bag a
fromMaybe Nothing = mempty
fromMaybe (Just x) = singleton x

concatMap :: (a -> Bag b) -> Bag a -> Bag b
concatMap = foldBag

map :: (a -> b) -> Bag a -> Bag b
map f = concatMap (singleton . f)

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

filter :: (a -> Bool) -> Bag a -> Bag a
filter p xs
  = do x <- xs
       guard (p x)
       pure x

cartesianProduct :: Bag a -> Bag b -> Bag (a, b)
cartesianProduct xs ys
  = do x <- xs
       y <- ys
       pure (x, y)

equijoin ::
           Eq k => (a -> k) -> (b -> k) -> Bag a -> Bag b -> Bag (a, b)
equijoin f g xs ys
  = do x <- xs
       y <- ys
       guard (f x == g y)
       pure (x, y)

