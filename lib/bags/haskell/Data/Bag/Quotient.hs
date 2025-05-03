module Data.Bag.Quotient
    ( Bag
    , singleton
    , foldBag
    ) where

import qualified Data.Bag.Raw as Raw

import qualified Data.Monoid.Refinement as Monoid

-- | A 'Bag'@ a@ is a collection of items of type @a@.
-- Items may appear multiple times.
-- The order of items does __not__ matter.
--
-- Put differently,
-- 'Bag'@ a@ is the free commutative monoid on items of type @a@.
newtype Bag a = Bag (Raw.Bag a)

-- | '(<>)' is the union of two 'Bag's.
instance Semigroup (Bag a) where
    (Bag xs) <> (Bag ys) = Bag (Raw.union xs ys)

-- | 'mempty' is the empty 'Bag'.
instance Monoid (Bag a) where
    mempty = Bag Raw.empty

-- | The union of two 'Bag's is commutative.
instance Monoid.Commutative (Bag a)

-- | 'Bag' containing a single item.
singleton :: a -> Bag a
singleton = Bag . Raw.singleton

-- | Map all items from a 'Bag' to another commutative monoid,
-- and combine the results.
--
-- Put differently,
-- 'foldBag' is the universal map from 'Bag' to any other commutative monoid.
foldBag :: Monoid.Commutative b => (a -> b) -> Bag a -> b
foldBag f (Bag xs) = Raw.foldBag f xs
