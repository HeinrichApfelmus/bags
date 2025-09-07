{-# LANGUAGE StandaloneDeriving #-}
{-# OPTIONS_GHC -Wno-unused-top-binds -Wno-orphans #-}

module Data.Bag.Counts 
    (
    -- * Type
    Counts (..),
    -- ** Construction
    singleton,
    -- ** Conversion
    natFromPositiveNat,
    toCounts,
    fromCounts,
    fromUnique,
    )
    where

import Prelude hiding (null, filter, lookup, map, concatMap, replicate)
import Data.Bag.Quotient (Bag, foldBag)
import qualified Data.Bag.Quotient as Bag (singleton)
import Data.List.Extra (replicateNat)
import Data.Map (Map)
import qualified Data.Map as Map (empty, mapWithKey, singleton, toAscList, unionWith)
import qualified Data.Monoid.Refinement (Commutative)
import Numeric.Natural (Natural)

{-|
A positive natural number.
-}
newtype PositiveNat = OnePlus Natural

deriving instance Eq PositiveNat

one :: PositiveNat
one = OnePlus 0

natFromPositiveNat :: PositiveNat -> Natural
natFromPositiveNat (OnePlus x) = x + 1

instance Semigroup PositiveNat where
    OnePlus x <> OnePlus y = OnePlus (x + y + 1)

{-|
Construct a 'Bag' by replicating one item multiple times.
-}
replicatePositiveNat :: PositiveNat -> a -> Bag a
replicatePositiveNat n x
  = mconcat $ replicateNat (natFromPositiveNat n) (Bag.singleton x)

{-|
'Counts' is a different representation for 'Bag',
where items are mapped to their number of occurrences.

-}
newtype Counts a = MkCounts{getCounts :: Map a PositiveNat}

deriving instance (Ord a) => Eq (Counts a)

{-|
Construct a 'Counts' with a single item.
-}
singleton :: Ord a => a -> Counts a
singleton x = MkCounts (Map.singleton x one)

instance (Ord a) => Semigroup (Counts a) where
    xs <> ys
      = MkCounts (Map.unionWith (<>) (getCounts xs) (getCounts ys))

instance (Ord a) => Monoid (Counts a) where
    mempty = MkCounts Map.empty

instance (Ord a) => Data.Monoid.Refinement.Commutative (Counts a)
         where

mtoCounts :: Ord a => Bag a -> Counts a
mtoCounts = foldBag singleton

{-|
Convert a 'Bag' to a mapping from items to their number of occurrences.
-}
toCounts :: Ord a => Bag a -> Map a Natural
toCounts
  = fmap natFromPositiveNat . (\ r -> getCounts r) . mtoCounts

replicateBag :: Natural -> a -> Bag a
replicateBag n x = mconcat $ replicateNat n (Bag.singleton x)

{-|
Convert a map of items and their number of occurrences to a 'Bag'.
-}
fromCounts :: Ord a => Map a Natural -> Bag a
fromCounts = foldMap id . Map.mapWithKey (flip replicateBag)

mfromCounts :: Ord a => Counts a -> Bag a
mfromCounts
  = foldMap id .
      Map.mapWithKey (flip replicatePositiveNat) . \ r -> getCounts r

instance (Ord a) => Eq (Bag a) where
    xs == ys = mtoCounts xs == mtoCounts ys

{-|
Given a 'Bag' that contains only one unique item
(though perhaps multiple times), extract that item.
-}
fromUnique :: Ord a => Bag a -> Maybe a
fromUnique xs
  = case Map.toAscList (toCounts xs) of
        [(x, _)] -> Just x
        _ -> Nothing

-- * Properties
{- $prop-Counts-<>-assoc
#p:prop-Counts-<>-assoc#

[prop-Counts-<>-assoc]:
    Union of 'Counts' is associative
    
    > prop-Counts-<>-assoc
    >   : ∀ ⦃ _ : Ord a ⦄ (xs ys zs : Counts a)
    >   → (xs <> ys) <> zs ≡ xs <> (ys <> zs)
-}
{- $prop-Counts-<>-mempty-x
#p:prop-Counts-<>-mempty-x#

[prop-Counts-<>-mempty-x]:
    Union with the empty 'Counts' on the left is empty.
    
    > prop-Counts-<>-mempty-x
    >   : ∀ ⦃ _ : Ord a ⦄ (xs : Counts a)
    >   → mempty <> xs ≡ xs
-}
{- $prop-Counts-<>-sym
#p:prop-Counts-<>-sym#

[prop-Counts-<>-sym]:
    Union of 'Counts' is commutative.
    
    > prop-Counts-<>-sym
    >   : ∀ ⦃ _ : Ord a ⦄ (xs ys : Counts a)
    >   → xs <> ys ≡ ys <> xs
-}
{- $prop-Counts-<>-x-mempty
#p:prop-Counts-<>-x-mempty#

[prop-Counts-<>-x-mempty]:
    Union with the empty 'Counts' on the right is empty.
    
    > prop-Counts-<>-x-mempty
    >   : ∀ ⦃ _ : Ord a ⦄ (xs : Counts a)
    >   → xs <> mempty ≡ xs
-}
{- $prop-Counts-equality
#p:prop-Counts-equality#

[prop-Counts-equality]:
    Two 'Counts' are equal if they are the same 'Map'.
    
    > prop-Counts-equality
    >   : ∀ ⦃ _ : Ord a ⦄ {xs ys : Counts a}
    >   → getCounts xs ≡ getCounts ys
    >   → xs ≡ ys
-}
