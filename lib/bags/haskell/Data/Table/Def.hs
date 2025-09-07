{-# LANGUAGE LambdaCase #-}
module Data.Table.Def 
    (
    -- * Type
    Table,
    -- $prop-Table-equality
    
    -- * Operations
    -- ** Query
    lookup,
    getMap,
    elements,
    -- ** Construction
    singleton,
    indexBy,
    fromMap,
    fromSingletonsMap,
    -- ** Combine
    merge,
    )
    where

import Prelude hiding (null, filter, lookup, map, concatMap, replicate)
import Data.Bag.Def (null)
import qualified Data.Bag.Def as Bag (cartesianProduct)
import Data.Bag.Quotient (Bag, foldBag)
import qualified Data.Bag.Quotient as Bag (singleton)
import Data.Map (Map)
import qualified Data.Map as Map (empty, intersectionWith, lookup, map, singleton, toAscList, unionWith)
import qualified Data.Monoid.Refinement (Commutative)

mergeRaw ::
           Ord k => Map k (Bag a) -> Map k (Bag b) -> Map k (Bag (a, b))
mergeRaw = Map.intersectionWith Bag.cartesianProduct

{-|
A 'Table' is a finite map from keys (indices) to finite 'Bag's
of values. Think @'Table' k a ~ 'Map' k ('Bag' a)@.

This type can also be viewed as a 'Bag' where elements have been grouped
by keys.
-}
newtype Table k a = MkTable{getTable :: Map k (Bag a)}

{-|
Get the 'Data.Map.Map' that stores the mapping from keys to 'Bag's.
-}
getMap :: Ord k => Table k a -> Map k (Bag a)
getMap = \ r -> getTable r

toBag :: Maybe (Bag a) -> Bag a
toBag Nothing = mempty
toBag (Just x) = x

{-|
Look up a key in a 'Table'.
-}
lookup :: Ord k => k -> Table k a -> Bag a
lookup = \ key -> toBag . Map.lookup key . \ r -> getTable r

{-|
Construct a 'Table' with a single item.
-}
singleton :: Ord k => k -> a -> Table k a
singleton key x = MkTable (Map.singleton key (Bag.singleton x))

instance (Ord k) => Semigroup (Table k a) where
    xs <> ys = MkTable (Map.unionWith (<>) (getTable xs) (getTable ys))

instance (Ord k) => Monoid (Table k a) where
    mempty = MkTable Map.empty

instance (Ord k) => Data.Monoid.Refinement.Commutative (Table k a)
         where

{-|
Helper function: Construct a 'Table' from a 'Bag' for a single key.
-}
fromKeyAndBag :: Ord k => k -> Bag a -> Table k a
fromKeyAndBag key xs
  = if null xs then mempty else MkTable (Map.singleton key xs)

{-|
Construct a 'Table' from a 'Map' from keys to 'Bag'.
-}
fromMap :: Ord k => Map k (Bag a) -> Table k a
fromMap
  = mconcat .
      fmap
        (\case
             (key, xs) -> fromKeyAndBag key xs)
        . Map.toAscList

{-|
Construct a 'Table' from a 'Map' from keys to items.
-}
fromSingletonsMap :: Ord k => Map k a -> Table k a
fromSingletonsMap = fromMap . Map.map Bag.singleton

{-|
Index the items in a 'Bag' by a function.
-}
indexBy :: Ord k => Bag a -> (a -> k) -> Table k a
indexBy xs f = foldBag (\ x -> singleton (f x) x) xs

{-|
Forget the grouping of items by key.
-}
elements :: Ord k => Table k a -> Bag a
elements = foldMap id . \ r -> getTable r

{-|
For each key, construct the 'Data.Bag.cartesianProduct' of 'Bag's.
-}
merge :: Ord k => Table k a -> Table k b -> Table k (a, b)
merge xs ys = MkTable (mergeRaw (getTable xs) (getTable ys))

-- * Properties
{- $prop-Table-<>-assoc
#p:prop-Table-<>-assoc#

[prop-Table-<>-assoc]:
    Union of 'Table' is associative
    
    > prop-Table-<>-assoc
    >   : ∀ {k} ⦃ _ : Ord k ⦄ (xs ys zs : Table k a)
    >   → (xs <> ys) <> zs ≡ xs <> (ys <> zs)
-}
{- $prop-Table-<>-mempty-x
#p:prop-Table-<>-mempty-x#

[prop-Table-<>-mempty-x]:
    Union with the empty 'Table' on the left is empty.
    
    > prop-Table-<>-mempty-x
    >   : ∀ {k} ⦃ _ : Ord k ⦄ (xs : Table k a)
    >   → mempty <> xs ≡ xs
-}
{- $prop-Table-<>-sym
#p:prop-Table-<>-sym#

[prop-Table-<>-sym]:
    The semigroup operation on 'Table' is commutative.
    
    > @0 prop-Table-<>-sym
    >   : ∀ {k} ⦃ _ : Ord k ⦄ (xs ys : Table k a)
    >   → xs <> ys ≡ ys <> xs
-}
{- $prop-Table-<>-x-mempty
#p:prop-Table-<>-x-mempty#

[prop-Table-<>-x-mempty]:
    Union with the empty 'Table' on the right is empty.
    
    > prop-Table-<>-x-mempty
    >   : ∀ {k} ⦃ _ : Ord k ⦄ (xs : Table k a)
    >   → xs <> mempty ≡ xs
-}
{- $prop-Table-equality
#p:prop-Table-equality#

[prop-Table-equality]:
    Two Tables are equal if they contain the same 'Map'.
    
    > prop-Table-equality
    >   : ∀ {k} ⦃ _ : Ord k ⦄ {xs ys : Table k a}
    >   → getMap xs ≡ getMap ys
    >   → xs ≡ ys
-}
{- $prop-lookup→equality
#p:prop-lookup→equality#

[prop-lookup→equality]:
    Tables that have the same 'lookup' function are equal.
    
    > @0 prop-lookup→equality
    >   : ∀ {k} ⦃ _ : Ord k ⦄ (xs ys : Table k a)
    >   → (∀ key → lookup key xs ≡ lookup key ys)
    >   → xs ≡ ys
-}
