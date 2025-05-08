module Data.Table.Def where

import Prelude hiding (null, filter, map, concatMap)
import qualified Data.Bag.Def as Bag (cartesianProduct)
import Data.Bag.Quotient (Bag, foldBag)
import qualified Data.Bag.Quotient as Bag (singleton)
import Data.Map (Map)
import qualified Data.Map as Map (empty, intersectionWith, lookup, singleton, unionWith)
import qualified Data.Monoid.Refinement (Commutative)

isJust :: Maybe a -> Bool
isJust Nothing = False
isJust (Just _) = True

mergeRaw ::
           Ord k => Map k (Bag a) -> Map k (Bag b) -> Map k (Bag (a, b))
mergeRaw = Map.intersectionWith Bag.cartesianProduct

newtype Table k a = MkTable{getTable :: Map k (Bag a)}

toBag :: Maybe (Bag a) -> Bag a
toBag Nothing = mempty
toBag (Just x) = x

lookup :: Ord k => k -> Table k a -> Bag a
lookup = \ key -> toBag . Map.lookup key . \ r -> getTable r

singleton :: Ord k => k -> a -> Table k a
singleton key x = MkTable (Map.singleton key (Bag.singleton x))

instance (Ord k) => Semigroup (Table k a) where
    MkTable xs <> MkTable ys = MkTable (Map.unionWith (<>) xs ys)

instance (Ord k) => Monoid (Table k a) where
    mempty = MkTable Map.empty

instance (Ord k) => Data.Monoid.Refinement.Commutative (Table k a)
         where

indexBy :: Ord k => Bag a -> (a -> k) -> Table k a
indexBy xs f = foldBag (\ x -> singleton (f x) x) xs

elements :: Ord k => Table k a -> Bag a
elements = foldMap id . \ r -> getTable r

merge :: Ord k => Table k a -> Table k b -> Table k (a, b)
merge xs ys = MkTable (mergeRaw (getTable xs) (getTable ys))

