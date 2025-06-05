module Data.Bag.Found where

import Prelude hiding (null, filter, map, concatMap)
import Data.Bag.Quotient (Bag, foldBag, singleton)
import qualified Data.Monoid.Refinement (Commutative)

data Found a = MkFound{found :: Maybe a, rest :: Bag a}

emptyFound :: Found a
emptyFound = MkFound Nothing mempty

unionFound :: Found a -> Found a -> Found a
unionFound (MkFound Nothing r1) (MkFound Nothing r2)
  = MkFound Nothing (r1 <> r2)
unionFound (MkFound Nothing r1) (MkFound (Just y2) r2)
  = MkFound (Just y2) (r1 <> r2)
unionFound (MkFound (Just y1) r1) (MkFound Nothing r2)
  = MkFound (Just y1) (r1 <> r2)
unionFound (MkFound (Just y1) r1) (MkFound (Just y2) r2)
  = MkFound (Just y1) (r1 <> singleton y2 <> r2)

instance Semigroup (Found a) where
    (<>) = unionFound

instance Monoid (Found a) where
    mempty = emptyFound

here :: a -> Found a
here x = MkFound (Just x) mempty

elsewhere :: a -> Found a
elsewhere y = MkFound Nothing (singleton y)

putBack :: Found a -> Bag a
putBack (MkFound Nothing xs) = xs
putBack (MkFound (Just x) xs) = singleton x <> xs

instance (Eq a) => Data.Monoid.Refinement.Commutative (Found a)
         where

findOne :: Eq a => a -> a -> Found a
findOne x y = if x == y then here y else elsewhere y

deleteOne :: Eq a => a -> Bag a -> Bag a
deleteOne x = (\ r -> rest r) . foldBag (findOne x)

