module Data.Bag.Found where

import Prelude hiding (null, filter, map, concatMap)
import Data.Bag.Quotient (Bag, singleton)

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

