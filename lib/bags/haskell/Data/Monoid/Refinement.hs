module Data.Monoid.Refinement where

import Prelude hiding (null, filter, map, concatMap)
import Data.Monoid.Extra (Conj, Disj, Sum')

class Monoid a => Commutative a where

instance Commutative () where

instance (Commutative a, Commutative b) => Commutative ((a, b))
         where

instance (Commutative a, Commutative b, Commutative c) =>
         Commutative ((a, b, c))
         where

instance Commutative Conj where

instance Commutative Disj where

instance (Num a) => Commutative (Sum' a) where

