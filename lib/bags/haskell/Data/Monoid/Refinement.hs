module Data.Monoid.Refinement where

import Prelude hiding (null, filter, map, concatMap)
import Data.Monoid.Extra (Conj)

class Monoid a => Commutative a where

instance Commutative () where

instance (Commutative a, Commutative b) => Commutative ((a, b))
         where

instance (Commutative a, Commutative b, Commutative c) =>
         Commutative ((a, b, c))
         where

instance Commutative Conj where

