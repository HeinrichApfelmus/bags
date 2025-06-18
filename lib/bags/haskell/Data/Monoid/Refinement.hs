module Data.Monoid.Refinement 
    (
    Commutative,
    -- $prop-<>-sym
    
    )
    where

import Prelude hiding (null, filter, lookup, map, concatMap, replicate)
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

-- * Properties
{- $prop-<>-sym
#p:prop-<>-sym#

[prop-<>-sym]:
    For a 'Commutative' monoid,
    interchanging the two arguments of the monoid operation '(<>)'
    does not change the result.
    
    > @0 prop-<>-sym
    >   : ∀ ⦃ _ : Commutative a ⦄ (x y : a)
    >   → x <> y ≡ y <> x 
-}
