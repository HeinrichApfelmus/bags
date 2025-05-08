module Data.Monoid.Extra where

import Prelude hiding (null, filter, map, concatMap)

newtype Conj = MkConj{getConj :: Bool}

instance Semigroup Conj where
    x <> y = MkConj (getConj x && getConj y)

instance Monoid Conj where
    mempty = MkConj True

