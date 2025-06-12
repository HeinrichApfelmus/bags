module Data.Monoid.Extra where

import Prelude hiding (null, filter, lookup, map, concatMap)

newtype Conj = MkConj{getConj :: Bool}

instance Semigroup Conj where
    x <> y = MkConj (getConj x && getConj y)

instance Monoid Conj where
    mempty = MkConj True

newtype Disj = MkDisj{getDisj :: Bool}

instance Semigroup Disj where
    MkDisj x <> MkDisj y = MkDisj (x || y)

instance Monoid Disj where
    mempty = MkDisj False

newtype Sum' a = MkSum{getSum' :: a}

instance (Num a) => Semigroup (Sum' a) where
    x <> y = MkSum (getSum' x + getSum' y)

instance (Num a) => Monoid (Sum' a) where
    mempty = MkSum 0

