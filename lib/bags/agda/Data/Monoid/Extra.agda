module Data.Monoid.Extra where

open import Haskell.Prelude

-- Boolean monoid under conjunction '(&&)'.
record Conj : Type where
  constructor MkConj
  field
    getConj : Bool

open Conj public

{-# COMPILE AGDA2HS Conj newtype #-}

instance
  iSemigroupConj : Semigroup Conj
  iSemigroupConj ._<>_ x y = record{getConj = getConj x && getConj y}

  iDefaultMonoidConj : DefaultMonoid Conj
  iDefaultMonoidConj .DefaultMonoid.mempty = record{getConj = True}

  iMonoidConj : Monoid Conj
  iMonoidConj = record{DefaultMonoid iDefaultMonoidConj}

{-# COMPILE AGDA2HS iSemigroupConj #-}
{-# COMPILE AGDA2HS iMonoidConj #-}

-- Monoid under addition.
record Sum' a : Type where
  constructor MkSum
  field
    getSum' : a

open Sum' public

{-# COMPILE AGDA2HS Sum' newtype #-}

instance
  iSemigroupSum' : ⦃ Num a ⦄ → Semigroup (Sum' a)
  iSemigroupSum' ._<>_ x y = record{getSum' = getSum' x + getSum' y}

  iDefaultMonoidSum' : ⦃ Num a ⦄ → DefaultMonoid (Sum' a)
  iDefaultMonoidSum' .DefaultMonoid.mempty = record{getSum' = 0}

  iMonoidSum' : ⦃ Num a ⦄ → Monoid (Sum' a)
  iMonoidSum' = record{DefaultMonoid iDefaultMonoidSum'}

{-# COMPILE AGDA2HS iSemigroupSum' #-}
{-# COMPILE AGDA2HS iMonoidSum' #-}
