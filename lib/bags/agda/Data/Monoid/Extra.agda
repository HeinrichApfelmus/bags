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
