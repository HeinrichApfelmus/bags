module Data.Monoid.Extra where

open import Haskell.Prelude

open import Haskell.Law.Equality
open import Haskell.Law.Monoid
open import Haskell.Law.Num

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

  isLawfulSemigroupConj : IsLawfulSemigroup Conj
  isLawfulSemigroupConj .associativity (MkConj False) y z = refl
  isLawfulSemigroupConj .associativity (MkConj True) y z = refl

  isLawfulMonoidConj : IsLawfulMonoid Conj
  isLawfulMonoidConj .rightIdentity (MkConj False) = refl
  isLawfulMonoidConj .rightIdentity (MkConj True) = refl
  isLawfulMonoidConj .leftIdentity (MkConj False) = refl
  isLawfulMonoidConj .leftIdentity (MkConj True) = refl
  isLawfulMonoidConj .concatenation [] = refl
  isLawfulMonoidConj .concatenation (x ∷ xs)
    rewrite (concatenation {{_}} {{isLawfulMonoidConj}} xs)
    = refl

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

postulate
  -- TODO: Fix 'Num' class to deal with '0'.
  -- Should follow from  +-idʳ ,
  --  but does not quite work due to fromInteger 0 .
  prop-Sum'-rightIdentity
    : ⦃ _ : Num a ⦄ → ⦃ IsLawfulNum a ⦄ → (x : Sum' a) → x <> mempty ≡ x
  prop-Sum'-leftIdentity
    : ⦃ _ : Num a ⦄ → ⦃ IsLawfulNum a ⦄ → (x : Sum' a) → mempty <> x ≡ x

instance
  isLawfulSemigroupSum'
    : ⦃ _ : Num a ⦄ → ⦃ IsLawfulNum a ⦄ → IsLawfulSemigroup (Sum' a)
  isLawfulSemigroupSum' .associativity (MkSum x) (MkSum y) (MkSum z) =
    cong MkSum (sym (+-assoc x y z))

  isLawfulMonoidSum'
    : ⦃ _ : Num a ⦄ → ⦃ IsLawfulNum a ⦄ → IsLawfulMonoid (Sum' a)
  isLawfulMonoidSum' .rightIdentity = prop-Sum'-rightIdentity
  isLawfulMonoidSum' .leftIdentity = prop-Sum'-leftIdentity
  isLawfulMonoidSum' .concatenation [] = refl
  isLawfulMonoidSum' .concatenation (x ∷ xs)
    rewrite (concatenation {{_}} {{isLawfulMonoidSum'}} xs)
    = refl

{-# COMPILE AGDA2HS iSemigroupSum' #-}
{-# COMPILE AGDA2HS iMonoidSum' #-}
