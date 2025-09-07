module Data.Monoid.Extra where

open import Haskell.Prelude

open import Haskell.Law.Equality
open import Haskell.Law.Monoid
open import Haskell.Law.Num

-------------------------------------------------------------------------------
-- Properties

-- | 'mconcat' is a monoid homomorphism.
prop-mconcat-++
  : ∀ ⦃ _ : Monoid a ⦄ ⦃ _ : IsLawfulMonoid a ⦄ 
    (xs ys : List a)
  → mconcat (xs ++ ys) ≡ mconcat xs <> mconcat ys
--
prop-mconcat-++ {a} [] ys
  rewrite concatenation ([] ++ ys)
  | concatenation {a} []
  | sym (concatenation ys)
  | leftIdentity (mconcat ys)
  = refl
prop-mconcat-++ (x ∷ xs) ys
  rewrite concatenation ((x ∷ xs) ++ ys)
  | concatenation (x ∷ xs)
  | sym (concatenation (xs ++ ys))
  | sym (concatenation xs)
  | prop-mconcat-++ xs ys
  | associativity x (mconcat xs) (mconcat ys)
  = refl

-------------------------------------------------------------------------------
--

-- | Boolean monoid under conjunction '(&&)'.
record Conj : Type where
  constructor MkConj
  no-eta-equality
  pattern
  field
    getConj : Bool

open Conj public

{-# COMPILE AGDA2HS Conj newtype #-}

instance
  iEqConj : Eq Conj
  iEqConj ._==_ x y = getConj x == getConj y

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

-------------------------------------------------------------------------------
--

-- | Boolean monoid under disjunction '(||)'.
record Disj : Type where
  constructor MkDisj
  no-eta-equality
  pattern
  field
    getDisj : Bool

open Disj public

{-# COMPILE AGDA2HS Disj newtype #-}

instance
  iEqDisj : Eq Disj
  iEqDisj ._==_ x y = getDisj x == getDisj y

  iSemigroupDisj : Semigroup Disj
  iSemigroupDisj ._<>_ (MkDisj x) (MkDisj y) = MkDisj (x || y)

  iDefaultMonoidDisj : DefaultMonoid Disj
  iDefaultMonoidDisj .DefaultMonoid.mempty = record{getDisj = False}

  iMonoidDisj : Monoid Disj
  iMonoidDisj = record{DefaultMonoid iDefaultMonoidDisj}

  isLawfulSemigroupDisj : IsLawfulSemigroup Disj
  isLawfulSemigroupDisj .associativity (MkDisj False) (MkDisj y) (MkDisj z) = refl
  isLawfulSemigroupDisj .associativity (MkDisj True ) (MkDisj y) (MkDisj z) = refl

  isLawfulMonoidDisj : IsLawfulMonoid Disj
  isLawfulMonoidDisj .rightIdentity (MkDisj False) = refl
  isLawfulMonoidDisj .rightIdentity (MkDisj True) = refl
  isLawfulMonoidDisj .leftIdentity (MkDisj False) = refl
  isLawfulMonoidDisj .leftIdentity (MkDisj True) = refl
  isLawfulMonoidDisj .concatenation [] = refl
  isLawfulMonoidDisj .concatenation (x ∷ xs)
    rewrite (concatenation {{_}} {{isLawfulMonoidDisj}} xs)
    = refl

{-# COMPILE AGDA2HS iSemigroupDisj #-}
{-# COMPILE AGDA2HS iMonoidDisj #-}

-------------------------------------------------------------------------------
--

-- | Monoid under addition.
record Sum' a : Type where
  constructor MkSum
  no-eta-equality
  pattern
  field
    getSum' : a

open Sum' public

{-# COMPILE AGDA2HS Sum' newtype #-}

instance
  iEqSum' : ⦃ Eq a ⦄ → Eq (Sum' a)
  iEqSum' ._==_ x y = getSum' x == getSum' y
  
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
