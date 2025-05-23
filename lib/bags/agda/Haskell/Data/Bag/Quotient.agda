-- | Type and operations, after taking the quotient.
--
-- * We use an export list in Haskell to make the type abstract.
-- * We do not prove that the operations preserve the equivalence
--   — we only postulate this fact here.
--
module Haskell.Data.Bag.Quotient where

open import Agda.Builtin.Equality.Rewrite

open import Haskell.Prelude

open import Haskell.Law.Eq
open import Haskell.Law.Equality
open import Haskell.Law.Extensionality
open import Haskell.Law.Function
open import Haskell.Law.Monoid

import Data.Monoid.Morphism as Monoid
import Data.Monoid.Refinement as Monoid

{-----------------------------------------------------------------------------
    Type and Operations
------------------------------------------------------------------------------}
postulate
  Bag : Type → Type

  singleton : a → Bag a

  -- Bags are a monoid.
  instance
    iMonoidBag : Monoid (Bag a)

  -- Any map to a commutative monoid factors through 'Bag'
  foldBag
    : ∀ ⦃ _ : Monoid.Commutative b ⦄
    → (a → b) → (Bag a → b)

instance
  iSemigroupBag : Semigroup (Bag a)
  iSemigroupBag = iMonoidBag .Monoid.super

{-----------------------------------------------------------------------------
    Properties
------------------------------------------------------------------------------}
postulate
  instance
    iLawfulMonoidBag : IsLawfulMonoid (Bag a)

  -- Bags are a commutative monoid.
  prop-<>-sym : Commutative (_<>_ {Bag a})

  -- Universal properties of 'foldBag'
  -- 'f' factors through 'singleton'.
  prop-foldBag-singleton
    : ∀ ⦃ _ : Monoid.Commutative b ⦄ (f : a → b) (x : a)
    → foldBag f (singleton x) ≡ f x

  -- Universal property, 'foldBag' is a homomorphism.
  prop-foldBag-mempty
    : ∀ ⦃ _ : Monoid.Commutative b ⦄ (f : a → b)
    → foldBag f mempty ≡ mempty

  prop-foldBag-<>
    : ∀ ⦃ _ : Monoid.Commutative b ⦄ (f : a → b) (xs ys : Bag a)
    → foldBag f (xs <> ys) ≡ foldBag f xs <> foldBag f ys

  -- Universal property, uniqueness
  prop-foldBag-unique
    : ∀ ⦃ _ : Monoid.Commutative b ⦄ ⦃ _ : IsLawfulMonoid b ⦄ (g : Bag a → b)
    → @0 Monoid.IsHomomorphism g
    → ∀ (xs : Bag a) → foldBag (g ∘ singleton) xs ≡ g xs

instance
  iLawfulSemigroupBag : IsLawfulSemigroup (Bag a)
  iLawfulSemigroupBag = iLawfulMonoidBag .super

  iMonoidCommutativeBag : Monoid.Commutative (Bag a)
  iMonoidCommutativeBag .Monoid.monoid = iMonoidBag
  iMonoidCommutativeBag .Monoid.commutative = prop-<>-sym

{-----------------------------------------------------------------------------
    Rewrite Rules
------------------------------------------------------------------------------}
{- [Rewrite foldBag]

In order to make the 'Bag' quotient type easy to use,
we introduce rewrite rules that allow us to compute 'foldBag'.
-}
{-# REWRITE prop-foldBag-singleton #-}
{-# REWRITE prop-foldBag-mempty #-}
{-# REWRITE prop-foldBag-<> #-}
