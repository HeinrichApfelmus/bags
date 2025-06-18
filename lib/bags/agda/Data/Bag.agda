module Data.Bag
  {-|
  -- * Type and Definitional Properties
  ; Bag
  ; singleton
  ; foldBag
    ; prop-morphism-foldBag
    ; prop-foldBag-singleton
    ; prop-foldBag-unique

  -- * Operations
  -- ** Query
  ; null
  ; mnull
  ; size
  ; msize
  ; count
  ; member
  ; mmember

  -- ** Construction
  ; fromMaybe
  ; fromList
  ; replicate

  -- ** Deletion
  ; deleteOne
    ; prop-deleteOne-member-True
    ; prop-deleteOne-member-False

  -- ** Combine
  ; union
  ; cartesianProduct
  ; equijoin

  -- ** Traversal
  ; map
  ; concatMap
  ; filter

  -- ** Conversion
  ; toCounts
  ; fromCounts

  -- * Properties
  ; module Data.Bag.Prop.Core
  ; module Data.Bag.Prop.Deletion
  ; module Data.Bag.Prop.Operations
  -} where

{-# FOREIGN AGDA2HS
  {-# OPTIONS_GHC -Wno-unused-imports -Wno-dodgy-exports #-}
  import Data.Bag.Def
  import Data.Bag.Quotient
  import Data.Bag.Found (deleteOne)
  import Data.Bag.Prop.Core
  import Data.Bag.Prop.Deletion
  import Data.Bag.Prop.Operations
#-}

import      Haskell.Data.Bag.Quotient
open import Haskell.Data.Bag.Quotient   public hiding
  ( prop-foldBag-singleton
  ; prop-foldBag-unique
  )
open import Data.Bag.Def                public
open import Data.Bag.Counts             using (toCounts; fromCounts)
open import Data.Bag.Found              public using (deleteOne)
import      Data.Bag.Prop.Core
open import Data.Bag.Prop.Core          public hiding
  ( prop-morphism-foldBag )
open import Data.Bag.Prop.Operations    public

open import Haskell.Prelude
open import Haskell.Law.Eq
open import Haskell.Law.Monoid

import Data.Map as Map
import Data.Monoid.Refinement as Monoid
import Data.Monoid.Morphism as Monoid

{-# FOREIGN AGDA2HS
  import Data.Bag.Counts (toCounts, fromCounts)
#-}

{-----------------------------------------------------------------------------
    Properties
    definitional
------------------------------------------------------------------------------}
-- | Universal property: 'foldBag' is a homomorphism
-- (see "Data.Monoid.Morphism#g:1") of 'Monoid'.
prop-morphism-foldBag
  : ∀ ⦃ _ : Monoid.Commutative b ⦄ (f : a → b)
  → Monoid.IsHomomorphism (foldBag f)
--
prop-morphism-foldBag =
    Data.Bag.Prop.Core.prop-morphism-foldBag

-- | Universal property: Every 'Monoid' homomorphism
-- (see "Data.Monoid.Morphism#g:1")
-- factors through 'foldBag' and 'singleton'.
prop-foldBag-singleton
  : ∀ ⦃ _ : Monoid.Commutative b ⦄ (f : a → b) (x : a)
  → foldBag f (singleton x) ≡ f x
--
prop-foldBag-singleton =
  Haskell.Data.Bag.Quotient.prop-foldBag-singleton

-- | Universal property: 'foldBag' is the unique homomorphism
-- (see "Data.Monoid.Morphism#g:1").
prop-foldBag-unique
  : ∀ ⦃ _ : Monoid.Commutative b ⦄ ⦃ _ : IsLawfulMonoid b ⦄ (g : Bag a → b)
  → @0 Monoid.IsHomomorphism g
  → ∀ (xs : Bag a) → foldBag (g ∘ singleton) xs ≡ g xs
--
prop-foldBag-unique =
  Haskell.Data.Bag.Quotient.prop-foldBag-unique
