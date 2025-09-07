module Data.Bag.Prop.Conversion
  {-|
  -- * Conversion
  ; prop-morphism-mtoCounts
  ; prop-morphism-mfromCounts
  ; prop-mfromCounts-mtoCounts
  -} where

open import Haskell.Data.Bag.Quotient as Bag
open import Data.Bag.Def
open import Data.Bag.Counts
open import Data.Bag.Prop.Core

open import Haskell.Prelude
open import Haskell.Law.Eq
open import Haskell.Law.Equality
open import Haskell.Law.Ord

import      Data.Map as Map
open import Data.Map using (Map)
import      Data.Map.Prop.Extra as Map
import      Data.Monoid.Refinement as Monoid
import      Data.Monoid.Morphism as Monoid

{-# FOREIGN AGDA2HS
{-# OPTIONS_GHC -Wno-unused-top-binds #-}
#-}
dummyPropConversion : ⊤
dummyPropConversion = tt
{-# COMPILE AGDA2HS dummyPropConversion #-}

{-----------------------------------------------------------------------------
    Properties
    maps of Bags
------------------------------------------------------------------------------}
-- | @'foldMap' 'id'@ on an empty 'Map' gives the empty 'Bag'.
prop-Bag-fold-mempty
  : ∀ {k} ⦃ _ : Ord k ⦄
  → foldMap id (Map.empty {k}) ≡ mempty {Bag a}
--
prop-Bag-fold-mempty {a} {k = k}
  rewrite Map.prop-toAscList-empty {k = k} {a = Bag a}
  = refl

-- | @'foldMap' 'id'@ commutes with 'Bag'.
prop-Bag-fold-<>
  : ∀ {k} ⦃ _ : Ord k ⦄ (xs ys : Map k (Bag a))
  → foldMap id (Map.unionWith (_<>_) xs ys)
    ≡ foldMap id xs <> foldMap id ys
--
prop-Bag-fold-<> xs ys = Map.prop-fold-unionWith xs ys

{-----------------------------------------------------------------------------
    Properties
    Counts
------------------------------------------------------------------------------}
-- | 'Data.Bag.Counts.mtoCounts' is a monoid homomorphism.
prop-morphism-mtoCounts
  : ⦃ _ : Ord a ⦄ → Monoid.IsHomomorphism (mtoCounts {a})
--
prop-morphism-mtoCounts = prop-morphism-foldBag _

-- | 'Data.Bag.Counts.mfromCounts' is a monoid homomorphism.
prop-morphism-mfromCounts
  : ⦃ _ : Ord a ⦄ → Monoid.IsHomomorphism (mfromCounts {a})
--
prop-morphism-mfromCounts {a} .Monoid.homo-mempty =
  begin
    (foldMap id $ Map.mapWithKey (flip replicatePositiveNat) $ getCounts mempty)
  ≡⟨ cong (foldMap id) (Map.prop-mapWithKey-empty _) ⟩
    foldMap id (Map.empty {a})
  ≡⟨ prop-Bag-fold-mempty ⟩
    mempty
  ∎
prop-morphism-mfromCounts .Monoid.homo-<> xs ys =
  begin
    (foldMap id $ Map.mapWithKey (flip replicatePositiveNat) $ getCounts (xs <> ys))
  ≡⟨ cong (foldMap id) (Map.prop-mapWithKey-unionWith _ _ _ _ _ λ key x y → prop-replicatePositiveNat-<> x y key) ⟩
    (foldMap id $ Map.unionWith (_<>_)
      (Map.mapWithKey (flip replicatePositiveNat) (getCounts xs))
      (Map.mapWithKey (flip replicatePositiveNat) (getCounts ys))
    )
  ≡⟨ prop-Bag-fold-<> _ _ ⟩
    mfromCounts xs <> mfromCounts ys
  ∎

-- | 'mfromCounts' is a left-inverse of 'mtoCounts'.
prop-mfromCounts-mtoCounts
  : ∀ ⦃ _ : Ord a ⦄ ⦃ _ : IsLawfulEq a ⦄ (xs : Bag a)
  → mfromCounts (mtoCounts xs) ≡ xs
--
prop-mfromCounts-mtoCounts =
    prop-Bag-equality lhs rhs
      (Monoid.prop-morphism-∘ _ _ prop-morphism-mtoCounts prop-morphism-mfromCounts)
      (Monoid.prop-morphism-id)
      eq-singleton
  where 
    lhs = λ xs → mfromCounts (mtoCounts xs)
    rhs = λ xs → xs

    eq-singleton
      : ∀ x → lhs (Bag.singleton x) ≡ rhs (Bag.singleton x)
    eq-singleton x
      = begin
        (foldMap id $ Map.mapWithKey (flip replicatePositiveNat) $ Map.singleton x one)
      ≡⟨ cong (foldMap id) (Map.prop-mapWithKey-singleton (flip replicatePositiveNat) _ _) ⟩
        (foldMap id $ Map.singleton x (replicatePositiveNat one x))
      ≡⟨ cong (λ o → foldMap id (Map.singleton x o)) (prop-replicatePositiveNat-one _) ⟩
        foldMap id (Map.singleton x (Bag.singleton x))
      ≡⟨ Map.prop-fold-singleton _ _ ⟩
        Bag.singleton x
      ∎

instance
  iIsLawfulEqBag : ⦃ _ : Ord a ⦄ → ⦃ IsLawfulOrd a ⦄ → IsLawfulEq (Bag a)
  iIsLawfulEqBag .isEquality xs ys
    with xs == ys in eq
  ... | False = λ { refl → nequality (mtoCounts xs) _ eq refl }
  ... | True  =
      begin
        xs
      ≡⟨ sym (prop-mfromCounts-mtoCounts _) ⟩
        mfromCounts (mtoCounts xs)
      ≡⟨ cong mfromCounts (equality (mtoCounts xs) (mtoCounts ys) eq) ⟩
        mfromCounts (mtoCounts ys)
      ≡⟨ prop-mfromCounts-mtoCounts _ ⟩
        ys
      ∎
