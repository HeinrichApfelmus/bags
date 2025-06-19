{-# OPTIONS --irrelevant-projections #-}

-- | Mapping from items to number of occurrences.
module Data.Bag.Counts
  {-|
  -- * Type
  ; Counts (..)

  -- ** Construction
  ; singleton

  -- ** Conversion
  ; natFromPositiveNat
  ; toCounts
  ; fromCounts
  -} where

open import Haskell.Prelude hiding (lookup; null)

open import Haskell.Data.Bag.Quotient using (Bag; foldBag)
import      Haskell.Data.Bag.Quotient as Bag
open import Data.Bag.Prop.Core
open import Haskell.Data.List.Extra

open import Data.Map using (Map)
import      Data.Map as Map
import      Data.Map.Prop.Extra as Map

open import Haskell.Prim using (monusNat)
open import Haskell.Law.Num
open import Haskell.Law.Equality
open import Haskell.Law.Extensionality
open import Haskell.Law.Maybe using (Just-injective)
import      Haskell.Law.Monoid as Monoid

open import Data.Monoid.Extra renaming (Sum' to Sum; getSum' to getSum)
import Data.Monoid.Morphism as Monoid
import Data.Monoid.Refinement as Monoid

{-----------------------------------------------------------------------------
    Count
    Type with invariant
------------------------------------------------------------------------------}
-- | A positive natural number.
data PositiveNat : Type where
  OnePlus : Nat → PositiveNat

open PositiveNat

{-# COMPILE AGDA2HS PositiveNat newtype #-}

one : PositiveNat
one = OnePlus 0

{-# COMPILE AGDA2HS one #-}

natFromPositiveNat : PositiveNat → Nat
natFromPositiveNat (OnePlus x) = x + 1

{-# COMPILE AGDA2HS natFromPositiveNat #-}

instance
  iSemigroupPositiveNat : Semigroup PositiveNat
  iSemigroupPositiveNat ._<>_ (OnePlus x) (OnePlus y) =
    OnePlus (x + y + 1)

{-# COMPILE AGDA2HS iSemigroupPositiveNat #-}

--
prop-natFromPositiveNat-<>
  : ∀ (x y : PositiveNat)
  → natFromPositiveNat (x <> y)
    ≡ natFromPositiveNat x + natFromPositiveNat y
--
prop-natFromPositiveNat-<> (OnePlus n) (OnePlus m)
  rewrite +-assoc n m 1
  | +-assoc n (m + 1) 1
  | +-assoc n 1 (m + 1)
  | +-comm m 1
  | +-comm (1 + m) 1
  = refl

instance  
  iIsLawfulSemigroup : Monoid.IsLawfulSemigroup PositiveNat
  iIsLawfulSemigroup .Monoid.associativity
    (OnePlus x) (OnePlus y) (OnePlus z)
    rewrite +-assoc x y 1
    | +-assoc x (y + 1) z
    | +-assoc y z 1
    | +-assoc y 1 z
    | +-comm  z 1
    = refl

--
prop-PositiveNat-<>-sym
  : ∀ (x y : PositiveNat) → x <> y ≡ y <> x
--
prop-PositiveNat-<>-sym (OnePlus x) (OnePlus y) rewrite +-comm x y = refl

-- | Construct a 'Bag' by replicating one item multiple times.
replicatePositiveNat : PositiveNat → a → Bag a
replicatePositiveNat n x =
  mconcat $ replicateNat (natFromPositiveNat n) (Bag.singleton x)

{-# COMPILE AGDA2HS replicatePositiveNat #-}

--
prop-replicatePositiveNat-<>
  : ∀ (m n : PositiveNat) (x : a)
  → replicatePositiveNat (m <> n) x
    ≡ replicatePositiveNat m x <> replicatePositiveNat n x
--
prop-replicatePositiveNat-<> m n x
  rewrite prop-natFromPositiveNat-<> m n
  | prop-replicateNat-+ (natFromPositiveNat m) (natFromPositiveNat n) (Bag.singleton x)
  = prop-mconcat-++ _ _

{-----------------------------------------------------------------------------
    Type
------------------------------------------------------------------------------}
-- | 'Counts' is a different representation for 'Bag',
-- where items are mapped to their number of occurrences.
--
record Counts a ⦃ @0 _ : Ord a ⦄ : Type where
  constructor MkCounts
  field
    getCounts : Map a PositiveNat

open Counts public

{-# COMPILE AGDA2HS Counts newtype #-}

-- | Two 'Counts' are equal if they are the same 'Map'.
prop-Counts-equality
  : ∀ ⦃ _ : Ord a ⦄ {xs ys : Counts a}
  → getCounts xs ≡ getCounts ys
  → xs ≡ ys
--
prop-Counts-equality refl = refl

{-----------------------------------------------------------------------------
    Operations
------------------------------------------------------------------------------}
-- | Construct a 'Counts' with a single item.
singleton : ∀ ⦃ _ : Ord a ⦄ → a → Counts a
singleton x = MkCounts (Map.singleton x one)

{-# COMPILE AGDA2HS singleton #-}

instance
  iSemigroupCounts : ∀ ⦃ _ : Ord a ⦄ → Semigroup (Counts a)
  iSemigroupCounts ._<>_ (MkCounts xs) (MkCounts ys) =
    MkCounts (Map.unionWith (_<>_) xs ys)

  iDefaultMonoidCounts : ∀ ⦃ _ : Ord a ⦄ → DefaultMonoid (Counts a)
  iDefaultMonoidCounts .DefaultMonoid.mempty = MkCounts Map.empty

  iMonoidCounts : ∀ ⦃ _ : Ord a ⦄ → Monoid (Counts a)
  iMonoidCounts = record{DefaultMonoid iDefaultMonoidCounts}

{-# COMPILE AGDA2HS iSemigroupCounts #-}
{-# COMPILE AGDA2HS iMonoidCounts #-}

-- | Union with the empty 'Counts' on the left is empty.
prop-Counts-<>-mempty-x
  : ∀ ⦃ _ : Ord a ⦄ (xs : Counts a)
  → mempty <> xs ≡ xs
--
prop-Counts-<>-mempty-x (MkCounts xs) =
  prop-Counts-equality Map.prop-unionWith-empty-x

-- | Union with the empty 'Counts' on the right is empty.
prop-Counts-<>-x-mempty
  : ∀ ⦃ _ : Ord a ⦄ (xs : Counts a)
  → xs <> mempty ≡ xs
--
prop-Counts-<>-x-mempty {a} (MkCounts xs) =
  prop-Counts-equality Map.prop-unionWith-x-empty

-- | Union of 'Counts' is associative
prop-Counts-<>-assoc
  : ∀ ⦃ _ : Ord a ⦄ (xs ys zs : Counts a)
  → (xs <> ys) <> zs ≡ xs <> (ys <> zs)
--
prop-Counts-<>-assoc {a} (MkCounts xs) (MkCounts ys) (MkCounts zs) =
    prop-Counts-equality (Map.prop-unionWith-assoc prop-f-assoc)
  where
    prop-f-assoc = λ x y z → sym (Monoid.associativity x y z)

instance
  iIsLawfulSemigroupCounts : ∀ ⦃ _ : Ord a ⦄ → Monoid.IsLawfulSemigroup (Counts a)
  iIsLawfulSemigroupCounts .Monoid.associativity =
    λ x y z → sym (prop-Counts-<>-assoc x y z)

  iIsLawfulMonoidCounts : ⦃ _ : Ord a ⦄ → Monoid.IsLawfulMonoid (Counts a)
  iIsLawfulMonoidCounts .Monoid.leftIdentity = prop-Counts-<>-mempty-x
  iIsLawfulMonoidCounts .Monoid.rightIdentity = prop-Counts-<>-x-mempty
  iIsLawfulMonoidCounts .Monoid.concatenation [] = refl
  iIsLawfulMonoidCounts .Monoid.concatenation (x ∷ xs)
    rewrite (Monoid.concatenation {{_}} {{iIsLawfulMonoidCounts}} xs)
    = refl

-- | A commutative function is equal to its flip.
lemma-sym→flip
  : ∀ {f : a → a → b} → (∀ x y → f x y ≡ f y x) → f ≡ flip f
--
lemma-sym→flip {f = f} cond-sym = ext₂ cond-sym

-- | Union of 'Counts' is commutative.
prop-Counts-<>-sym
  : ∀ ⦃ _ : Ord a ⦄ (xs ys : Counts a)
  → xs <> ys ≡ ys <> xs
--
prop-Counts-<>-sym (MkCounts xs) (MkCounts ys) = prop-Counts-equality $
  begin
    Map.unionWith (_<>_) xs ys
  ≡⟨ Map.prop-unionWith-sym ⟩
    Map.unionWith (flip (_<>_)) ys xs
  ≡⟨ sym (cong (λ o → Map.unionWith o ys xs) (lemma-sym→flip prop-PositiveNat-<>-sym)) ⟩
    Map.unionWith (_<>_) ys xs
  ∎

instance
  iCommutativeCounts : ∀ ⦃ _ : Ord a ⦄ → Monoid.Commutative (Counts a)
  iCommutativeCounts .Monoid.monoid = iMonoidCounts
  iCommutativeCounts .Monoid.commutative = prop-Counts-<>-sym

{-# COMPILE AGDA2HS iCommutativeCounts #-}

{-----------------------------------------------------------------------------
    Operations
    Bag
------------------------------------------------------------------------------}
mtoCounts : ∀ ⦃ _ : Ord a ⦄ → Bag a → Counts a
mtoCounts = foldBag (λ x → singleton x)

{-# COMPILE AGDA2HS mtoCounts #-}

-- | Convert a 'Bag' to a mapping from items to their number of occurrences.
toCounts : ⦃ Ord a ⦄ → Bag a → Map.Map a Nat
toCounts = fmap natFromPositiveNat ∘ getCounts ∘ mtoCounts

{-# COMPILE AGDA2HS toCounts #-}

replicateBag : Nat → a → Bag a
replicateBag n x = mconcat $ replicateNat n (Bag.singleton x)

{-# COMPILE AGDA2HS replicateBag #-}

-- | Convert a map of items and their number of occurrences to a 'Bag'.
fromCounts : ⦃ Ord a ⦄ → Map.Map a Nat → Bag a
fromCounts = foldMap id ∘ Map.mapWithKey (flip replicateBag)

{-# COMPILE AGDA2HS fromCounts #-}

mfromCounts : ⦃ _ : Ord a ⦄ → Counts a → Bag a
mfromCounts =
  foldMap id ∘ Map.mapWithKey (flip replicatePositiveNat) ∘ getCounts

{-# COMPILE AGDA2HS mfromCounts #-}
