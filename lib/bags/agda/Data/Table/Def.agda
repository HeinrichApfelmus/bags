{-# OPTIONS --irrelevant-projections #-}

-- | Indexed Tables and operations on them.
module Data.Table.Def
  {-|
  -- * Type
  ; Table
  ; prop-Table-equality

  -- * Operations
  -- ** Query
  ; lookup
  ; getMap
  ; elements

  -- ** Construction
  ; singleton
  ; indexBy
  ; fromMap
  ; fromSingletonsMap

  -- ** Combine
  ; merge
  -} where

open import Haskell.Prelude hiding (lookup; null)

open import Data.Bag using (Bag; null; foldBag)
import      Data.Bag as Bag
open import Data.Map using (Map)
import      Data.Map as Map
import      Data.Map.Prop.Extra as Map

open import Haskell.Law.Eq
open import Haskell.Law.Equality
open import Haskell.Law.Extensionality
open import Haskell.Law.Maybe using (Just-injective)
import      Haskell.Law.Monoid as Monoid

import Data.Monoid.Morphism as Monoid
import Data.Monoid.Refinement as Monoid

------------------------------------------------------------------------------
-- Move out: Elimination of irrelevant ⊥
private
  ⊥-elim-irr : ∀ {ℓ} {Whatever : Type ℓ} → .⊥ → Whatever
  ⊥-elim-irr ()

------------------------------------------------------------------------------
-- Move out: Helper function on "Data.Maybe"

isJust : Maybe a → Bool
isJust Nothing = False
isJust (Just _) = True

{-----------------------------------------------------------------------------
    Raw operations
------------------------------------------------------------------------------}
mergeRaw
  : ∀ {k} ⦃ _ : Ord k ⦄
  → Map k (Bag a) → Map k (Bag b) → Map k (Bag (a × b))
mergeRaw = Map.intersectionWith Bag.cartesianProduct

{-# COMPILE AGDA2HS mergeRaw #-}

{-----------------------------------------------------------------------------
    Invariant
------------------------------------------------------------------------------}
-- | Invariant satisfied by the map inside 'Table':
--
-- The 'Map' is normalized to not contain explicit 'mempty' items.
Is-lookup-not-null : ∀ {k} ⦃ _ : Ord k ⦄ → Map k (Bag a) → Type
Is-lookup-not-null {k = k} = λ xs →
    ∀ (key : k) → (fmap null (Map.lookup key xs) == Just True) ≡ False

--
prop-invariant-mempty
  : ∀ {a k} ⦃ _ : Ord k ⦄ → Is-lookup-not-null {a} {k} Map.empty
--
prop-invariant-mempty {a} key
  rewrite Map.prop-lookup-empty {_} {Bag a} key
  = refl

--
prop-invariant-singleton
  : ∀ {a k} ⦃ _ : Ord k ⦄ {key : k} {x : a}
  → Is-lookup-not-null {a} {k} (Map.singleton key (Bag.singleton x))
--
prop-invariant-singleton {a} {k} {key} {x} key'
  rewrite Map.prop-lookup-singleton {_} {Bag a} key' key (Bag.singleton x)
  with (key' == key)
... | False = refl
... | True  = refl

--
prop-invariant-unionWith
  : ∀ {k} ⦃ _ : Ord k ⦄ {xs ys : Map k (Bag a)}
  → Is-lookup-not-null xs
  → Is-lookup-not-null ys
  → Is-lookup-not-null (Map.unionWith (_<>_) xs ys)
--
prop-invariant-unionWith {xs = xs} {ys = ys} cond-xs cond-ys key
  rewrite Map.prop-lookup-unionWith key (_<>_) xs ys
  with cx ← cond-xs key
  with cy ← cond-ys key
  with Map.lookup key xs | Map.lookup key ys
... | Nothing | Nothing = refl
... | Nothing | Just y  = cy
... | Just x  | Nothing = cx
... | Just x  | Just y
    with null x
...     | False = refl
        -- This case holds for Bags, but not for general monoids,
        -- where two items can cancel each other.

--
prop-invariant-mergeRaw
  : ∀ {k} ⦃ _ : Ord k ⦄ {xs : Map k (Bag a)} {ys : Map k (Bag b)}
  → Is-lookup-not-null xs
  → Is-lookup-not-null ys
  → Is-lookup-not-null (mergeRaw xs ys)
--
prop-invariant-mergeRaw {xs = xs} {ys = ys} cond-xs cond-ys key
  rewrite Map.prop-lookup-intersectionWith key xs ys Bag.cartesianProduct
  with cx ← cond-xs key
  with cy ← cond-ys key
  with Map.lookup key xs | Map.lookup key ys
... | Nothing | Nothing = refl
... | Nothing | Just y  = refl
... | Just x  | Nothing = refl
... | Just x  | Just y  
    rewrite Bag.prop-null-cartesianProduct x y
    with null x
...   | True  = cx
...   | False = cy

--
prop-invariant-null
  : ∀ {a k} ⦃ _ : Ord k ⦄ (key : k) (xs : Bag a)
  → null xs ≡ False
  → Is-lookup-not-null {a} {k} (Map.singleton key xs)
--
prop-invariant-null {a} {k} key xs cond key2
  rewrite Map.prop-lookup-insert key2 key xs Map.empty
  rewrite Map.prop-lookup-empty {k = k} {a = Bag a} key2
  with key2 == key in eq
... | False = refl
... | True  rewrite cond = refl

{-----------------------------------------------------------------------------
    Data type
------------------------------------------------------------------------------}
-- | A 'Table' is a finite map from keys (indices) to finite 'Bag's
-- of values. Think @'Table' k a ~ 'Map' k ('Bag' a)@.
--
-- This type can also be viewed as a 'Bag' where elements have been grouped
-- by keys.
record Table k a ⦃ @0 _ : Ord k ⦄ : Type where
  constructor MkTable
  field
    getTable : Map k (Bag a)
    @0 . invariant-lookup : Is-lookup-not-null getTable

open Table public

{-# COMPILE AGDA2HS Table newtype #-}

-- | Get the 'Data.Map.Map' that stores the mapping from keys to 'Bag's.
getMap : ∀ {k} ⦃ _ : Ord k ⦄ → Table k a → Map k (Bag a)
getMap = getTable

{-# COMPILE AGDA2HS getMap #-}

-- | Two Tables are equal if they contain the same 'Map'.
prop-Table-equality
  : ∀ {k} ⦃ _ : Ord k ⦄ {xs ys : Table k a}
  → getMap xs ≡ getMap ys
  → xs ≡ ys
--
prop-Table-equality refl = refl

{-----------------------------------------------------------------------------
    Operations
------------------------------------------------------------------------------}
-- Helper function for 'lookup'.
toBag : Maybe (Bag a) → Bag a
toBag Nothing  = mempty
toBag (Just x) = x

{-# COMPILE AGDA2HS toBag #-}

-- | Look up a key in a 'Table'.
lookup : ∀ {k} ⦃ _ : Ord k ⦄ → k → Table k a → Bag a
lookup = λ key → toBag ∘ Map.lookup key ∘ getTable

{-# COMPILE AGDA2HS lookup #-}

-- | Construct a 'Table' with a single item.
singleton : ∀ {k} ⦃ _ : Ord k ⦄ → k → a → Table k a
singleton key x =
  MkTable (Map.singleton key (Bag.singleton x)) prop-invariant-singleton

{-# COMPILE AGDA2HS singleton #-}

instance
  iSemigroupTable : ∀ {k} ⦃ _ : Ord k ⦄ → Semigroup (Table k a)
  iSemigroupTable ._<>_ (MkTable xs inv-x) (MkTable ys inv-y) =
    MkTable (Map.unionWith (_<>_) xs ys) (prop-invariant-unionWith inv-x inv-y)

  iDefaultMonoidTable : ∀ {k} ⦃ _ : Ord k ⦄ → DefaultMonoid (Table k a)
  iDefaultMonoidTable .DefaultMonoid.mempty =
    MkTable Map.empty prop-invariant-mempty

  iMonoidTable : ∀ {k} ⦃ _ : Ord k ⦄ → Monoid (Table k a)
  iMonoidTable = record{DefaultMonoid iDefaultMonoidTable}

{-# COMPILE AGDA2HS iSemigroupTable #-}
{-# COMPILE AGDA2HS iMonoidTable #-}

-- | Union with the empty 'Table' on the left is empty.
prop-Table-<>-mempty-x
  : ∀ {k} ⦃ _ : Ord k ⦄ (xs : Table k a)
  → mempty <> xs ≡ xs
--
prop-Table-<>-mempty-x {a} (MkTable xs inv-x) =
  prop-Table-equality Map.prop-unionWith-empty-x

-- | Union with the empty 'Table' on the right is empty.
prop-Table-<>-x-mempty
  : ∀ {k} ⦃ _ : Ord k ⦄ (xs : Table k a)
  → xs <> mempty ≡ xs
--
prop-Table-<>-x-mempty {a} (MkTable xs inv-x) =
  prop-Table-equality Map.prop-unionWith-x-empty

-- | Union of 'Table' is associative
prop-Table-<>-assoc
  : ∀ {k} ⦃ _ : Ord k ⦄ (xs ys zs : Table k a)
  → (xs <> ys) <> zs ≡ xs <> (ys <> zs)
--
prop-Table-<>-assoc {a} (MkTable xs inv-x) (MkTable ys inv-y) (MkTable zs inv-z) =
    prop-Table-equality (Map.prop-unionWith-assoc prop-f-assoc)
  where
    prop-f-assoc = λ x y z → sym (Monoid.associativity x y z)

instance
  isLawfulSemigroupTable : ∀ {k} ⦃ _ : Ord k ⦄ → Monoid.IsLawfulSemigroup (Table k a)
  isLawfulSemigroupTable .Monoid.associativity =
    λ x y z → sym (prop-Table-<>-assoc x y z)

  isLawfulMonoidTable : ∀ {k} ⦃ _ : Ord k ⦄ → Monoid.IsLawfulMonoid (Table k a)
  isLawfulMonoidTable .Monoid.leftIdentity = prop-Table-<>-mempty-x
  isLawfulMonoidTable .Monoid.rightIdentity = prop-Table-<>-x-mempty
  isLawfulMonoidTable .Monoid.concatenation [] = refl
  isLawfulMonoidTable .Monoid.concatenation (x ∷ xs)
    rewrite (Monoid.concatenation {{_}} {{isLawfulMonoidTable}} xs)
    = refl

-- | The semigroup operation on 'Table' is commutative.
@0 prop-Table-<>-sym
  : ∀ {k} ⦃ _ : Ord k ⦄ (xs ys : Table k a)
  → xs <> ys ≡ ys <> xs
--
prop-Table-<>-sym {a} (MkTable xs inv-x) (MkTable ys inv-y)
  = prop-Table-equality eq-Table
  where
    eq-Table : Map.unionWith (_<>_) xs ys ≡ Map.unionWith (_<>_) ys xs
    eq-Table
      rewrite Map.prop-unionWith-sym {f = _<>_} {xs} {ys}
      = cong (λ o → Map.unionWith o ys xs) (sym (ext₂ Monoid.commutative))

instance
  iCommutativeTable : ∀ {k} ⦃ _ : Ord k ⦄ → Monoid.Commutative (Table k a)
  iCommutativeTable .Monoid.monoid = iMonoidTable
  iCommutativeTable .Monoid.commutative = prop-Table-<>-sym

{-# COMPILE AGDA2HS iCommutativeTable #-}

-- | Helper function: Construct a 'Table' from a 'Bag' for a single key.
fromKeyAndBag : ∀ {k} ⦃ _ : Ord k ⦄ → k → Bag a → Table k a
fromKeyAndBag key xs =
  if null xs
  then mempty
  else λ ⦃ neq ⦄ → MkTable (Map.singleton key xs) (prop-invariant-null key xs neq)

{-# COMPILE AGDA2HS fromKeyAndBag #-}

-- | Construct a 'Table' from a 'Map' from keys to 'Bag'.
fromMap : ∀ {k} ⦃ _ : Ord k ⦄ → Map k (Bag a) → Table k a
fromMap =
  mconcat ∘ fmap (λ { (key , xs) → fromKeyAndBag key xs }) ∘ Map.toAscList

{-# COMPILE AGDA2HS fromMap #-}

-- | Construct a 'Table' from a 'Map' from keys to items.
fromSingletonsMap : ∀ {k} ⦃ _ : Ord k ⦄ → Map k a → Table k a
fromSingletonsMap = fromMap ∘ Map.map Bag.singleton

{-# COMPILE AGDA2HS fromSingletonsMap #-}

-- | Index the items in a 'Bag' by a function.
indexBy : ∀ {k} ⦃ _ : Ord k ⦄ → Bag a → (a → k) → Table k a
indexBy xs f = foldBag (λ x → singleton (f x) x) xs

{-# COMPILE AGDA2HS indexBy #-}

-- | Forget the grouping of items by key.
elements : ∀ {k} ⦃ _ : Ord k ⦄ → Table k a → Bag a
elements = foldMap id ∘ getTable

{-# COMPILE AGDA2HS elements #-}

-- | For each key, construct the 'Data.Bag.cartesianProduct' of 'Bag's.
merge : ∀ {k} ⦃ _ : Ord k ⦄ → Table k a → Table k b → Table k (a × b)
merge xs ys = record
  { getTable = mergeRaw (getTable xs) (getTable ys)
  ; invariant-lookup =
    prop-invariant-mergeRaw (invariant-lookup xs) (invariant-lookup ys)
  }

{-# COMPILE AGDA2HS merge #-}

{-----------------------------------------------------------------------------
    Properties
------------------------------------------------------------------------------}
-- Helper property that uses the invariant.
@0 prop-lookup≡mempty→Nothing
  : ∀ {k} ⦃ _ : Ord k ⦄ (key : k) (xs : Table k a)
  → (lookup key xs ≡ mempty)
  → Map.lookup key (getTable xs) ≡ Nothing
--
prop-lookup≡mempty→Nothing key xs cond
  with Map.lookup key (getTable xs) in eq
... | Nothing = refl
... | Just x  =
      ⊥-elim-irr (lemma (invariant-lookup xs) (cong isJust eq))
  where
    -- The invariant is marked irrelevant.
    -- In order to drop the irrelevance, we have to do a proof
    -- by contradiction.
    . lemma
      : Is-lookup-not-null (getTable xs)
      → isJust (Map.lookup key (getTable xs)) ≡ True
      → ⊥
    lemma invariant contr
      -- making the invariant participate in rewrite
      -- requires lemma to be irrelevant.
      with i ← invariant key
      with Map.lookup key (getTable xs) in eq-y
    ... | Nothing = case contr of λ ()
    ... | Just y
        rewrite Just-injective eq
        rewrite cond
        = case i of λ ()

-- | Tables that have the same 'lookup' function are equal.
@0 prop-lookup→equality
  : ∀ {k} ⦃ _ : Ord k ⦄ (xs ys : Table k a)
  → (∀ key → lookup key xs ≡ lookup key ys)
  → xs ≡ ys
--
prop-lookup→equality xs ys cond =
    prop-Table-equality (Map.prop-equality lemma)
  where
    lemma : ∀ key
      → Map.lookup key (getTable xs)
        ≡ Map.lookup key (getTable ys)
    lemma key
      with cond' ← cond key
      with lookup-x ← prop-lookup≡mempty→Nothing key xs
      with lookup-y ← prop-lookup≡mempty→Nothing key ys
      with Map.lookup key (getTable xs) | Map.lookup key (getTable ys)
    ... | Nothing | Nothing = refl
    ... | Nothing | Just y  = sym (lookup-y (sym cond'))
    ... | Just x  | Nothing = lookup-x cond'
    ... | Just x  | Just y  = cong Just cond'
