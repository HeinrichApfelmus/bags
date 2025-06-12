-- | Monoid for finding an element inside a 'Bag'.
module Data.Bag.Found where

open import Haskell.Prelude
open import Haskell.Data.Maybe

open import Haskell.Law.Bool
open import Haskell.Law.Eq
open import Haskell.Law.Equality
open import Haskell.Law.Monoid

open import Haskell.Data.Bag.Quotient
open import Data.Bag.Def
open import Data.Bag.Prop
open import Data.Bag.Quotient.Prop

import Data.Monoid.Extra as Monoid
import Data.Monoid.Morphism as Monoid
import Data.Monoid.Refinement as Monoid

------------------------------------------------------------------------------
-- Move out: Elimination of irrelevant ⊥

private
  ⊥-elim-irr : ∀ {ℓ} {Whatever : Type ℓ} → .⊥ → Whatever
  ⊥-elim-irr ()

{-----------------------------------------------------------------------------
    Type
------------------------------------------------------------------------------}
-- | Find a known item in a 'Bag',
-- and also return a 'Bag' without that item.
--
-- The item is part of the type, but erased.
record Found (a : Type) (@0 x : a) : Type where
  constructor MkFound
  field
    found : Maybe a
    rest  : Bag a

    @0 . invariant : ∀ y → found ≡ Just y → x ≡ y

open Found public

{-# COMPILE AGDA2HS Found #-}

{-----------------------------------------------------------------------------
    Equality
------------------------------------------------------------------------------}
-- | Basic lemma about two 'Found' being equal.
equality-Found
  : ∀ {@0 z : a} (x y : Found a z)
  → found x ≡ found y → rest x ≡ rest y → x ≡ y
--
equality-Found x y refl refl = refl

-- | Use a decidable equality to get 
recompute-Eq : ∀ ⦃ _ : Eq a ⦄ ⦃ _ : IsLawfulEq a ⦄ (x y : a)
  → .(x ≡ y) → x ≡ y
--
recompute-Eq x y eq-irr
  with x == y in eq
... | False = ⊥-elim-irr (nequality x y eq eq-irr)
... | True  = equality x y eq

-- | Advanced lemma about two 'Found' being equal.
@0 equality-Found-1
  : ∀ {@0 z : a} ⦃ _ : Eq a ⦄ ⦃ _ : IsLawfulEq a ⦄
  → (x y : Found a z)
  → isJust (found x) ≡ isJust (found y)
  → (found x ≡ found y → rest x ≡ rest y)
  → x ≡ y
--
equality-Found-1 (MkFound mx rx ix) (MkFound my ry iy) eq eq-rest
  with mx | my
... | Nothing | Nothing rewrite eq-rest refl = refl
... | Nothing | Just y  = case eq of λ ()
... | Just x  | Nothing = case eq of λ ()
... | Just x  | Just y  = equality-Found _ _ Just-x≡y (eq-rest Just-x≡y)
  where
    x≡y : x ≡ y
    x≡y = recompute-Eq x y (trans (sym (ix x refl)) (iy y refl))

    Just-x≡y = cong Just x≡y

{-----------------------------------------------------------------------------
    Operations
------------------------------------------------------------------------------}
emptyFound : ∀ {@0 x : a} → Found a x
emptyFound = MkFound Nothing mempty (λ y ())

{-# COMPILE AGDA2HS emptyFound #-}

unionFound : ∀ {@0 x : a} → Found a x → Found a x → Found a x
unionFound (MkFound Nothing r1 i1) (MkFound Nothing r2 _) =
  MkFound Nothing (r1 <> r2) i1
unionFound (MkFound Nothing r1 _) (MkFound (Just y2) r2 i2) =
  MkFound (Just y2) (r1 <> r2) i2
unionFound (MkFound (Just y1) r1 i1) (MkFound Nothing r2 _) =
  MkFound (Just y1) (r1 <> r2) i1
unionFound (MkFound (Just y1) r1 i1) (MkFound (Just y2) r2 _) =
  MkFound (Just y1) (r1 <> singleton y2 <> r2) i1

{-# COMPILE AGDA2HS unionFound #-}

instance
  iSemigroupFound : {@0 x : a} → Semigroup (Found a x)
  iSemigroupFound ._<>_ = unionFound

  iDefaultMonoid : {@0 x : a} → DefaultMonoid (Found a x)
  iDefaultMonoid .DefaultMonoid.mempty = emptyFound

  iMonoidFound : {@0 x : a} → Monoid (Found a x)
  iMonoidFound = record {DefaultMonoid iDefaultMonoid}

{-# COMPILE AGDA2HS iSemigroupFound #-}
{-# COMPILE AGDA2HS iMonoidFound #-}

-- | We have found the item.
here : ∀ {@0 z : a} → (x : a) → @0 (x ≡ z) → Found a z
here x refl = MkFound (Just x) mempty (λ y → λ { refl → refl })

-- | We have an item, but the item that we are looking for is elsewhere.
elsewhere : ∀ {@0 z : a} (y : a) → Found a z
elsewhere y = MkFound Nothing (singleton y) (λ y ())

{-# COMPILE AGDA2HS here #-}
{-# COMPILE AGDA2HS elsewhere #-}

-- | Put the item back into the 'Bag'.
putBack : ∀ {@0 z : a} → Found a z → Bag a
putBack (MkFound Nothing  xs _) = xs
putBack (MkFound (Just x) xs _) = singleton x <> xs

{-# COMPILE AGDA2HS putBack #-}

{-----------------------------------------------------------------------------
    Properties
------------------------------------------------------------------------------}
instance
  iIsLawfulSemigroupFound : ∀ {@0 x : a} → IsLawfulSemigroup (Found a x)
  iIsLawfulSemigroupFound .associativity
      (MkFound mx rx _) (MkFound my ry _) (MkFound mz rz _)
    with mx | my | mz
  ... | Nothing | Nothing | Nothing rewrite associativity rx ry rz = refl
  ... | Nothing | Nothing | Just z  rewrite associativity rx ry rz = refl
  ... | Nothing | Just y  | Nothing rewrite associativity rx ry rz = refl
  ... | Nothing | Just y  | Just z
    rewrite associativity rx ry (singleton z <> rz) = refl
  ... | Just x  | Nothing | Nothing rewrite associativity rx ry rz = refl
  ... | Just x  | Nothing | Just z
    rewrite prop-<>-sym (singleton z) rz
    | prop-<>-sym (singleton z) (ry <> rz)
    | sym (associativity ry rz (singleton z))
    | sym (associativity rx ry (rz <> singleton z))
    = refl
  ... | Just x  | Just y  | Nothing
    rewrite sym (associativity rx (singleton y <> ry) rz)
    | sym (associativity (singleton y) ry rz)
    = refl
  ... | Just x  | Just y  | Just z
    rewrite sym (associativity (singleton y) ry (singleton z <> rz))
    | sym (associativity rx (singleton y) ry)
    | sym (associativity rx (singleton y <> ry) (singleton z <> rz))
    | sym (associativity (singleton y) ry (singleton z <> rz))
    = refl

  iIsLawfulMonoidFound : ∀ {@0 x : a} → IsLawfulMonoid (Found a x)
  iIsLawfulMonoidFound .rightIdentity (MkFound mx rx _)
    with mx
  ... | Nothing rewrite rightIdentity rx = refl
  ... | Just x  rewrite rightIdentity rx = refl
  iIsLawfulMonoidFound .leftIdentity (MkFound my ry _)
    with my
  ... | Nothing rewrite leftIdentity ry = refl
  ... | Just y  rewrite leftIdentity ry = refl
  iIsLawfulMonoidFound .concatenation [] = refl 
  iIsLawfulMonoidFound .concatenation (x ∷ xs)
    rewrite iIsLawfulMonoidFound .IsLawfulMonoid.concatenation xs
    = refl


-- | The monoid 'Found' is commutative.
--
-- We rely on the crucial fact that the found item is always the same.
@0 prop-Found-<>-sym
  : ∀ {@0 z : a} ⦃ _ : Eq a ⦄ ⦃ @0 _ : IsLawfulEq a ⦄
  → (x y : Found a z) → x <> y ≡ y <> x
--
prop-Found-<>-sym {z = z} (MkFound mx rx ix) (MkFound my ry iy)
  with mx | my
... | Nothing | Nothing rewrite prop-<>-sym rx ry = refl
... | Nothing | Just y  rewrite prop-<>-sym rx ry = refl
... | Just x  | Nothing rewrite prop-<>-sym rx ry = refl
... | Just x  | Just y
    rewrite prop-<>-sym rx (singleton y <> ry)
    | sym (associativity (singleton y) ry rx)
    | associativity ry (singleton x) rx
    | prop-<>-sym ry (singleton x)
    | sym (associativity (singleton x) ry rx)
    | prop-<>-sym ry rx
    = equality-Found-1 _ _ refl
      (cong (λ o → singleton o <> rx <> ry) ∘ Just-injective _ _ ∘ sym)
  where
    Just-injective : ∀ (x y : b) → Just x ≡ Just y → x ≡ y
    Just-injective _ _ refl = refl

instance
  iCommutativeFound
    : ∀ {@0 z : a}  ⦃ _ : Eq a ⦄ ⦃ @0 _ : IsLawfulEq a ⦄
    → Monoid.Commutative (Found a z)
  iCommutativeFound .Monoid.monoid = iMonoidFound
  iCommutativeFound .Monoid.commutative = prop-Found-<>-sym

{-# COMPILE AGDA2HS iCommutativeFound #-}

{-----------------------------------------------------------------------------
    Properties
    putBack
------------------------------------------------------------------------------}

-- | 'putBack' is a homomorphism of 'Monoid'.
prop-morphism-putBack
  : ∀ {@0 z : a} → Monoid.IsHomomorphism (putBack {z = z})
--
prop-morphism-putBack .Monoid.homo-mempty = refl
prop-morphism-putBack .Monoid.homo-<> (MkFound mx rx _) (MkFound my ry _)
  with mx | my
... | Nothing | Nothing = refl
... | Nothing | Just y
  rewrite associativity (singleton y) rx ry
  | prop-<>-sym (singleton y) rx
  | sym (associativity rx (singleton y) ry)
  = refl
... | Just x  | Nothing
  rewrite associativity (singleton x) rx ry
  = refl
... | Just x  | Just y
  rewrite associativity (singleton x) rx (singleton y <> ry)
  = refl

--
prop-putBack-here
  : ∀ {@0 z : a} (x : a)
  → (@0 prf : x ≡ z) → putBack (here x prf) ≡ singleton x
--
prop-putBack-here x refl = rightIdentity (singleton x)

{-----------------------------------------------------------------------------
    Properties
    foundIt
------------------------------------------------------------------------------}

-- | Test whether we have found an element.
foundIt : ∀ {@0 z : a} → Found a z → Monoid.Disj
foundIt (MkFound Nothing  _ _) = mempty
foundIt (MkFound (Just _) _ _) = Monoid.MkDisj True

-- | 'foundIt' is a monoid homomorphism.
prop-morphism-foundIt
  : ∀ {@0 z : a} → Monoid.IsHomomorphism (foundIt {z = z})
--
prop-morphism-foundIt .Monoid.homo-mempty = refl
prop-morphism-foundIt .Monoid.homo-<> (MkFound mx _ _) (MkFound my _ _)
  with mx | my
... | Nothing | Nothing = refl
... | Nothing | Just y  = refl
... | Just x  | Nothing = refl
... | Just x  | Just y  = refl

--
prop-foundIt-here
  : ∀ {@0 z : a} (x : a)
  → (@0 prf : x ≡ z) → foundIt (here x prf) ≡ Monoid.MkDisj True
--
prop-foundIt-here x refl = refl

{-----------------------------------------------------------------------------
    Operations
    findOne
------------------------------------------------------------------------------}
-- | 'deleteOne' on a 'singleton' 'Bag'.
findOne : ∀ ⦃ _ : Eq a ⦄ ⦃ @0 _ : IsLawfulEq a ⦄ → (x : a) → a → Found a x
findOne x y =
  if x == y
  then (λ ⦃ @0 eq ⦄ → here y (sym (equality _ _ eq)))
  else elsewhere y 

{-# COMPILE AGDA2HS findOne #-}

--
prop-putBack-findOne-singleton
  : ∀ ⦃ _ : Eq a ⦄ ⦃ _ : IsLawfulEq a ⦄ (x y : a)
  → putBack (foldBag (findOne x) (singleton y)) ≡ singleton y
--
prop-putBack-findOne-singleton {a} x y =
    helper (x == y) refl
  where
    helper : (b : Bool) → (x == y) ≡ b
      → putBack (foldBag (findOne x) (singleton y)) ≡ singleton y
    helper True eq =
      trans (cong putBack (ifTrueEqThen _ eq)) (prop-putBack-here y (sym (equality _ _ eq)))
    helper False eq =
      trans (cong putBack (ifFalseEqElse _ eq)) refl

-- | Finding an item and putting it back is equivalent to no change.
prop-putBack-findOne
  : ∀ ⦃ _ : Eq a ⦄ ⦃ _ : IsLawfulEq a ⦄ (x : a) (xs : Bag a)
  → putBack (foldBag (findOne x) xs) ≡ xs
--
prop-putBack-findOne x = 
    prop-Bag-equality lhs rhs
      (Monoid.prop-morphism-∘ _ _ (prop-morphism-foldBag _) prop-morphism-putBack)
      (Monoid.prop-morphism-id)
      (λ y → prop-putBack-findOne-singleton x y)
  where 
    lhs = λ xs → putBack (foldBag (findOne x) xs)
    rhs = λ xs → xs

--
prop-foundIt-findOne-singleton
  : ∀ ⦃ _ : Eq a ⦄ ⦃ _ : IsLawfulEq a ⦄ (x y : a)
  → foundIt (foldBag (findOne x) (singleton y)) ≡ mmember x (singleton y)
--
prop-foundIt-findOne-singleton {a} x y =
    helper (x == y) refl
  where
    helper : (b : Bool) → (x == y) ≡ b
      → foundIt (foldBag (findOne x) (singleton y)) ≡ mmember x (singleton y)
    helper True eq =
      begin
        foundIt (foldBag (findOne x) (singleton y))
      ≡⟨ cong foundIt (ifTrueEqThen _ eq) ⟩
        foundIt (here y (sym (equality _ _ eq)))
      ≡⟨ prop-foundIt-here y (sym (equality _ _ eq)) ⟩
        Monoid.MkDisj True
      ≡⟨ sym (ifTrueEqThen _ eq) ⟩
        mmember x (singleton y)
      ∎
    helper False eq =
      begin
        foundIt (foldBag (findOne x) (singleton y))
      ≡⟨ cong foundIt (ifFalseEqElse _ eq) ⟩
        foundIt {z = x} (elsewhere y)
      ≡⟨⟩
        mempty
      ≡⟨ sym (ifFalseEqElse _ eq) ⟩
        mmember x (singleton y)
      ∎

--
prop-foundIt-findOne
  : ∀ ⦃ _ : Eq a ⦄ ⦃ _ : IsLawfulEq a ⦄ (x : a) (xs : Bag a)
  → foundIt (foldBag (findOne x) xs) ≡ mmember x xs
--
prop-foundIt-findOne x = 
    prop-Bag-equality lhs rhs
      (Monoid.prop-morphism-∘ _ _ (prop-morphism-foldBag _) prop-morphism-foundIt)
      (prop-morphism-mmember x)
      (λ y → prop-foundIt-findOne-singleton x y)
  where 
    lhs = λ xs → foundIt (foldBag (findOne x) xs)
    rhs = λ xs → mmember x xs

--
prop-findOne-member
  : ∀ ⦃ _ : Eq a ⦄ ⦃ _ : IsLawfulEq a ⦄ (x : a) (xs : Bag a)
  → isJust (found (foldBag (findOne x) xs)) ≡ member x xs
--
prop-findOne-member {a} x xs =
  begin
    isJust (found (foldBag (findOne x) xs))
  ≡⟨ sym (lemma (foldBag (findOne x) xs))⟩
    Monoid.getDisj (foundIt (foldBag (findOne x) xs))
  ≡⟨ cong Monoid.getDisj (prop-foundIt-findOne x xs) ⟩
    Monoid.getDisj (mmember x xs)
  ≡⟨⟩
    member x xs
  ∎
  where
    lemma
      : ∀ {@0 z : a} (fx : Found a z)
      → Monoid.getDisj (foundIt fx) ≡ isJust (found fx)
    lemma (MkFound Nothing  _ _) = refl
    lemma (MkFound (Just x) _ _) = refl

{-----------------------------------------------------------------------------
    Operations and Properties
    deleteOne
------------------------------------------------------------------------------}
-- | Delete a given item from the given 'Bag' once.
deleteOne
  : ∀ ⦃ _ : Eq a ⦄ ⦃ @0 _ : IsLawfulEq a ⦄
  → a → Bag a → Bag a
deleteOne x = rest ∘ foldBag (findOne x)

{-# COMPILE AGDA2HS deleteOne #-}

--
@0 prop-deleteOne-member-True
  : ∀ ⦃ _ : Eq a ⦄ ⦃ @0 _ : IsLawfulEq a ⦄ (x : a) (xs : Bag a)
  → member x xs ≡ True
  → xs ≡ singleton x <> deleteOne x xs
--
prop-deleteOne-member-True x xs eq-member
  with eq-found ← prop-findOne-member x xs
  with eq-putback ← prop-putBack-findOne x xs
  with foldBag (findOne x) xs
... | MkFound Nothing  _ _ = case trans eq-found eq-member of λ ()
... | MkFound (Just x1) _ ix1
  rewrite recompute-Eq x x1 (ix1 x1 refl)
  = sym eq-putback

--
prop-deleteOne-member-False
  : ∀ ⦃ _ : Eq a ⦄ ⦃ _ : IsLawfulEq a ⦄ (x : a) (xs : Bag a)
  → member x xs ≡ False
  → xs ≡ deleteOne x xs
--
prop-deleteOne-member-False x xs eq-member
  with eq-found ← prop-findOne-member x xs
  with eq-putback ← prop-putBack-findOne x xs
  with foldBag (findOne x) xs
... | MkFound Nothing  _ _ = sym eq-putback
... | MkFound (Just _) _ _ = case trans eq-found eq-member of λ ()
