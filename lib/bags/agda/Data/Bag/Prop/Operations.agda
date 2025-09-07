
-- | Proofs on 'Bag'.
module Data.Bag.Prop.Operations
  {-|
  -- * Query
  -- ** null
  ; prop-null-singleton
  ; prop-morphism-mnull
  -- ** size
  ; prop-size-mempty
  ; prop-size-singleton
  ; prop-size-<>
  ; prop-morphism-msize
  -- ** count
  ; prop-def-count
  -- ** member
  ; prop-member-singleton
  ; prop-morphism-mmember

  -- * Construction
  -- ** fromList
  ; prop-fromList-singleton
  ; prop-fromList-empty
  ; prop-fromList-++
  ; prop-morphism-fromList
  ; prop-size-fromList
  ; prop-fromList-filter

  -- * Combine
  -- ** cartesianProduct
  ; prop-def-cartesianProduct
  ; prop-morphism-cartesianProduct-1
  ; prop-morphism-cartesianProduct-2
  ; prop-null-cartesianProduct
  ; prop-filter-cartesianProduct

  -- ** equijoin
  ; prop-def-equijoin
  ; prop-morphism-equijoin-1
  ; prop-morphism-equijoin-2

  -- * Traversal
  -- ** map
  ; prop-map-singleton
  ; prop-morphism-map
  -- ** concatMap
  ; prop-def-concatMap
  -- ** filter
  ; prop-def-filter
  ; prop-morphism-filter
  -} where

open import Haskell.Prelude hiding (lookup; null; map; filter; concatMap)

open import Haskell.Data.Bag.Quotient
open import Data.Bag.Prop.Core
open import Data.Bag.Def

open import Haskell.Prim.Alternative
open import Haskell.Prim.MonadPlus
open import Haskell.Law
open import Haskell.Law.Applicative.FromMonad
open import Haskell.Law.Extensionality
open import Haskell.Law.Functor.FromMonad
open import Haskell.Law.Monad.Extra
open import Haskell.Law.MonadPlus
open import Haskell.Law.Num

import Haskell.Prim.List as List
import Haskell.Law.Monad as Monad
import Haskell.Law.Monoid as Monoid

open import Data.Monoid.Extra
import      Data.Monoid.Morphism as Monoid
import      Data.Monoid.Refinement as Monoid

{-# FOREIGN AGDA2HS
{-# OPTIONS_GHC -Wno-unused-top-binds #-}
#-}
dummyProp : ⊤
dummyProp = tt
{-# COMPILE AGDA2HS dummyProp #-}

------------------------------------------------------------------------------
-- Move out: Additional type of monad

record IsCommutativeMonad (m : Type → Type) ⦃ _ : Monad m ⦄ : Type₁ where
  field
    -- Different monadic actions commute
    prop-monad-sym : ∀ {a b} (mx : m a) (my : m b) (mz : a → b → m c)
      → mx >>= (λ x → my >>= (λ y → mz x y))
        ≡ my >>= (λ y → mx >>= (λ x → mz x y))

{-----------------------------------------------------------------------------
    Properties
    null
------------------------------------------------------------------------------}
-- | The 'Data.Bag.singleton' 'Data.Bag.Bag' is not empty.
prop-null-singleton
  : ∀ (x : a) → null (singleton x) ≡ False
--
prop-null-singleton x = refl

{-----------------------------------------------------------------------------
    Properties
    size
------------------------------------------------------------------------------}
-- | The 'Data.Bag.singleton' 'Data.Bag.Bag' has @'size' = 1@.
prop-size-singleton
  : ∀ (x : a) → size (singleton x) ≡ 1
--
prop-size-singleton x = refl

-- | The empty 'Data.Bag.Bag' has @'size' = 0@.
prop-size-mempty
  : ∀ {a} → size {a} mempty ≡ 0
--
prop-size-mempty = refl

-- | The union of 'Data.Bag.Bag's adds their sizes.
prop-size-<>
  : ∀ (xs ys : Bag a) → size (xs <> ys) ≡ size xs + size ys
--
prop-size-<> xs ys = refl

{-----------------------------------------------------------------------------
    Properties
    count
------------------------------------------------------------------------------}
-- | Definition of 'Data.Bag.count'.
prop-def-count
  : ∀ ⦃ _ : Eq a ⦄ (x : a) (xs : Bag a)
  → count x xs ≡ size (filter (x ==_) xs)
--
prop-def-count x xs = refl

{-----------------------------------------------------------------------------
    Properties
    member
------------------------------------------------------------------------------}
-- | An item is a member of a 'Data.Bag.singleton'
-- 'Data.Bag.Bag' if and only if it is equal to the item in the bag.
prop-member-singleton
  : ∀ ⦃ _ : Eq a ⦄ (x y : a)
  → member x (singleton y) ≡ (x == y)
--
prop-member-singleton x y
  with x == y
... | False = refl
... | True  = refl

{-----------------------------------------------------------------------------
    Properties
    functorial type classes
------------------------------------------------------------------------------}
--
prop-foldBag-associative
  : ∀ ⦃ _ : Monoid.Commutative c ⦄ ⦃ _ : IsLawfulMonoid c ⦄
    (g : b → c) (f : a → Bag b) (xs : Bag a)
  → foldBag (foldBag g ∘ f) xs ≡ foldBag g (foldBag f xs)
--
prop-foldBag-associative g f =
    prop-Bag-equality lhs rhs
      (prop-morphism-foldBag _)
      (Monoid.prop-morphism-∘ _ _ (prop-morphism-foldBag _) (prop-morphism-foldBag _))
      (λ x → refl)
  where 
    lhs = λ xs → foldBag (foldBag g ∘ f) xs
    rhs = λ xs → foldBag g (foldBag f xs)


instance
  iPreLawfulMonadBag : PreLawfulMonad Bag
  iPreLawfulMonadBag .leftIdentity  = λ a' k → refl
  iPreLawfulMonadBag .rightIdentity = prop-foldBag-function-singleton
  iPreLawfulMonadBag .associativity = λ ma f g → prop-foldBag-associative g f ma
  iPreLawfulMonadBag .def->>->>= _ _ = refl
  iPreLawfulMonadBag .def-pure-return _ = refl
  iPreLawfulMonadBag .def-fmap->>= _ _ = refl
  iPreLawfulMonadBag .def-<*>->>= _ _ = refl

  isLawfulApplicativeBag : IsLawfulApplicative Bag
  isLawfulApplicativeBag = prop-PreLawfulMonad→IsLawfulApplicative

  iLawfulFunctorBag : IsLawfulFunctor Bag
  iLawfulFunctorBag = prop-PreLawfulMonad→IsLawfulFunctor

  iIsLawfulMonadBag : IsLawfulMonad Bag
  iIsLawfulMonadBag = record {}

  iLawfulMonadPlusBag : IsLawfulMonadPlus Bag
  iLawfulMonadPlusBag .mplus-mzero-x = Monoid.leftIdentity
  iLawfulMonadPlusBag .mplus-x-mzero = Monoid.rightIdentity
  iLawfulMonadPlusBag .mplus-assoc   = λ x y z → sym (Monoid.associativity x y z)
  iLawfulMonadPlusBag .mzero-bind    = λ k → refl
  iLawfulMonadPlusBag .bind-mzero    = prop-foldBag-function-mempty

  iDistributiveMonadPlusBag : IsDistributiveMonadPlus Bag
  iDistributiveMonadPlusBag .mplus-bind x y k = prop-foldBag-<> k x y

  iCommutativeMonadBag : IsCommutativeMonad Bag
  iCommutativeMonadBag .IsCommutativeMonad.prop-monad-sym mx my mz =
      prop-Bag-equality-2 lhs rhs
        (λ xs → Monoid.prop-morphism-∘ _ _ (Monoid.prop-morphism-curry _ (λ x → prop-morphism-foldBag _)) (prop-morphism-foldBag-fun xs))
        (λ xs → prop-morphism-foldBag _)
        (λ ys → prop-morphism-foldBag _)
        (λ ys → Monoid.prop-morphism-∘ _ _ (Monoid.prop-morphism-curry _ (λ y → prop-morphism-foldBag _)) (prop-morphism-foldBag-fun ys))
        (λ x y → refl)
        mx my
    where
      lhs = λ xs ys → xs >>= (λ x → ys >>= (λ y → mz x y))
      rhs = λ xs ys → ys >>= (λ y → xs >>= (λ x → mz x y))

{-----------------------------------------------------------------------------
    Properties
    fromList
------------------------------------------------------------------------------}
-- | 'Data.Bag.fromList' maps single element lists to 'Data.Bag.singleton'.
prop-fromList-singleton
  : ∀ (x : a) → fromList (x ∷ []) ≡ singleton x
--
prop-fromList-singleton x = Monoid.rightIdentity (singleton x)

-- | 'Data.Bag.fromList' maps single element lists to singleton
prop-fromList-empty
  : ∀ {a} → fromList {a} [] ≡ mempty
--
prop-fromList-empty = refl

-- | 'Data.Bag.fromList' maps list concatenation
-- to 'Data.Bag.union' of 'Bag's.
prop-fromList-++
  : ∀ (xs ys : List a) 
  → fromList (xs ++ ys) ≡ fromList xs <> fromList ys
--
prop-fromList-++ [] ys = sym (Monoid.leftIdentity _)
prop-fromList-++ (x ∷ xs) ys
  rewrite ∷-++-assoc x xs ys
  rewrite prop-fromList-++ xs ys
  rewrite Monoid.associativity (singleton x) (fromList xs) (fromList ys)
  = refl

-- | 'Data.Bag.fromList' preserves list length.
prop-size-fromList
  : ∀ (xs : List a)
  → size (fromList xs) ≡ length xs
--
prop-size-fromList [] = refl
prop-size-fromList (x ∷ xs) rewrite prop-size-fromList xs = refl

-- | 'Data.Bag.fromList' maps 'Data.List.filter' to 'Data.Bag.filter'.
prop-fromList-filter
  : ∀ (p : a → Bool) (xs : List a) 
  → fromList (List.filter p xs) ≡ filter p (fromList xs)
--
prop-fromList-filter p [] = refl
prop-fromList-filter p (x ∷ xs)
  with p x
... | False
    rewrite Monoid.leftIdentity (filter p (fromList xs))
    = prop-fromList-filter p xs
... | True
    rewrite prop-fromList-filter p xs
    = refl

{-----------------------------------------------------------------------------
    Properties
    Homomorphisms
------------------------------------------------------------------------------}
-- | 'Data.Bag.msize' is a monoid homomorphism.
prop-morphism-msize
  : Monoid.IsHomomorphism ⦃ iMonoidBag {a} ⦄ msize
--
prop-morphism-msize = prop-morphism-foldBag _

-- | 'Data.Bag.fromList' is a monoid homomorphism.
prop-morphism-fromList
  : Monoid.IsHomomorphism (fromList {a})
--
prop-morphism-fromList =
  Monoid.MkIsHomomorphism prop-fromList-empty prop-fromList-++

-- | 'Data.Bag.map' is a monoid homomorphism.
prop-morphism-map
  : ∀ (f : a → b) → Monoid.IsHomomorphism (map f)
--
prop-morphism-map f = prop-morphism-foldBag _

-- | 'Data.Bag.filter' is a monoid homomorphism.
prop-morphism-filter
  : ∀ (p : a → Bool) → Monoid.IsHomomorphism (filter p)
--
prop-morphism-filter p = prop-morphism-foldBag _

-- | 'Data.Bag.mnull' is a monoid homomorphism.
prop-morphism-mnull
  : Monoid.IsHomomorphism ⦃ iMonoidBag {a} ⦄ mnull
--
prop-morphism-mnull = prop-morphism-foldBag _

-- | 'Data.Bag.member' is a monoid homomorphism.
prop-morphism-mmember
  : ∀ ⦃ _ : Eq a ⦄ (x : a)
  → Monoid.IsHomomorphism ⦃ iMonoidBag {a} ⦄ (mmember x)
--
prop-morphism-mmember _ = prop-morphism-foldBag _

-- | 'Data.Bag.cartesianProduct' is a monoid homomorphism
-- in its first argument.
prop-morphism-cartesianProduct-1
  : ∀ (ys : Bag b)
  → Monoid.IsHomomorphism (λ xs → cartesianProduct {a} {b} xs ys)
--
prop-morphism-cartesianProduct-1 ys = prop-morphism-foldBag _

-- | 'Data.Bag.cartesianProduct' is a monoid homomorphism
-- in its second argument.
prop-morphism-cartesianProduct-2
  : ∀ (xs : Bag a)
  → Monoid.IsHomomorphism (λ (ys : Bag b) → cartesianProduct {a} {b} xs ys)
--
prop-morphism-cartesianProduct-2 xs .Monoid.homo-mempty =
  prop-foldBag-function-mempty xs
prop-morphism-cartesianProduct-2 xs .Monoid.homo-<> ys1 ys2 =
  prop-foldBag-function-<> _ _ xs

-- | 'Data.Bag.equijoin' is a monoid homomorphism in its first argument.
prop-morphism-equijoin-1
  : ∀ {k} ⦃ _ : Eq k ⦄ (f : a → k) (g : b → k) (ys : Bag b)
  → Monoid.IsHomomorphism (λ xs → equijoin f g xs ys)
--
prop-morphism-equijoin-1 f g ys = prop-morphism-foldBag _

-- | 'Data.Bag.equijoin' is a monoid homomorphism in its second argument.
prop-morphism-equijoin-2
  : ∀ {k} ⦃ _ : Eq k ⦄ (f : a → k) (g : b → k) (xs : Bag a)
  → Monoid.IsHomomorphism (λ ys → equijoin f g xs ys)
--
prop-morphism-equijoin-2 f g xs .Monoid.homo-mempty =
  prop-foldBag-function-mempty xs
prop-morphism-equijoin-2 f g xs .Monoid.homo-<> x y =
  prop-foldBag-function-<> _ _ xs

{-----------------------------------------------------------------------------
    Properties
    cartesianProduct
------------------------------------------------------------------------------}
-- | Definition of 'Data.Bag.cartesianProduct'.
prop-def-cartesianProduct
  : ∀ (xs : Bag a) (ys : Bag b)
  → cartesianProduct xs ys
    ≡ (do x ← xs; y ← ys; pure (x , y))
--
prop-def-cartesianProduct xs ys = refl

_||-Conj_ : Conj → Conj → Conj
_||-Conj_ (MkConj x) (MkConj y) = MkConj (x || y)

lemma-morphism-||-1
  : ∀ (x : Conj)
  → Monoid.IsHomomorphism (λ y → y ||-Conj x)
lemma-morphism-||-1 (MkConj x) = record
  { homo-mempty = refl
  ; homo-<> = λ (MkConj a) (MkConj b) → cong MkConj (lemma a b x)
  }
  where
    lemma : ∀ (a b c : Bool) → ((a && b) || c) ≡ ((a || c) && (b || c))
    lemma False False c = sym (prop-&&-idem c)
    lemma False True  c = sym (prop-x-&&-True c)
    lemma True  b     c = refl

lemma-morphism-||-2
  : ∀ (x : Conj)
  → Monoid.IsHomomorphism (λ y → x ||-Conj y)
lemma-morphism-||-2 (MkConj x) = record
  { homo-mempty = cong MkConj (prop-x-||-True x)
  ; homo-<> = λ (MkConj a) (MkConj b) → cong MkConj (prop-||-&&-distribute x a b)
  }

-- | Monoid version of 'prop-null-cartesianProduct'.
lemma-mnull-cartesianProduct
  : ∀ (xs : Bag a) (ys : Bag b)
  → mnull (cartesianProduct xs ys) ≡ (mnull xs ||-Conj mnull ys)
--
lemma-mnull-cartesianProduct =
    prop-Bag-equality-2 lhs rhs
      (λ xs → Monoid.prop-morphism-∘ _ _ (prop-morphism-cartesianProduct-2 xs) prop-morphism-mnull)
      (λ xs → Monoid.prop-morphism-∘ _ _ prop-morphism-mnull (lemma-morphism-||-2 (mnull xs)))
      (λ ys → Monoid.prop-morphism-∘ _ _ (prop-morphism-cartesianProduct-1 ys) prop-morphism-mnull)
      (λ ys → Monoid.prop-morphism-∘ _ _ prop-morphism-mnull (lemma-morphism-||-1 (mnull ys)))
      (λ x y → refl)
  where 
    lhs = λ xs ys → mnull (cartesianProduct xs ys)
    rhs = λ xs ys → (mnull xs ||-Conj mnull ys)

-- | A 'Data.Bag.cartesianProduct' is empty
-- if and only if both arguments are empty.
prop-null-cartesianProduct
  : ∀ (xs : Bag a) (ys : Bag b)
  → null (cartesianProduct xs ys) ≡ (null xs || null ys)
--
prop-null-cartesianProduct xs ys =
  cong getConj (lemma-mnull-cartesianProduct xs ys)

{-----------------------------------------------------------------------------
    Properties
    equijoin
------------------------------------------------------------------------------}
-- | Definition of 'Data.Bag.equijoin'.
prop-def-equijoin
  : ∀ {k} ⦃ _ : Eq k ⦄
      (f : a → k) (g : b → k) (xs : Bag a) (ys : Bag b)
  → equijoin f g xs ys
    ≡ (do x ← xs; y ← ys; guard (f x == g y); pure (x , y))
--
prop-def-equijoin f g xs ys = refl

{-----------------------------------------------------------------------------
    Properties
    map
------------------------------------------------------------------------------}
-- | Applying 'Data.Bag.map' to a 'Data.Bag.singleton'
-- applies the function to the item.
prop-map-singleton
  : ∀ (f : a → b) (x : a)
  → map f (singleton x) ≡ singleton (f x)
--
prop-map-singleton f x = refl

{-----------------------------------------------------------------------------
    Properties
    concatMap
------------------------------------------------------------------------------}
-- | Definition of 'Data.Bag.concatMap'.
prop-def-concatMap
  : ∀ (f : a → Bag b) (xs : Bag a)
  → concatMap f xs ≡ foldBag f xs
--
prop-def-concatMap f xs = refl

{-----------------------------------------------------------------------------
    Properties
    filter
------------------------------------------------------------------------------}
-- | Definition of 'filter'.
prop-def-filter
  : ∀ (p : a → Bool) (xs : Bag a)
  → filter p xs
    ≡ (do x ← xs; guard (p x); pure x)
--
prop-def-filter p xs = refl

-- | Independent filters promote through 'Data.Bag.cartesianProduct'.
prop-filter-cartesianProduct
  : ∀ (p : a → Bool) (q : b → Bool) (xs : Bag a) (ys : Bag b)
  → filter (λ xy → p (fst xy) && q (snd xy)) (cartesianProduct xs ys)
    ≡ cartesianProduct (filter p xs) (filter q ys)
--
prop-filter-cartesianProduct p q =
    prop-Bag-equality-2 lhs rhs
      (λ xs → Monoid.prop-morphism-∘ _ _ (prop-morphism-cartesianProduct-2 xs) (prop-morphism-filter r))
      (λ xs → Monoid.prop-morphism-∘ _ _ (prop-morphism-filter q) (prop-morphism-cartesianProduct-2 (filter p xs)))
      (λ ys → Monoid.prop-morphism-∘ _ _ (prop-morphism-cartesianProduct-1 ys) (prop-morphism-filter r))
      (λ ys → Monoid.prop-morphism-∘ _ _ (prop-morphism-filter p) (prop-morphism-cartesianProduct-1 (filter q ys)))
      eq-singleton
  where 
    r   = λ xy → p (fst xy) && q (snd xy)
    lhs = λ xs ys → filter r (cartesianProduct xs ys)
    rhs = λ xs ys → cartesianProduct (filter p xs) (filter q ys)
    eq-singleton
      : ∀ x y → lhs (singleton x) (singleton y) ≡ rhs (singleton x) (singleton y)
    eq-singleton x y
      with p x | q y
    ... | True  | True  = refl
    ... | True  | False = refl
    ... | False | True  = refl
    ... | False | False = refl
