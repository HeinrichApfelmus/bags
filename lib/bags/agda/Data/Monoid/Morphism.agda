-- | Monoid morphisms
module Data.Monoid.Morphism
  {-|
  -- * Definition
  ; prop-homomorphism-mempty
  ; prop-homomorphism-<>
  -- * Properties
  ; prop-morphism-id
  ; prop-morphism-∘
  ; prop-morphism-curry
  -}
  where

open import Haskell.Prim
open import Haskell.Prim.Monoid

open import Haskell.Law
open import Haskell.Law.Extensionality

{-# FOREIGN AGDA2HS
{-# OPTIONS_GHC -Wno-unused-top-binds #-}
#-}
dummyHomo : ⊤
dummyHomo = tt
{-# COMPILE AGDA2HS dummyHomo #-}

-------------------------------------------------------------------------------
-- Monoid Homomorphisms

record IsHomomorphism ⦃ _ : Monoid a ⦄ ⦃ _ : Monoid b ⦄ (f : a → b)
    : Type where
  constructor MkIsHomomorphism
  field
    homo-mempty : f mempty ≡ mempty
    homo-<>     : ∀ x y → f (x <> y) ≡ f x <> f y

open IsHomomorphism public

-- | A homomorphisms of 'Monoid' maps 'mempty' to 'mempty'.
prop-homomorphism-mempty
  : ∀ ⦃ _ : Monoid a ⦄ ⦃ _ : Monoid b ⦄
  → ∀ (f : a → b) → IsHomomorphism f → f mempty ≡ mempty
--
prop-homomorphism-mempty f is = homo-mempty is

-- | A homomorphisms of 'Monoid' distributes over '(<>)'.
prop-homomorphism-<>
  : ∀ ⦃ _ : Monoid a ⦄ ⦃ _ : Monoid b ⦄
  → ∀ (f : a → b) → IsHomomorphism f
  → ∀ x y → f (x <> y) ≡ f x <> f y
--
prop-homomorphism-<> f is = homo-<> is

-------------------------------------------------------------------------------
-- Properties

-- | The identity map is a homomorphism.
prop-morphism-id : ∀ ⦃ _ : Monoid a ⦄ → IsHomomorphism (id {a})
--
prop-morphism-id = MkIsHomomorphism refl (λ x y → refl)

-- | The composition of two homomorphisms is again a homomorphism.
prop-morphism-∘
  : ∀ ⦃ _ : Monoid a ⦄ ⦃ _ : Monoid b ⦄ ⦃ _ : Monoid c ⦄
      (f : a → b) (g : b → c)
  → IsHomomorphism f → IsHomomorphism g → IsHomomorphism (g ∘ f)
--
prop-morphism-∘ f g prop-f prop-g = record
  { homo-mempty =
    trans (cong g (homo-mempty prop-f)) (homo-mempty prop-g)
  ; homo-<> = λ x y →
    trans (cong g (homo-<> prop-f x y)) (homo-<> prop-g (f x) (f y))
  }

-- | Parametrizations of homomorphisms are homomorphisms.
--
-- @f@ can be viewed as a function
-- from the @Monoid a@ to the @Monoid (b → c)@.
prop-morphism-curry
  : ∀ ⦃ _ : Monoid a ⦄ ⦃ _ : Monoid c ⦄ (f : a → b → c)
  → (∀ y → IsHomomorphism (λ x → f x y))
  → IsHomomorphism f
--
prop-morphism-curry f eq .homo-mempty = ext (λ y → eq y .homo-mempty)
prop-morphism-curry f eq .homo-<> x1 x2 = ext (λ y → eq y .homo-<> x1 x2)
