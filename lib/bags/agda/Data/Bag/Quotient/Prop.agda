
-- | Core properties of 'Bag'
module Data.Bag.Quotient.Prop where

open import Haskell.Prelude

open import Haskell.Law
open import Haskell.Law.Extensionality using (ext)
open import Haskell.Law.Function
open import Haskell.Law.Monoid as Monoid

import Data.Monoid.Refinement as Monoid
import Data.Monoid.Morphism as Monoid

open import Haskell.Data.Bag.Quotient public

{-----------------------------------------------------------------------------
    Core properties
------------------------------------------------------------------------------}
-- | 'foldBag' is a homomorphism of 'Monoid'.
prop-morphism-foldBag
  : ∀ ⦃ _ : Monoid.Commutative b ⦄ (f : a → b)
  → Monoid.IsHomomorphism (foldBag f)
--
prop-morphism-foldBag f = Monoid.MkIsHomomorphism refl (λ x y → refl)

-- | Proof principle:
-- Two maps @f@, @g@ from 'Bag' to any commutative monoid are equal if:
--
-- * They are monoid homomorphisms.
--   This property typically follows from composition of morphisms.
-- * And they are equal on 'singleton'.
--   With the rewrite rules, this property can be computed.
prop-Bag-equality
  : ∀ ⦃ _ : Monoid.Commutative b ⦄ (f g : Bag a → b)
  → @0 Monoid.IsHomomorphism f → @0 Monoid.IsHomomorphism g
  → (∀ x → f (singleton x) ≡ g (singleton x))
  → ∀ xs → f xs ≡ g xs
--
prop-Bag-equality f g hom-f hom-g eq-singleton xs =
  begin
    f xs
  ≡⟨ sym (prop-foldBag-unique f hom-f xs) ⟩
    foldBag (f ∘ singleton) xs
  ≡⟨ cong (λ o → foldBag o xs) (ext eq-singleton) ⟩
    foldBag (g ∘ singleton) xs
  ≡⟨ prop-foldBag-unique g hom-g xs ⟩
    g xs
  ∎

-- | Proof principle for functions with two 'Bag' arguments.
prop-Bag-equality-2
  : ∀ ⦃ _ : Monoid.Commutative c ⦄ (f g : Bag a → Bag b → c)
  → @0 (∀ xs → Monoid.IsHomomorphism (λ ys → f xs ys))
  → @0 (∀ xs → Monoid.IsHomomorphism (λ ys → g xs ys))
  → @0 (∀ ys → Monoid.IsHomomorphism (λ xs → f xs ys))
  → @0 (∀ ys → Monoid.IsHomomorphism (λ xs → g xs ys))
  → (∀ x y → f (singleton x) (singleton y) ≡ g (singleton x) (singleton y))
  → ∀ xs ys → f xs ys ≡ g xs ys
--
prop-Bag-equality-2 f g hom-f1 hom-g1 hom-f2 hom-g2 eq-singleton =
  λ xs → prop-Bag-equality _ _ (hom-f1 xs) (hom-g1 xs) (λ y → lemma y xs)
  where
    lemma : ∀ y xs → f xs (singleton y) ≡ g xs (singleton y)
    lemma y = prop-Bag-equality _ _ (hom-f2 _) (hom-g2 _) (λ x → eq-singleton x y)

{-----------------------------------------------------------------------------
    Properties
    Homomorphisms
------------------------------------------------------------------------------}
-- | 'foldBag' that maps to 'mempty' will return 'mempty'.
prop-foldBag-function-mempty
  : ∀ {a b} ⦃ iMb : Monoid.Commutative b ⦄ ⦃ _ : IsLawfulMonoid b ⦄
      (xs : Bag a)
  → foldBag (λ x → mempty) xs ≡ mempty
--
prop-foldBag-function-mempty {a} {b} {{iMb}} =
    prop-foldBag-unique g' homo-g'
  where
    g : a → b
    g = λ x → mempty {b} {{iMb .Monoid.monoid}}

    g' : Bag a → b
    g' = λ xs → mempty

    lemma : g' ∘ singleton ≡ g
    lemma = refl

    homo-g' : Monoid.IsHomomorphism g'
    homo-g' .Monoid.homo-mempty = refl
    homo-g' .Monoid.homo-<> xs ys = sym (Monoid.leftIdentity _)

-- | 'foldBag' is a homomorphism on functions as well.
-- 
-- Note: This property requires commutativity of the image monoid!
-- It does not generally hold for the 'Foldable' class.
--
prop-foldBag-function-<>
  : ∀ ⦃ _ : Monoid.Commutative b ⦄ ⦃ _ : IsLawfulMonoid b ⦄
      (f g : a → b) (xs : Bag a)
  → foldBag (λ x → f x <> g x) xs
    ≡ foldBag f xs <> foldBag g xs
--
prop-foldBag-function-<> {a} f g =
    prop-Bag-equality lhs rhs lhs-homo rhs-homo (λ x → refl)
  where
    lhs = λ xs → foldBag (λ x → f x <> g x) xs
    rhs = λ xs → foldBag f xs <> foldBag g xs

    lhs-homo : Monoid.IsHomomorphism lhs
    lhs-homo = prop-morphism-foldBag _

    @0 rhs-homo : Monoid.IsHomomorphism rhs
    rhs-homo .Monoid.homo-mempty
      = Monoid.leftIdentity mempty
    rhs-homo .Monoid.homo-<> xs ys
      = begin
        (foldBag f xs <> foldBag f ys)
          <> (foldBag g xs <> foldBag g ys)
      ≡⟨ sym (Monoid.associativity _ _ _) ⟩
        foldBag f xs <>
          (foldBag f ys <> (foldBag g xs
            <> foldBag g ys))
      ≡⟨ cong (λ o → foldBag f xs <> o) (Monoid.associativity _ _ _) ⟩
        foldBag f xs <>
          ((foldBag f ys <> foldBag g xs)
            <> foldBag g ys)
      ≡⟨ cong (λ o → foldBag f xs <> (o <> foldBag g ys)) (Monoid.commutative _ _) ⟩
        foldBag f xs <>
          ((foldBag  g xs <> foldBag f ys)
            <> foldBag g ys)
      ≡⟨ cong (λ o → foldBag f xs <> o) (sym (Monoid.associativity _ _ _)) ⟩
        foldBag f xs <>
          (foldBag g xs <> (foldBag f ys)
            <> foldBag g ys)
      ≡⟨ Monoid.associativity _ _ _ ⟩
        rhs xs <> rhs ys
      ∎

-- | 'foldBag' that maps to 'singleton' is the identity.
prop-foldBag-function-singleton
  : ∀ ⦃ _ : Monoid.Commutative b ⦄ (xs : Bag b)
  → foldBag (λ x → singleton x) xs ≡ xs
--
prop-foldBag-function-singleton =
  prop-foldBag-unique _ Monoid.prop-morphism-id
