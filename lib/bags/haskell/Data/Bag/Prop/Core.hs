{-# OPTIONS_GHC -Wno-unused-top-binds #-}

module Data.Bag.Prop.Core 
    (
    -- * Properties
    -- ** Equality Proofs
    -- $prop-Bag-equality
    
    -- $prop-Bag-equality-2
    
    -- ** foldBag
    -- $prop-foldBag-function-mempty
    
    -- $prop-foldBag-function-<>
    
    -- $prop-morphism-foldBag-fun
    
    )
    where

import Prelude hiding (null, filter, lookup, map, concatMap, replicate)

dummy :: ()
dummy = ()

-- * Properties
{- $prop-Bag-equality
#p:prop-Bag-equality#

[prop-Bag-equality]:
    Proof principle:
    Two maps @f@, @g@ from 'Bag' to any commutative monoid are equal if:
    
    * They are monoid homomorphisms.
    This property typically follows from composition of morphisms.
    * And they are equal on 'singleton'.
    With the rewrite rules, this property can be computed.
    
    > prop-Bag-equality
    >   : ∀ ⦃ _ : Monoid.Commutative b ⦄ ⦃ _ : IsLawfulMonoid b ⦄ (f g : Bag a → b)
    >   → @0 Monoid.IsHomomorphism f → @0 Monoid.IsHomomorphism g
    >   → (∀ x → f (singleton x) ≡ g (singleton x))
    >   → ∀ xs → f xs ≡ g xs
-}
{- $prop-Bag-equality-2
#p:prop-Bag-equality-2#

[prop-Bag-equality-2]:
    Proof principle for functions with two 'Bag' arguments.
    
    > prop-Bag-equality-2
    >   : ∀ ⦃ _ : Monoid.Commutative c ⦄ ⦃ _ : IsLawfulMonoid c ⦄ (f g : Bag a → Bag b → c)
    >   → @0 (∀ xs → Monoid.IsHomomorphism (λ ys → f xs ys))
    >   → @0 (∀ xs → Monoid.IsHomomorphism (λ ys → g xs ys))
    >   → @0 (∀ ys → Monoid.IsHomomorphism (λ xs → f xs ys))
    >   → @0 (∀ ys → Monoid.IsHomomorphism (λ xs → g xs ys))
    >   → (∀ x y → f (singleton x) (singleton y) ≡ g (singleton x) (singleton y))
    >   → ∀ xs ys → f xs ys ≡ g xs ys
-}
{- $prop-foldBag-function-<>
#p:prop-foldBag-function-<>#

[prop-foldBag-function-<>]:
    'foldBag' is a homomorphism on functions as well.
    
    Note: This property requires commutativity of the image monoid!
    It does not generally hold for the 'Foldable' class.
    
    > prop-foldBag-function-<>
    >   : ∀ ⦃ _ : Monoid.Commutative b ⦄ ⦃ _ : IsLawfulMonoid b ⦄
    >       (f g : a → b) (xs : Bag a)
    >   → foldBag (λ x → f x <> g x) xs
    >     ≡ foldBag f xs <> foldBag g xs
-}
{- $prop-foldBag-function-mempty
#p:prop-foldBag-function-mempty#

[prop-foldBag-function-mempty]:
    'foldBag' that maps to 'mempty' will return 'mempty'.
    
    > prop-foldBag-function-mempty
    >   : ∀ {a b} ⦃ iMb : Monoid.Commutative b ⦄ ⦃ _ : IsLawfulMonoid b ⦄
    >       (xs : Bag a)
    >   → foldBag (λ x → mempty) xs ≡ mempty
-}
{- $prop-foldBag-function-singleton
#p:prop-foldBag-function-singleton#

[prop-foldBag-function-singleton]:
    'foldBag' that maps to 'singleton' is the identity.
    
    > prop-foldBag-function-singleton
    >   : ∀ (xs : Bag b)
    >   → foldBag (λ x → singleton x) xs ≡ xs
-}
{- $prop-morphism-foldBag
#p:prop-morphism-foldBag#

[prop-morphism-foldBag]:
    'foldBag' is a homomorphism of 'Monoid'.
    
    > prop-morphism-foldBag
    >   : ∀ ⦃ _ : Monoid.Commutative b ⦄ (f : a → b)
    >   → Monoid.IsHomomorphism (foldBag f)
-}
{- $prop-morphism-foldBag-fun
#p:prop-morphism-foldBag-fun#

[prop-morphism-foldBag-fun]:
    'foldBag' is a homomorphism in the function argument as well.
    
    > prop-morphism-foldBag-fun
    >   : ∀ {a b} ⦃ _ : Monoid.Commutative b ⦄ ⦃ _ : IsLawfulMonoid b ⦄ (xs : Bag a)
    >   → Monoid.IsHomomorphism (λ (f : a → b) → foldBag f xs)
-}
