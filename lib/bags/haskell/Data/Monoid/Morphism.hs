{-# OPTIONS_GHC -Wno-unused-top-binds #-}

module Data.Monoid.Morphism 
    (
    -- * Definition
    -- $prop-homomorphism-mempty
    
    -- $prop-homomorphism-<>
    
    -- * Properties
    -- $prop-morphism-id
    
    -- $prop-morphism-∘
    
    -- $prop-morphism-curry
    
    )
    where

import Prelude hiding (null, filter, lookup, map, concatMap)

dummyHomo :: ()
dummyHomo = ()

-- * Properties
{- $prop-homomorphism-<>
#p:prop-homomorphism-<>#

[prop-homomorphism-<>]:
    A homomorphisms of 'Monoid' distributes over '(<>)'.
    
    > prop-homomorphism-<>
    >   : ∀ ⦃ _ : Monoid a ⦄ ⦃ _ : Monoid b ⦄
    >   → ∀ (f : a → b) → IsHomomorphism f
    >   → ∀ x y → f (x <> y) ≡ f x <> f y
-}
{- $prop-homomorphism-mempty
#p:prop-homomorphism-mempty#

[prop-homomorphism-mempty]:
    A homomorphisms of 'Monoid' maps 'mempty' to 'mempty'.
    
    > prop-homomorphism-mempty
    >   : ∀ ⦃ _ : Monoid a ⦄ ⦃ _ : Monoid b ⦄
    >   → ∀ (f : a → b) → IsHomomorphism f → f mempty ≡ mempty
-}
{- $prop-morphism-curry
#p:prop-morphism-curry#

[prop-morphism-curry]:
    Parametrizations of homomorphisms are homomorphisms.
    
    @f@ can be viewed as a function
    from the @Monoid a@ to the @Monoid (b → c)@.
    
    > prop-morphism-curry
    >   : ∀ ⦃ _ : Monoid a ⦄ ⦃ _ : Monoid c ⦄ (f : a → b → c)
    >   → (∀ y → IsHomomorphism (λ x → f x y))
    >   → IsHomomorphism f
-}
{- $prop-morphism-id
#p:prop-morphism-id#

[prop-morphism-id]:
    The identity map is a homomorphism.
    
    > prop-morphism-id : ∀ ⦃ _ : Monoid a ⦄ → IsHomomorphism (id {a})
-}
{- $prop-morphism-∘
#p:prop-morphism-∘#

[prop-morphism-∘]:
    The composition of two homomorphisms is again a homomorphism.
    
    > prop-morphism-∘
    >   : ∀ ⦃ _ : Monoid a ⦄ ⦃ _ : Monoid b ⦄ ⦃ _ : Monoid c ⦄
    >       (f : a → b) (g : b → c)
    >   → IsHomomorphism f → IsHomomorphism g → IsHomomorphism (g ∘ f)
-}
