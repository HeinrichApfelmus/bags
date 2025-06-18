{-# OPTIONS_GHC -Wno-unused-top-binds #-}

module Data.Table.Prop 
    (
    -- * Properties
    -- ** Query
    -- $prop-lookup→equality
    
    -- $prop-lookup-singleton
    
    -- $prop-morphism-lookup
    
    -- $prop-elements-singleton
    
    -- $prop-morphism-elements
    
    -- ** Construction
    -- $prop-indexBy-singleton
    
    -- $prop-morphism-indexBy
    
    -- $prop-lookup-indexBy
    
    -- $prop-elements-indexBy
    
    -- ** Combine
    -- $prop-merge-singleton
    
    -- $prop-morphism-merge-1
    
    -- $prop-morphism-merge-2
    
    -- $prop-equijoin-merge-indexBy
    
    )
    where

import Prelude hiding (null, filter, lookup, map, concatMap, replicate)

dummy :: ()
dummy = ()

-- * Properties
{- $prop-elements-indexBy
#p:prop-elements-indexBy#

[prop-elements-indexBy]:
    'elements' is an inverse of 'indexBy'.
    
    > @0 prop-elements-indexBy
    >   : ∀ {k} ⦃ _ : Ord k ⦄ (xs : Bag a) (f : a → k)
    >   → elements (indexBy xs f) ≡ xs
-}
{- $prop-elements-singleton
#p:prop-elements-singleton#

[prop-elements-singleton]:
    The 'elements' of a 'singleton' 'Table' are a 'Bag' with a single item.
    
    > prop-elements-singleton
    >   : ∀ {k a} ⦃ _ : Ord k ⦄ (key : k) (x : a)
    >   → elements (singleton key x) ≡ Bag.singleton x
-}
{- $prop-equijoin-merge-indexBy
#p:prop-equijoin-merge-indexBy#

[prop-equijoin-merge-indexBy]:
    Combinging 'merge' and 'indexBy' will give an efficient implementation
    implementation of 'equijoin'.
    
    Proof: We use a proof idea that differs from the one in the paper.
    Specifically, we use uniqueness of 'Data.Bag.foldBag'.
    The property holds because:
    
    * When considered as maps from @xs@ or @ys@, the left-hand side
    and the right-hand side are monoid homomorphisms, and
    
    * it holds on 'Data.Bag.singleton'.
    
    > @0 prop-equijoin-merge-indexBy
    >   : ∀ {k} ⦃ _ : Ord k ⦄ ⦃ _ : IsLawfulEq k ⦄
    >       (f : a → k) (g : b → k) (xs : Bag a) (ys : Bag b)
    >   → Bag.equijoin f g xs ys
    >     ≡ elements (merge (indexBy xs f) (indexBy ys g))
-}
{- $prop-indexBy-singleton
#p:prop-indexBy-singleton#

[prop-indexBy-singleton]:
    'indexBy' on a single item returns a 'singleton'
    whose key is a given by an application of the grouping function.
    
    > prop-indexBy-singleton
    >   : ∀ {k} ⦃ _ : Ord k ⦄ (x : a) (f : a → k)
    >   → indexBy (Bag.singleton x) f
    >     ≡ singleton (f x) x
-}
{- $prop-lookup-indexBy
#p:prop-lookup-indexBy#

[prop-lookup-indexBy]:
    'indexBy' filters items by 'key'.
    
    > prop-lookup-indexBy
    >   : ∀ {k} ⦃ _ : Ord k ⦄ (key : k) (xs : Bag a) (f : a → k)
    >   → lookup key (indexBy xs f)
    >     ≡ Bag.filter (λ x → key == f x) xs
-}
{- $prop-lookup-singleton
#p:prop-lookup-singleton#

[prop-lookup-singleton]:
    Looking up a key in a 'singleton' 'Table' returns the item
    if and only if the keys match.
    
    > prop-lookup-singleton
    >   : ∀ {k a} ⦃ _ : Ord k ⦄ ⦃ _ : IsLawfulEq k ⦄
    >       (key keyx : k) (x : a)
    >   → lookup key (singleton keyx x)
    >     ≡ (if key == keyx then Bag.singleton x else mempty)
-}
{- $prop-lookup→equality
#p:prop-lookup→equality#

[prop-lookup→equality]:
    Tables that have the same 'lookup' function are equal.
    
    > @0 prop-lookup→equality
    >   : ∀ {k} ⦃ _ : Ord k ⦄ (xs ys : Table k a)
    >   → (∀ key → lookup key xs ≡ lookup key ys)
    >   → xs ≡ ys
-}
{- $prop-merge-singleton
#p:prop-merge-singleton#

[prop-merge-singleton]:
    Merging two 'singleton' 'Table's yields another 'singleton'
    'Table' if and only if the two items have the same key.
    
    > @0 prop-merge-singleton
    >   : ∀ {k} ⦃ _ : Ord k ⦄ ⦃ _ : IsLawfulEq k ⦄
    >     (keyx : k) (x : a) (keyy : k) (y : b)
    >   → merge (singleton keyx x) (singleton keyy y)
    >     ≡ (if keyx == keyy then singleton keyx (x , y) else mempty)
-}
{- $prop-morphism-elements
#p:prop-morphism-elements#

[prop-morphism-elements]:
    'elements' on 'Table' is a homomorphism of monoids.
    
    > @0 prop-morphism-elements
    >   : ∀ {a k} ⦃ _ : Ord k ⦄
    >   → Monoid.IsHomomorphism (elements {a} {k})
-}
{- $prop-morphism-indexBy
#p:prop-morphism-indexBy#

[prop-morphism-indexBy]:
    'indexBy' is a homomorphism of monoids.
    
    > prop-morphism-indexBy
    >   : ∀ {a k} ⦃ _ : Ord k ⦄
    >   → ∀ (f : a → k) → Monoid.IsHomomorphism (λ xs → indexBy xs f)
-}
{- $prop-morphism-lookup
#p:prop-morphism-lookup#

[prop-morphism-lookup]:
    'lookup' is a homomorphism of monoids.
    
    > prop-morphism-lookup
    >   : ∀ {a k} ⦃ _ : Ord k ⦄
    >   → ∀ (key : k) → Monoid.IsHomomorphism (lookup {a} key)
-}
{- $prop-morphism-merge-1
#p:prop-morphism-merge-1#

[prop-morphism-merge-1]:
    'merge' is a homomorphism of monoids in its first argument.
    
    > @0 prop-morphism-merge-1
    >   : ∀ {k} ⦃ _ : Ord k ⦄
    >   → ∀ (ys : Table k b) → Monoid.IsHomomorphism (λ xs → merge {a} xs ys)
-}
{- $prop-morphism-merge-2
#p:prop-morphism-merge-2#

[prop-morphism-merge-2]:
    'merge' is a homomorphism of monoids in its second argument.
    
    > @0 prop-morphism-merge-2
    >   : ∀ {k} ⦃ _ : Ord k ⦄
    >   → ∀ (xs : Table k a) → Monoid.IsHomomorphism (λ ys → merge {a} {b} xs ys)
-}
