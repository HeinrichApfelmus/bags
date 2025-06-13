{-# OPTIONS_GHC -Wno-unused-top-binds #-}

module Data.Bag.Prop.Operations 
    (
    -- * Query
    -- ** null
    -- $prop-null-singleton
    
    -- $prop-morphism-mnull
    
    -- ** size
    -- $prop-size-mempty
    
    -- $prop-size-singleton
    
    -- $prop-size-<>
    
    -- $prop-morphism-msize
    
    -- ** count
    -- $prop-def-count
    
    -- ** member
    -- $prop-member-singleton
    
    -- $prop-morphism-mmember
    
    -- * Construction
    -- ** fromList
    -- $prop-fromList-singleton
    
    -- $prop-fromList-empty
    
    -- $prop-fromList-++
    
    -- $prop-morphism-fromList
    
    -- $prop-size-fromList
    
    -- $prop-fromList-filter
    
    -- * Combine
    -- ** cartesianProduct
    -- $prop-def-cartesianProduct
    
    -- $prop-morphism-cartesianProduct-1
    
    -- $prop-morphism-cartesianProduct-2
    
    -- $prop-null-cartesianProduct
    
    -- $prop-filter-cartesianProduct
    
    -- ** equijoin
    -- $prop-def-equijoin
    
    -- $prop-morphism-equijoin-1
    
    -- $prop-morphism-equijoin-2
    
    -- * Traversal
    -- ** map
    -- $prop-map-singleton
    
    -- $prop-morphism-map
    
    -- ** concatMap
    -- $prop-def-concatMap
    
    -- ** filter
    -- $prop-def-filter
    
    -- $prop-morphism-filter
    
    )
    where

import Prelude hiding (null, filter, lookup, map, concatMap)

dummyProp :: ()
dummyProp = ()

-- * Properties
{- $prop-def-cartesianProduct
#p:prop-def-cartesianProduct#

[prop-def-cartesianProduct]:
    Definition of 'Data.Bag.cartesianProduct'.
    
    > prop-def-cartesianProduct
    >   : ∀ (xs : Bag a) (ys : Bag b)
    >   → cartesianProduct xs ys
    >     ≡ (do x ← xs; y ← ys; pure (x , y))
-}
{- $prop-def-concatMap
#p:prop-def-concatMap#

[prop-def-concatMap]:
    Definition of 'Data.Bag.concatMap'.
    
    > prop-def-concatMap
    >   : ∀ (f : a → Bag b) (xs : Bag a)
    >   → concatMap f xs ≡ foldBag f xs
-}
{- $prop-def-count
#p:prop-def-count#

[prop-def-count]:
    Definition of 'Data.Bag.count'.
    
    > prop-def-count
    >   : ∀ ⦃ _ : Eq a ⦄ (x : a) (xs : Bag a)
    >   → count x xs ≡ size (filter (x ==_) xs)
-}
{- $prop-def-equijoin
#p:prop-def-equijoin#

[prop-def-equijoin]:
    Definition of 'Data.Bag.equijoin'.
    
    > prop-def-equijoin
    >   : ∀ {k} ⦃ _ : Eq k ⦄
    >       (f : a → k) (g : b → k) (xs : Bag a) (ys : Bag b)
    >   → equijoin f g xs ys
    >     ≡ (do x ← xs; y ← ys; guard (f x == g y); pure (x , y))
-}
{- $prop-def-filter
#p:prop-def-filter#

[prop-def-filter]:
    Definition of 'filter'.
    
    > prop-def-filter
    >   : ∀ (p : a → Bool) (xs : Bag a)
    >   → filter p xs
    >     ≡ (do x ← xs; guard (p x); pure x)
-}
{- $prop-filter-cartesianProduct
#p:prop-filter-cartesianProduct#

[prop-filter-cartesianProduct]:
    Independent filters promote through 'Data.Bag.cartesianProduct'.
    
    > prop-filter-cartesianProduct
    >   : ∀ (p : a → Bool) (q : b → Bool) (xs : Bag a) (ys : Bag b)
    >   → filter (λ xy → p (fst xy) && q (snd xy)) (cartesianProduct xs ys)
    >     ≡ cartesianProduct (filter p xs) (filter q ys)
-}
{- $prop-fromList-++
#p:prop-fromList-++#

[prop-fromList-++]:
    'Data.Bag.fromList' maps list concatenation
    to 'Data.Bag.union' of 'Bag's.
    
    > prop-fromList-++
    >   : ∀ (xs ys : List a) 
    >   → fromList (xs ++ ys) ≡ fromList xs <> fromList ys
-}
{- $prop-fromList-empty
#p:prop-fromList-empty#

[prop-fromList-empty]:
    'Data.Bag.fromList' maps single element lists to singleton
    
    > prop-fromList-empty
    >   : ∀ {a} → fromList {a} [] ≡ mempty
-}
{- $prop-fromList-filter
#p:prop-fromList-filter#

[prop-fromList-filter]:
    'Data.Bag.fromList' maps 'Data.List.filter' to 'Data.Bag.filter'.
    
    > prop-fromList-filter
    >   : ∀ (p : a → Bool) (xs : List a) 
    >   → fromList (List.filter p xs) ≡ filter p (fromList xs)
-}
{- $prop-fromList-singleton
#p:prop-fromList-singleton#

[prop-fromList-singleton]:
    'Data.Bag.fromList' maps single element lists to 'Data.Bag.singleton'.
    
    > prop-fromList-singleton
    >   : ∀ (x : a) → fromList (x ∷ []) ≡ singleton x
-}
{- $prop-map-singleton
#p:prop-map-singleton#

[prop-map-singleton]:
    Applying 'Data.Bag.map' to a 'Data.Bag.singleton'
    applies the function to the item.
    
    > prop-map-singleton
    >   : ∀ (f : a → b) (x : a)
    >   → map f (singleton x) ≡ singleton (f x)
-}
{- $prop-member-singleton
#p:prop-member-singleton#

[prop-member-singleton]:
    An item is a member of a 'Data.Bag.singleton'
    'Data.Bag.Bag' if and only if it is equal to the item in the bag.
    
    > prop-member-singleton
    >   : ∀ ⦃ _ : Eq a ⦄ (x y : a)
    >   → member x (singleton y) ≡ (x == y)
-}
{- $prop-morphism-cartesianProduct-1
#p:prop-morphism-cartesianProduct-1#

[prop-morphism-cartesianProduct-1]:
    'Data.Bag.cartesianProduct' is a monoid homomorphism
    in its first argument.
    
    > prop-morphism-cartesianProduct-1
    >   : ∀ (ys : Bag b)
    >   → Monoid.IsHomomorphism (λ xs → cartesianProduct {a} {b} xs ys)
-}
{- $prop-morphism-cartesianProduct-2
#p:prop-morphism-cartesianProduct-2#

[prop-morphism-cartesianProduct-2]:
    'Data.Bag.cartesianProduct' is a monoid homomorphism
    in its second argument.
    
    > prop-morphism-cartesianProduct-2
    >   : ∀ (xs : Bag a)
    >   → Monoid.IsHomomorphism (λ (ys : Bag b) → cartesianProduct {a} {b} xs ys)
-}
{- $prop-morphism-equijoin-1
#p:prop-morphism-equijoin-1#

[prop-morphism-equijoin-1]:
    'Data.Bag.equijoin' is a monoid homomorphism in its first argument.
    
    > prop-morphism-equijoin-1
    >   : ∀ {k} ⦃ _ : Eq k ⦄ (f : a → k) (g : b → k) (ys : Bag b)
    >   → Monoid.IsHomomorphism (λ xs → equijoin f g xs ys)
-}
{- $prop-morphism-equijoin-2
#p:prop-morphism-equijoin-2#

[prop-morphism-equijoin-2]:
    'Data.Bag.equijoin' is a monoid homomorphism in its second argument.
    
    > prop-morphism-equijoin-2
    >   : ∀ {k} ⦃ _ : Eq k ⦄ (f : a → k) (g : b → k) (xs : Bag a)
    >   → Monoid.IsHomomorphism (λ ys → equijoin f g xs ys)
-}
{- $prop-morphism-filter
#p:prop-morphism-filter#

[prop-morphism-filter]:
    'Data.Bag.filter' is a monoid homomorphism.
    
    > prop-morphism-filter
    >   : ∀ (p : a → Bool) → Monoid.IsHomomorphism (filter p)
-}
{- $prop-morphism-fromList
#p:prop-morphism-fromList#

[prop-morphism-fromList]:
    'Data.Bag.fromList' is a monoid homomorphism.
    
    > prop-morphism-fromList
    >   : Monoid.IsHomomorphism (fromList {a})
-}
{- $prop-morphism-map
#p:prop-morphism-map#

[prop-morphism-map]:
    'Data.Bag.map' is a monoid homomorphism.
    
    > prop-morphism-map
    >   : ∀ (f : a → b) → Monoid.IsHomomorphism (map f)
-}
{- $prop-morphism-mmember
#p:prop-morphism-mmember#

[prop-morphism-mmember]:
    'Data.Bag.member' is a monoid homomorphism.
    
    > prop-morphism-mmember
    >   : ∀ ⦃ _ : Eq a ⦄ (x : a)
    >   → Monoid.IsHomomorphism ⦃ iMonoidBag {a} ⦄ (mmember x)
-}
{- $prop-morphism-mnull
#p:prop-morphism-mnull#

[prop-morphism-mnull]:
    'Data.Bag.mnull' is a monoid homomorphism.
    
    > prop-morphism-mnull
    >   : Monoid.IsHomomorphism ⦃ iMonoidBag {a} ⦄ mnull
-}
{- $prop-morphism-msize
#p:prop-morphism-msize#

[prop-morphism-msize]:
    'Data.Bag.msize' is a monoid homomorphism.
    
    > prop-morphism-msize
    >   : Monoid.IsHomomorphism ⦃ iMonoidBag {a} ⦄ msize
-}
{- $prop-null-cartesianProduct
#p:prop-null-cartesianProduct#

[prop-null-cartesianProduct]:
    A 'Data.Bag.cartesianProduct' is empty
    if and only if both arguments are empty.
    
    > prop-null-cartesianProduct
    >   : ∀ (xs : Bag a) (ys : Bag b)
    >   → null (cartesianProduct xs ys) ≡ (null xs || null ys)
-}
{- $prop-null-singleton
#p:prop-null-singleton#

[prop-null-singleton]:
    The 'Data.Bag.singleton' 'Data.Bag.Bag' is not empty.
    
    > prop-null-singleton
    >   : ∀ (x : a) → null (singleton x) ≡ False
-}
{- $prop-size-<>
#p:prop-size-<>#

[prop-size-<>]:
    The union of 'Data.Bag.Bag's adds their sizes.
    
    > prop-size-<>
    >   : ∀ (xs ys : Bag a) → size (xs <> ys) ≡ size xs + size ys
-}
{- $prop-size-fromList
#p:prop-size-fromList#

[prop-size-fromList]:
    'Data.Bag.fromList' preserves list length.
    
    > prop-size-fromList
    >   : ∀ (xs : List a)
    >   → size (fromList xs) ≡ length xs
-}
{- $prop-size-mempty
#p:prop-size-mempty#

[prop-size-mempty]:
    The empty 'Data.Bag.Bag' has @'size' = 0@.
    
    > prop-size-mempty
    >   : ∀ {a} → size {a} mempty ≡ 0
-}
{- $prop-size-singleton
#p:prop-size-singleton#

[prop-size-singleton]:
    The 'Data.Bag.singleton' 'Data.Bag.Bag' has @'size' = 1@.
    
    > prop-size-singleton
    >   : ∀ (x : a) → size (singleton x) ≡ 1
-}
