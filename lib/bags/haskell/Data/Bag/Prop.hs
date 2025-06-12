module Data.Bag.Prop 
    (
    -- * Query
    -- ** null
    -- $prop-morphism-mnull
    
    -- ** size
    -- $prop-size-mempty
    
    -- $prop-size-singleton
    
    -- $prop-size-<>
    
    -- $prop-morphism-msize
    
    -- ** member
    -- $prop-morphism-mmember
    
    -- * Construction
    -- ** fromList
    -- $prop-fromList-empty
    
    -- $prop-fromList-++
    
    -- $prop-size-fromList
    
    -- $prop-fromList-filter
    
    -- * Combine
    -- ** cartesianProduct
    -- $prop-morphism-cartesianProduct-1
    
    -- $prop-morphism-cartesianProduct-2
    
    -- $prop-null-cartesianProduct
    
    -- $prop-filter-cartesianProduct
    
    -- ** equijoin
    -- $prop-morphism-equijoin-1
    
    -- $prop-morphism-equijoin-2
    
    -- * Traversal
    -- ** filter
    -- $prop-morphism-filter
    
    )
    where

import Prelude hiding (null, filter, lookup, map, concatMap)

dummy :: ()
dummy = ()

-- * Properties
{- $prop-filter-cartesianProduct
#p:prop-filter-cartesianProduct#

[prop-filter-cartesianProduct]:
    Independent filters promote through cartesian product.
    
    > prop-filter-cartesianProduct
    >   : ∀ (p : a → Bool) (q : b → Bool) (xs : Bag a) (ys : Bag b)
    >   → filter (λ xy → p (fst xy) && q (snd xy)) (cartesianProduct xs ys)
    >     ≡ cartesianProduct (filter p xs) (filter q ys)
-}
{- $prop-fromList-++
#p:prop-fromList-++#

[prop-fromList-++]:
    'fromList' maps list concatenation to 'union' of 'Bag's.
    
    > prop-fromList-++
    >   : ∀ (xs ys : List a) 
    >   → fromList (xs ++ ys) ≡ fromList xs <> fromList ys
-}
{- $prop-fromList-empty
#p:prop-fromList-empty#

[prop-fromList-empty]:
    'fromList' maps single element lists to singleton
    
    > prop-fromList-empty : ∀ {a} → fromList {a} [] ≡ mempty
-}
{- $prop-fromList-filter
#p:prop-fromList-filter#

[prop-fromList-filter]:
    'fromList' maps 'Data.List.filter' to 'filter'.
    
    > prop-fromList-filter
    >   : ∀ (p : a → Bool) (xs : List a) 
    >   → fromList (List.filter p xs) ≡ filter p (fromList xs)
-}
{- $prop-morphism-cartesianProduct-1
#p:prop-morphism-cartesianProduct-1#

[prop-morphism-cartesianProduct-1]:
    'cartesianProduct' is a monoid homomorphism in its first argument.
    
    > prop-morphism-cartesianProduct-1
    >   : ∀ (ys : Bag b)
    >   → Monoid.IsHomomorphism (λ xs → cartesianProduct {a} {b} xs ys)
-}
{- $prop-morphism-cartesianProduct-2
#p:prop-morphism-cartesianProduct-2#

[prop-morphism-cartesianProduct-2]:
    'cartesianProduct' is a monoid homomorphism in its second argument.
    
    > prop-morphism-cartesianProduct-2
    >   : ∀ (xs : Bag a)
    >   → Monoid.IsHomomorphism (λ (ys : Bag b) → cartesianProduct {a} {b} xs ys)
-}
{- $prop-morphism-equijoin-1
#p:prop-morphism-equijoin-1#

[prop-morphism-equijoin-1]:
    'equijoin' is a monoid homomorphism in its first argument.
    
    > prop-morphism-equijoin-1
    >   : ∀ {k} ⦃ _ : Eq k ⦄ (f : a → k) (g : b → k) (ys : Bag b)
    >   → Monoid.IsHomomorphism (λ xs → equijoin f g xs ys)
-}
{- $prop-morphism-equijoin-2
#p:prop-morphism-equijoin-2#

[prop-morphism-equijoin-2]:
    'equijoin' is a monoid homomorphism in its second argument.
    
    > prop-morphism-equijoin-2
    >   : ∀ {k} ⦃ _ : Eq k ⦄ (f : a → k) (g : b → k) (xs : Bag a)
    >   → Monoid.IsHomomorphism (λ ys → equijoin f g xs ys)
-}
{- $prop-morphism-filter
#p:prop-morphism-filter#

[prop-morphism-filter]:
    'filter' is a monoid homomorphism.
    
    > prop-morphism-filter
    >   : ∀ (p : a → Bool) → Monoid.IsHomomorphism (filter p)
-}
{- $prop-morphism-fromList
#p:prop-morphism-fromList#

[prop-morphism-fromList]:
    'fromList' is a monoid homomorphism.
    
    > prop-morphism-fromList
    >   : Monoid.IsHomomorphism (fromList {a})
-}
{- $prop-morphism-mmember
#p:prop-morphism-mmember#

[prop-morphism-mmember]:
    'member' is a monoid homomorphism.
    
    > prop-morphism-mmember
    >   : ∀ ⦃ _ : Eq a ⦄ (x : a)
    >   → Monoid.IsHomomorphism ⦃ iMonoidBag {a} ⦄ (mmember x)
-}
{- $prop-morphism-mnull
#p:prop-morphism-mnull#

[prop-morphism-mnull]:
    'null' is a monoid homomorphism.
    
    > prop-morphism-mnull
    >   : Monoid.IsHomomorphism ⦃ iMonoidBag {a} ⦄ mnull
-}
{- $prop-morphism-msize
#p:prop-morphism-msize#

[prop-morphism-msize]:
    'size' is a monoid homomorphism.
    
    > prop-morphism-msize
    >   : Monoid.IsHomomorphism ⦃ iMonoidBag {a} ⦄ msize
-}
{- $prop-null-cartesianProduct
#p:prop-null-cartesianProduct#

[prop-null-cartesianProduct]:
    A 'cartesianProduct' is empty if and only if both arguments are empty.
    
    > prop-null-cartesianProduct
    >   : ∀ (xs : Bag a) (ys : Bag b)
    >   → null (cartesianProduct xs ys) ≡ (null xs || null ys)
-}
{- $prop-size-<>
#p:prop-size-<>#

[prop-size-<>]:
    The union of 'Bags' adds their sizes.
    
    > prop-size-<>
    >   : ∀ (xs ys : Bag a) → size (xs <> ys) ≡ size xs + size ys
-}
{- $prop-size-fromList
#p:prop-size-fromList#

[prop-size-fromList]:
    'fromList' preserves list length.
    
    > prop-size-fromList
    >   : ∀ (xs : List a)
    >   → size (fromList xs) ≡ length xs
-}
{- $prop-size-mempty
#p:prop-size-mempty#

[prop-size-mempty]:
    The empty 'Bag' has @'size' = 0@.
    
    > prop-size-mempty
    >   : ∀ {a} → size {a} mempty ≡ 0
-}
{- $prop-size-singleton
#p:prop-size-singleton#

[prop-size-singleton]:
    The 'singleton' 'Bag' has @'size' = 1@.
    
    > prop-size-singleton
    >   : ∀ (x : a) → size (singleton x) ≡ 1
-}
-- * Properties
{- $prop-filter-cartesianProduct
#p:prop-filter-cartesianProduct#

[prop-filter-cartesianProduct]:
    Independent filters promote through cartesian product.
    
    > prop-filter-cartesianProduct
    >   : ∀ (p : a → Bool) (q : b → Bool) (xs : Bag a) (ys : Bag b)
    >   → filter (λ xy → p (fst xy) && q (snd xy)) (cartesianProduct xs ys)
    >     ≡ cartesianProduct (filter p xs) (filter q ys)
-}
{- $prop-fromList-++
#p:prop-fromList-++#

[prop-fromList-++]:
    'fromList' maps list concatenation to 'union' of 'Bag's.
    
    > prop-fromList-++
    >   : ∀ (xs ys : List a) 
    >   → fromList (xs ++ ys) ≡ fromList xs <> fromList ys
-}
{- $prop-fromList-empty
#p:prop-fromList-empty#

[prop-fromList-empty]:
    'fromList' maps single element lists to singleton
    
    > prop-fromList-empty : ∀ {a} → fromList {a} [] ≡ mempty
-}
{- $prop-fromList-filter
#p:prop-fromList-filter#

[prop-fromList-filter]:
    'fromList' maps 'Data.List.filter' to 'filter'.
    
    > prop-fromList-filter
    >   : ∀ (p : a → Bool) (xs : List a) 
    >   → fromList (List.filter p xs) ≡ filter p (fromList xs)
-}
{- $prop-morphism-cartesianProduct-1
#p:prop-morphism-cartesianProduct-1#

[prop-morphism-cartesianProduct-1]:
    'cartesianProduct' is a monoid homomorphism in its first argument.
    
    > prop-morphism-cartesianProduct-1
    >   : ∀ (ys : Bag b)
    >   → Monoid.IsHomomorphism (λ xs → cartesianProduct {a} {b} xs ys)
-}
{- $prop-morphism-cartesianProduct-2
#p:prop-morphism-cartesianProduct-2#

[prop-morphism-cartesianProduct-2]:
    'cartesianProduct' is a monoid homomorphism in its second argument.
    
    > prop-morphism-cartesianProduct-2
    >   : ∀ (xs : Bag a)
    >   → Monoid.IsHomomorphism (λ (ys : Bag b) → cartesianProduct {a} {b} xs ys)
-}
{- $prop-morphism-equijoin-1
#p:prop-morphism-equijoin-1#

[prop-morphism-equijoin-1]:
    'equijoin' is a monoid homomorphism in its first argument.
    
    > prop-morphism-equijoin-1
    >   : ∀ {k} ⦃ _ : Eq k ⦄ (f : a → k) (g : b → k) (ys : Bag b)
    >   → Monoid.IsHomomorphism (λ xs → equijoin f g xs ys)
-}
{- $prop-morphism-equijoin-2
#p:prop-morphism-equijoin-2#

[prop-morphism-equijoin-2]:
    'equijoin' is a monoid homomorphism in its second argument.
    
    > prop-morphism-equijoin-2
    >   : ∀ {k} ⦃ _ : Eq k ⦄ (f : a → k) (g : b → k) (xs : Bag a)
    >   → Monoid.IsHomomorphism (λ ys → equijoin f g xs ys)
-}
{- $prop-morphism-filter
#p:prop-morphism-filter#

[prop-morphism-filter]:
    'filter' is a monoid homomorphism.
    
    > prop-morphism-filter
    >   : ∀ (p : a → Bool) → Monoid.IsHomomorphism (filter p)
-}
{- $prop-morphism-fromList
#p:prop-morphism-fromList#

[prop-morphism-fromList]:
    'fromList' is a monoid homomorphism.
    
    > prop-morphism-fromList
    >   : Monoid.IsHomomorphism (fromList {a})
-}
{- $prop-morphism-mmember
#p:prop-morphism-mmember#

[prop-morphism-mmember]:
    'member' is a monoid homomorphism.
    
    > prop-morphism-mmember
    >   : ∀ ⦃ _ : Eq a ⦄ (x : a)
    >   → Monoid.IsHomomorphism ⦃ iMonoidBag {a} ⦄ (mmember x)
-}
{- $prop-morphism-mnull
#p:prop-morphism-mnull#

[prop-morphism-mnull]:
    'null' is a monoid homomorphism.
    
    > prop-morphism-mnull
    >   : Monoid.IsHomomorphism ⦃ iMonoidBag {a} ⦄ mnull
-}
{- $prop-morphism-msize
#p:prop-morphism-msize#

[prop-morphism-msize]:
    'size' is a monoid homomorphism.
    
    > prop-morphism-msize
    >   : Monoid.IsHomomorphism ⦃ iMonoidBag {a} ⦄ msize
-}
{- $prop-null-cartesianProduct
#p:prop-null-cartesianProduct#

[prop-null-cartesianProduct]:
    A 'cartesianProduct' is empty if and only if both arguments are empty.
    
    > prop-null-cartesianProduct
    >   : ∀ (xs : Bag a) (ys : Bag b)
    >   → null (cartesianProduct xs ys) ≡ (null xs || null ys)
-}
{- $prop-size-<>
#p:prop-size-<>#

[prop-size-<>]:
    The union of 'Bags' adds their sizes.
    
    > prop-size-<>
    >   : ∀ (xs ys : Bag a) → size (xs <> ys) ≡ size xs + size ys
-}
{- $prop-size-fromList
#p:prop-size-fromList#

[prop-size-fromList]:
    'fromList' preserves list length.
    
    > prop-size-fromList
    >   : ∀ (xs : List a)
    >   → size (fromList xs) ≡ length xs
-}
{- $prop-size-mempty
#p:prop-size-mempty#

[prop-size-mempty]:
    The empty 'Bag' has @'size' = 0@.
    
    > prop-size-mempty
    >   : ∀ {a} → size {a} mempty ≡ 0
-}
{- $prop-size-singleton
#p:prop-size-singleton#

[prop-size-singleton]:
    The 'singleton' 'Bag' has @'size' = 1@.
    
    > prop-size-singleton
    >   : ∀ (x : a) → size (singleton x) ≡ 1
-}
-- * Properties
{- $prop-filter-cartesianProduct
#p:prop-filter-cartesianProduct#

[prop-filter-cartesianProduct]:
    Independent filters promote through cartesian product.
    
    > prop-filter-cartesianProduct
    >   : ∀ (p : a → Bool) (q : b → Bool) (xs : Bag a) (ys : Bag b)
    >   → filter (λ xy → p (fst xy) && q (snd xy)) (cartesianProduct xs ys)
    >     ≡ cartesianProduct (filter p xs) (filter q ys)
-}
{- $prop-fromList-++
#p:prop-fromList-++#

[prop-fromList-++]:
    'fromList' maps list concatenation to 'union' of 'Bag's.
    
    > prop-fromList-++
    >   : ∀ (xs ys : List a) 
    >   → fromList (xs ++ ys) ≡ fromList xs <> fromList ys
-}
{- $prop-fromList-empty
#p:prop-fromList-empty#

[prop-fromList-empty]:
    'fromList' maps single element lists to singleton
    
    > prop-fromList-empty : ∀ {a} → fromList {a} [] ≡ mempty
-}
{- $prop-fromList-filter
#p:prop-fromList-filter#

[prop-fromList-filter]:
    'fromList' maps 'Data.List.filter' to 'filter'.
    
    > prop-fromList-filter
    >   : ∀ (p : a → Bool) (xs : List a) 
    >   → fromList (List.filter p xs) ≡ filter p (fromList xs)
-}
{- $prop-morphism-cartesianProduct-1
#p:prop-morphism-cartesianProduct-1#

[prop-morphism-cartesianProduct-1]:
    'cartesianProduct' is a monoid homomorphism in its first argument.
    
    > prop-morphism-cartesianProduct-1
    >   : ∀ (ys : Bag b)
    >   → Monoid.IsHomomorphism (λ xs → cartesianProduct {a} {b} xs ys)
-}
{- $prop-morphism-cartesianProduct-2
#p:prop-morphism-cartesianProduct-2#

[prop-morphism-cartesianProduct-2]:
    'cartesianProduct' is a monoid homomorphism in its second argument.
    
    > prop-morphism-cartesianProduct-2
    >   : ∀ (xs : Bag a)
    >   → Monoid.IsHomomorphism (λ (ys : Bag b) → cartesianProduct {a} {b} xs ys)
-}
{- $prop-morphism-equijoin-1
#p:prop-morphism-equijoin-1#

[prop-morphism-equijoin-1]:
    'equijoin' is a monoid homomorphism in its first argument.
    
    > prop-morphism-equijoin-1
    >   : ∀ {k} ⦃ _ : Eq k ⦄ (f : a → k) (g : b → k) (ys : Bag b)
    >   → Monoid.IsHomomorphism (λ xs → equijoin f g xs ys)
-}
{- $prop-morphism-equijoin-2
#p:prop-morphism-equijoin-2#

[prop-morphism-equijoin-2]:
    'equijoin' is a monoid homomorphism in its second argument.
    
    > prop-morphism-equijoin-2
    >   : ∀ {k} ⦃ _ : Eq k ⦄ (f : a → k) (g : b → k) (xs : Bag a)
    >   → Monoid.IsHomomorphism (λ ys → equijoin f g xs ys)
-}
{- $prop-morphism-filter
#p:prop-morphism-filter#

[prop-morphism-filter]:
    'filter' is a monoid homomorphism.
    
    > prop-morphism-filter
    >   : ∀ (p : a → Bool) → Monoid.IsHomomorphism (filter p)
-}
{- $prop-morphism-fromList
#p:prop-morphism-fromList#

[prop-morphism-fromList]:
    'fromList' is a monoid homomorphism.
    
    > prop-morphism-fromList
    >   : Monoid.IsHomomorphism (fromList {a})
-}
{- $prop-morphism-mmember
#p:prop-morphism-mmember#

[prop-morphism-mmember]:
    'member' is a monoid homomorphism.
    
    > prop-morphism-mmember
    >   : ∀ ⦃ _ : Eq a ⦄ (x : a)
    >   → Monoid.IsHomomorphism ⦃ iMonoidBag {a} ⦄ (mmember x)
-}
{- $prop-morphism-mnull
#p:prop-morphism-mnull#

[prop-morphism-mnull]:
    'null' is a monoid homomorphism.
    
    > prop-morphism-mnull
    >   : Monoid.IsHomomorphism ⦃ iMonoidBag {a} ⦄ mnull
-}
{- $prop-morphism-msize
#p:prop-morphism-msize#

[prop-morphism-msize]:
    'size' is a monoid homomorphism.
    
    > prop-morphism-msize
    >   : Monoid.IsHomomorphism ⦃ iMonoidBag {a} ⦄ msize
-}
{- $prop-null-cartesianProduct
#p:prop-null-cartesianProduct#

[prop-null-cartesianProduct]:
    A 'cartesianProduct' is empty if and only if both arguments are empty.
    
    > prop-null-cartesianProduct
    >   : ∀ (xs : Bag a) (ys : Bag b)
    >   → null (cartesianProduct xs ys) ≡ (null xs || null ys)
-}
{- $prop-size-<>
#p:prop-size-<>#

[prop-size-<>]:
    The union of 'Bags' adds their sizes.
    
    > prop-size-<>
    >   : ∀ (xs ys : Bag a) → size (xs <> ys) ≡ size xs + size ys
-}
{- $prop-size-fromList
#p:prop-size-fromList#

[prop-size-fromList]:
    'fromList' preserves list length.
    
    > prop-size-fromList
    >   : ∀ (xs : List a)
    >   → size (fromList xs) ≡ length xs
-}
{- $prop-size-mempty
#p:prop-size-mempty#

[prop-size-mempty]:
    The empty 'Bag' has @'size' = 0@.
    
    > prop-size-mempty
    >   : ∀ {a} → size {a} mempty ≡ 0
-}
{- $prop-size-singleton
#p:prop-size-singleton#

[prop-size-singleton]:
    The 'singleton' 'Bag' has @'size' = 1@.
    
    > prop-size-singleton
    >   : ∀ (x : a) → size (singleton x) ≡ 1
-}
-- * Properties
{- $prop-filter-cartesianProduct
#p:prop-filter-cartesianProduct#

[prop-filter-cartesianProduct]:
    Independent filters promote through cartesian product.
    
    > prop-filter-cartesianProduct
    >   : ∀ (p : a → Bool) (q : b → Bool) (xs : Bag a) (ys : Bag b)
    >   → filter (λ xy → p (fst xy) && q (snd xy)) (cartesianProduct xs ys)
    >     ≡ cartesianProduct (filter p xs) (filter q ys)
-}
{- $prop-fromList-++
#p:prop-fromList-++#

[prop-fromList-++]:
    'fromList' maps list concatenation to 'union' of 'Bag's.
    
    > prop-fromList-++
    >   : ∀ (xs ys : List a) 
    >   → fromList (xs ++ ys) ≡ fromList xs <> fromList ys
-}
{- $prop-fromList-empty
#p:prop-fromList-empty#

[prop-fromList-empty]:
    'fromList' maps single element lists to singleton
    
    > prop-fromList-empty : ∀ {a} → fromList {a} [] ≡ mempty
-}
{- $prop-fromList-filter
#p:prop-fromList-filter#

[prop-fromList-filter]:
    'fromList' maps 'Data.List.filter' to 'filter'.
    
    > prop-fromList-filter
    >   : ∀ (p : a → Bool) (xs : List a) 
    >   → fromList (List.filter p xs) ≡ filter p (fromList xs)
-}
{- $prop-morphism-cartesianProduct-1
#p:prop-morphism-cartesianProduct-1#

[prop-morphism-cartesianProduct-1]:
    'cartesianProduct' is a monoid homomorphism in its first argument.
    
    > prop-morphism-cartesianProduct-1
    >   : ∀ (ys : Bag b)
    >   → Monoid.IsHomomorphism (λ xs → cartesianProduct {a} {b} xs ys)
-}
{- $prop-morphism-cartesianProduct-2
#p:prop-morphism-cartesianProduct-2#

[prop-morphism-cartesianProduct-2]:
    'cartesianProduct' is a monoid homomorphism in its second argument.
    
    > prop-morphism-cartesianProduct-2
    >   : ∀ (xs : Bag a)
    >   → Monoid.IsHomomorphism (λ (ys : Bag b) → cartesianProduct {a} {b} xs ys)
-}
{- $prop-morphism-equijoin-1
#p:prop-morphism-equijoin-1#

[prop-morphism-equijoin-1]:
    'equijoin' is a monoid homomorphism in its first argument.
    
    > prop-morphism-equijoin-1
    >   : ∀ {k} ⦃ _ : Eq k ⦄ (f : a → k) (g : b → k) (ys : Bag b)
    >   → Monoid.IsHomomorphism (λ xs → equijoin f g xs ys)
-}
{- $prop-morphism-equijoin-2
#p:prop-morphism-equijoin-2#

[prop-morphism-equijoin-2]:
    'equijoin' is a monoid homomorphism in its second argument.
    
    > prop-morphism-equijoin-2
    >   : ∀ {k} ⦃ _ : Eq k ⦄ (f : a → k) (g : b → k) (xs : Bag a)
    >   → Monoid.IsHomomorphism (λ ys → equijoin f g xs ys)
-}
{- $prop-morphism-filter
#p:prop-morphism-filter#

[prop-morphism-filter]:
    'filter' is a monoid homomorphism.
    
    > prop-morphism-filter
    >   : ∀ (p : a → Bool) → Monoid.IsHomomorphism (filter p)
-}
{- $prop-morphism-fromList
#p:prop-morphism-fromList#

[prop-morphism-fromList]:
    'fromList' is a monoid homomorphism.
    
    > prop-morphism-fromList
    >   : Monoid.IsHomomorphism (fromList {a})
-}
{- $prop-morphism-mmember
#p:prop-morphism-mmember#

[prop-morphism-mmember]:
    'member' is a monoid homomorphism.
    
    > prop-morphism-mmember
    >   : ∀ ⦃ _ : Eq a ⦄ (x : a)
    >   → Monoid.IsHomomorphism ⦃ iMonoidBag {a} ⦄ (mmember x)
-}
{- $prop-morphism-mnull
#p:prop-morphism-mnull#

[prop-morphism-mnull]:
    'null' is a monoid homomorphism.
    
    > prop-morphism-mnull
    >   : Monoid.IsHomomorphism ⦃ iMonoidBag {a} ⦄ mnull
-}
{- $prop-morphism-msize
#p:prop-morphism-msize#

[prop-morphism-msize]:
    'size' is a monoid homomorphism.
    
    > prop-morphism-msize
    >   : Monoid.IsHomomorphism ⦃ iMonoidBag {a} ⦄ msize
-}
{- $prop-null-cartesianProduct
#p:prop-null-cartesianProduct#

[prop-null-cartesianProduct]:
    A 'cartesianProduct' is empty if and only if both arguments are empty.
    
    > prop-null-cartesianProduct
    >   : ∀ (xs : Bag a) (ys : Bag b)
    >   → null (cartesianProduct xs ys) ≡ (null xs || null ys)
-}
{- $prop-size-<>
#p:prop-size-<>#

[prop-size-<>]:
    The union of 'Bags' adds their sizes.
    
    > prop-size-<>
    >   : ∀ (xs ys : Bag a) → size (xs <> ys) ≡ size xs + size ys
-}
{- $prop-size-fromList
#p:prop-size-fromList#

[prop-size-fromList]:
    'fromList' preserves list length.
    
    > prop-size-fromList
    >   : ∀ (xs : List a)
    >   → size (fromList xs) ≡ length xs
-}
{- $prop-size-mempty
#p:prop-size-mempty#

[prop-size-mempty]:
    The empty 'Bag' has @'size' = 0@.
    
    > prop-size-mempty
    >   : ∀ {a} → size {a} mempty ≡ 0
-}
{- $prop-size-singleton
#p:prop-size-singleton#

[prop-size-singleton]:
    The 'singleton' 'Bag' has @'size' = 1@.
    
    > prop-size-singleton
    >   : ∀ (x : a) → size (singleton x) ≡ 1
-}
-- * Properties
{- $prop-filter-cartesianProduct
#p:prop-filter-cartesianProduct#

[prop-filter-cartesianProduct]:
    Independent filters promote through cartesian product.
    
    > prop-filter-cartesianProduct
    >   : ∀ (p : a → Bool) (q : b → Bool) (xs : Bag a) (ys : Bag b)
    >   → filter (λ xy → p (fst xy) && q (snd xy)) (cartesianProduct xs ys)
    >     ≡ cartesianProduct (filter p xs) (filter q ys)
-}
{- $prop-fromList-++
#p:prop-fromList-++#

[prop-fromList-++]:
    'fromList' maps list concatenation to 'union' of 'Bag's.
    
    > prop-fromList-++
    >   : ∀ (xs ys : List a) 
    >   → fromList (xs ++ ys) ≡ fromList xs <> fromList ys
-}
{- $prop-fromList-empty
#p:prop-fromList-empty#

[prop-fromList-empty]:
    'fromList' maps single element lists to singleton
    
    > prop-fromList-empty : ∀ {a} → fromList {a} [] ≡ mempty
-}
{- $prop-fromList-filter
#p:prop-fromList-filter#

[prop-fromList-filter]:
    'fromList' maps 'Data.List.filter' to 'filter'.
    
    > prop-fromList-filter
    >   : ∀ (p : a → Bool) (xs : List a) 
    >   → fromList (List.filter p xs) ≡ filter p (fromList xs)
-}
{- $prop-morphism-cartesianProduct-1
#p:prop-morphism-cartesianProduct-1#

[prop-morphism-cartesianProduct-1]:
    'cartesianProduct' is a monoid homomorphism in its first argument.
    
    > prop-morphism-cartesianProduct-1
    >   : ∀ (ys : Bag b)
    >   → Monoid.IsHomomorphism (λ xs → cartesianProduct {a} {b} xs ys)
-}
{- $prop-morphism-cartesianProduct-2
#p:prop-morphism-cartesianProduct-2#

[prop-morphism-cartesianProduct-2]:
    'cartesianProduct' is a monoid homomorphism in its second argument.
    
    > prop-morphism-cartesianProduct-2
    >   : ∀ (xs : Bag a)
    >   → Monoid.IsHomomorphism (λ (ys : Bag b) → cartesianProduct {a} {b} xs ys)
-}
{- $prop-morphism-equijoin-1
#p:prop-morphism-equijoin-1#

[prop-morphism-equijoin-1]:
    'equijoin' is a monoid homomorphism in its first argument.
    
    > prop-morphism-equijoin-1
    >   : ∀ {k} ⦃ _ : Eq k ⦄ (f : a → k) (g : b → k) (ys : Bag b)
    >   → Monoid.IsHomomorphism (λ xs → equijoin f g xs ys)
-}
{- $prop-morphism-equijoin-2
#p:prop-morphism-equijoin-2#

[prop-morphism-equijoin-2]:
    'equijoin' is a monoid homomorphism in its second argument.
    
    > prop-morphism-equijoin-2
    >   : ∀ {k} ⦃ _ : Eq k ⦄ (f : a → k) (g : b → k) (xs : Bag a)
    >   → Monoid.IsHomomorphism (λ ys → equijoin f g xs ys)
-}
{- $prop-morphism-filter
#p:prop-morphism-filter#

[prop-morphism-filter]:
    'filter' is a monoid homomorphism.
    
    > prop-morphism-filter
    >   : ∀ (p : a → Bool) → Monoid.IsHomomorphism (filter p)
-}
{- $prop-morphism-fromList
#p:prop-morphism-fromList#

[prop-morphism-fromList]:
    'fromList' is a monoid homomorphism.
    
    > prop-morphism-fromList
    >   : Monoid.IsHomomorphism (fromList {a})
-}
{- $prop-morphism-mmember
#p:prop-morphism-mmember#

[prop-morphism-mmember]:
    'member' is a monoid homomorphism.
    
    > prop-morphism-mmember
    >   : ∀ ⦃ _ : Eq a ⦄ (x : a)
    >   → Monoid.IsHomomorphism ⦃ iMonoidBag {a} ⦄ (mmember x)
-}
{- $prop-morphism-mnull
#p:prop-morphism-mnull#

[prop-morphism-mnull]:
    'null' is a monoid homomorphism.
    
    > prop-morphism-mnull
    >   : Monoid.IsHomomorphism ⦃ iMonoidBag {a} ⦄ mnull
-}
{- $prop-morphism-msize
#p:prop-morphism-msize#

[prop-morphism-msize]:
    'size' is a monoid homomorphism.
    
    > prop-morphism-msize
    >   : Monoid.IsHomomorphism ⦃ iMonoidBag {a} ⦄ msize
-}
{- $prop-null-cartesianProduct
#p:prop-null-cartesianProduct#

[prop-null-cartesianProduct]:
    A 'cartesianProduct' is empty if and only if both arguments are empty.
    
    > prop-null-cartesianProduct
    >   : ∀ (xs : Bag a) (ys : Bag b)
    >   → null (cartesianProduct xs ys) ≡ (null xs || null ys)
-}
{- $prop-size-<>
#p:prop-size-<>#

[prop-size-<>]:
    The union of 'Bags' adds their sizes.
    
    > prop-size-<>
    >   : ∀ (xs ys : Bag a) → size (xs <> ys) ≡ size xs + size ys
-}
{- $prop-size-fromList
#p:prop-size-fromList#

[prop-size-fromList]:
    'fromList' preserves list length.
    
    > prop-size-fromList
    >   : ∀ (xs : List a)
    >   → size (fromList xs) ≡ length xs
-}
{- $prop-size-mempty
#p:prop-size-mempty#

[prop-size-mempty]:
    The empty 'Bag' has @'size' = 0@.
    
    > prop-size-mempty
    >   : ∀ {a} → size {a} mempty ≡ 0
-}
{- $prop-size-singleton
#p:prop-size-singleton#

[prop-size-singleton]:
    The 'singleton' 'Bag' has @'size' = 1@.
    
    > prop-size-singleton
    >   : ∀ (x : a) → size (singleton x) ≡ 1
-}
-- * Properties
{- $prop-filter-cartesianProduct
#p:prop-filter-cartesianProduct#

[prop-filter-cartesianProduct]:
    Independent filters promote through cartesian product.
    
    > prop-filter-cartesianProduct
    >   : ∀ (p : a → Bool) (q : b → Bool) (xs : Bag a) (ys : Bag b)
    >   → filter (λ xy → p (fst xy) && q (snd xy)) (cartesianProduct xs ys)
    >     ≡ cartesianProduct (filter p xs) (filter q ys)
-}
{- $prop-fromList-++
#p:prop-fromList-++#

[prop-fromList-++]:
    'fromList' maps list concatenation to 'union' of 'Bag's.
    
    > prop-fromList-++
    >   : ∀ (xs ys : List a) 
    >   → fromList (xs ++ ys) ≡ fromList xs <> fromList ys
-}
{- $prop-fromList-empty
#p:prop-fromList-empty#

[prop-fromList-empty]:
    'fromList' maps single element lists to singleton
    
    > prop-fromList-empty : ∀ {a} → fromList {a} [] ≡ mempty
-}
{- $prop-fromList-filter
#p:prop-fromList-filter#

[prop-fromList-filter]:
    'fromList' maps 'Data.List.filter' to 'filter'.
    
    > prop-fromList-filter
    >   : ∀ (p : a → Bool) (xs : List a) 
    >   → fromList (List.filter p xs) ≡ filter p (fromList xs)
-}
{- $prop-morphism-cartesianProduct-1
#p:prop-morphism-cartesianProduct-1#

[prop-morphism-cartesianProduct-1]:
    'cartesianProduct' is a monoid homomorphism in its first argument.
    
    > prop-morphism-cartesianProduct-1
    >   : ∀ (ys : Bag b)
    >   → Monoid.IsHomomorphism (λ xs → cartesianProduct {a} {b} xs ys)
-}
{- $prop-morphism-cartesianProduct-2
#p:prop-morphism-cartesianProduct-2#

[prop-morphism-cartesianProduct-2]:
    'cartesianProduct' is a monoid homomorphism in its second argument.
    
    > prop-morphism-cartesianProduct-2
    >   : ∀ (xs : Bag a)
    >   → Monoid.IsHomomorphism (λ (ys : Bag b) → cartesianProduct {a} {b} xs ys)
-}
{- $prop-morphism-equijoin-1
#p:prop-morphism-equijoin-1#

[prop-morphism-equijoin-1]:
    'equijoin' is a monoid homomorphism in its first argument.
    
    > prop-morphism-equijoin-1
    >   : ∀ {k} ⦃ _ : Eq k ⦄ (f : a → k) (g : b → k) (ys : Bag b)
    >   → Monoid.IsHomomorphism (λ xs → equijoin f g xs ys)
-}
{- $prop-morphism-equijoin-2
#p:prop-morphism-equijoin-2#

[prop-morphism-equijoin-2]:
    'equijoin' is a monoid homomorphism in its second argument.
    
    > prop-morphism-equijoin-2
    >   : ∀ {k} ⦃ _ : Eq k ⦄ (f : a → k) (g : b → k) (xs : Bag a)
    >   → Monoid.IsHomomorphism (λ ys → equijoin f g xs ys)
-}
{- $prop-morphism-filter
#p:prop-morphism-filter#

[prop-morphism-filter]:
    'filter' is a monoid homomorphism.
    
    > prop-morphism-filter
    >   : ∀ (p : a → Bool) → Monoid.IsHomomorphism (filter p)
-}
{- $prop-morphism-fromList
#p:prop-morphism-fromList#

[prop-morphism-fromList]:
    'fromList' is a monoid homomorphism.
    
    > prop-morphism-fromList
    >   : Monoid.IsHomomorphism (fromList {a})
-}
{- $prop-morphism-mmember
#p:prop-morphism-mmember#

[prop-morphism-mmember]:
    'member' is a monoid homomorphism.
    
    > prop-morphism-mmember
    >   : ∀ ⦃ _ : Eq a ⦄ (x : a)
    >   → Monoid.IsHomomorphism ⦃ iMonoidBag {a} ⦄ (mmember x)
-}
{- $prop-morphism-mnull
#p:prop-morphism-mnull#

[prop-morphism-mnull]:
    'null' is a monoid homomorphism.
    
    > prop-morphism-mnull
    >   : Monoid.IsHomomorphism ⦃ iMonoidBag {a} ⦄ mnull
-}
{- $prop-morphism-msize
#p:prop-morphism-msize#

[prop-morphism-msize]:
    'size' is a monoid homomorphism.
    
    > prop-morphism-msize
    >   : Monoid.IsHomomorphism ⦃ iMonoidBag {a} ⦄ msize
-}
{- $prop-null-cartesianProduct
#p:prop-null-cartesianProduct#

[prop-null-cartesianProduct]:
    A 'cartesianProduct' is empty if and only if both arguments are empty.
    
    > prop-null-cartesianProduct
    >   : ∀ (xs : Bag a) (ys : Bag b)
    >   → null (cartesianProduct xs ys) ≡ (null xs || null ys)
-}
{- $prop-size-<>
#p:prop-size-<>#

[prop-size-<>]:
    The union of 'Bags' adds their sizes.
    
    > prop-size-<>
    >   : ∀ (xs ys : Bag a) → size (xs <> ys) ≡ size xs + size ys
-}
{- $prop-size-fromList
#p:prop-size-fromList#

[prop-size-fromList]:
    'fromList' preserves list length.
    
    > prop-size-fromList
    >   : ∀ (xs : List a)
    >   → size (fromList xs) ≡ length xs
-}
{- $prop-size-mempty
#p:prop-size-mempty#

[prop-size-mempty]:
    The empty 'Bag' has @'size' = 0@.
    
    > prop-size-mempty
    >   : ∀ {a} → size {a} mempty ≡ 0
-}
{- $prop-size-singleton
#p:prop-size-singleton#

[prop-size-singleton]:
    The 'singleton' 'Bag' has @'size' = 1@.
    
    > prop-size-singleton
    >   : ∀ (x : a) → size (singleton x) ≡ 1
-}
-- * Properties
{- $prop-filter-cartesianProduct
#p:prop-filter-cartesianProduct#

[prop-filter-cartesianProduct]:
    Independent filters promote through cartesian product.
    
    > prop-filter-cartesianProduct
    >   : ∀ (p : a → Bool) (q : b → Bool) (xs : Bag a) (ys : Bag b)
    >   → filter (λ xy → p (fst xy) && q (snd xy)) (cartesianProduct xs ys)
    >     ≡ cartesianProduct (filter p xs) (filter q ys)
-}
{- $prop-fromList-++
#p:prop-fromList-++#

[prop-fromList-++]:
    'fromList' maps list concatenation to 'union' of 'Bag's.
    
    > prop-fromList-++
    >   : ∀ (xs ys : List a) 
    >   → fromList (xs ++ ys) ≡ fromList xs <> fromList ys
-}
{- $prop-fromList-empty
#p:prop-fromList-empty#

[prop-fromList-empty]:
    'fromList' maps single element lists to singleton
    
    > prop-fromList-empty : ∀ {a} → fromList {a} [] ≡ mempty
-}
{- $prop-fromList-filter
#p:prop-fromList-filter#

[prop-fromList-filter]:
    'fromList' maps 'Data.List.filter' to 'filter'.
    
    > prop-fromList-filter
    >   : ∀ (p : a → Bool) (xs : List a) 
    >   → fromList (List.filter p xs) ≡ filter p (fromList xs)
-}
{- $prop-morphism-cartesianProduct-1
#p:prop-morphism-cartesianProduct-1#

[prop-morphism-cartesianProduct-1]:
    'cartesianProduct' is a monoid homomorphism in its first argument.
    
    > prop-morphism-cartesianProduct-1
    >   : ∀ (ys : Bag b)
    >   → Monoid.IsHomomorphism (λ xs → cartesianProduct {a} {b} xs ys)
-}
{- $prop-morphism-cartesianProduct-2
#p:prop-morphism-cartesianProduct-2#

[prop-morphism-cartesianProduct-2]:
    'cartesianProduct' is a monoid homomorphism in its second argument.
    
    > prop-morphism-cartesianProduct-2
    >   : ∀ (xs : Bag a)
    >   → Monoid.IsHomomorphism (λ (ys : Bag b) → cartesianProduct {a} {b} xs ys)
-}
{- $prop-morphism-equijoin-1
#p:prop-morphism-equijoin-1#

[prop-morphism-equijoin-1]:
    'equijoin' is a monoid homomorphism in its first argument.
    
    > prop-morphism-equijoin-1
    >   : ∀ {k} ⦃ _ : Eq k ⦄ (f : a → k) (g : b → k) (ys : Bag b)
    >   → Monoid.IsHomomorphism (λ xs → equijoin f g xs ys)
-}
{- $prop-morphism-equijoin-2
#p:prop-morphism-equijoin-2#

[prop-morphism-equijoin-2]:
    'equijoin' is a monoid homomorphism in its second argument.
    
    > prop-morphism-equijoin-2
    >   : ∀ {k} ⦃ _ : Eq k ⦄ (f : a → k) (g : b → k) (xs : Bag a)
    >   → Monoid.IsHomomorphism (λ ys → equijoin f g xs ys)
-}
{- $prop-morphism-filter
#p:prop-morphism-filter#

[prop-morphism-filter]:
    'filter' is a monoid homomorphism.
    
    > prop-morphism-filter
    >   : ∀ (p : a → Bool) → Monoid.IsHomomorphism (filter p)
-}
{- $prop-morphism-fromList
#p:prop-morphism-fromList#

[prop-morphism-fromList]:
    'fromList' is a monoid homomorphism.
    
    > prop-morphism-fromList
    >   : Monoid.IsHomomorphism (fromList {a})
-}
{- $prop-morphism-mmember
#p:prop-morphism-mmember#

[prop-morphism-mmember]:
    'member' is a monoid homomorphism.
    
    > prop-morphism-mmember
    >   : ∀ ⦃ _ : Eq a ⦄ (x : a)
    >   → Monoid.IsHomomorphism ⦃ iMonoidBag {a} ⦄ (mmember x)
-}
{- $prop-morphism-mnull
#p:prop-morphism-mnull#

[prop-morphism-mnull]:
    'null' is a monoid homomorphism.
    
    > prop-morphism-mnull
    >   : Monoid.IsHomomorphism ⦃ iMonoidBag {a} ⦄ mnull
-}
{- $prop-morphism-msize
#p:prop-morphism-msize#

[prop-morphism-msize]:
    'size' is a monoid homomorphism.
    
    > prop-morphism-msize
    >   : Monoid.IsHomomorphism ⦃ iMonoidBag {a} ⦄ msize
-}
{- $prop-null-cartesianProduct
#p:prop-null-cartesianProduct#

[prop-null-cartesianProduct]:
    A 'cartesianProduct' is empty if and only if both arguments are empty.
    
    > prop-null-cartesianProduct
    >   : ∀ (xs : Bag a) (ys : Bag b)
    >   → null (cartesianProduct xs ys) ≡ (null xs || null ys)
-}
{- $prop-size-<>
#p:prop-size-<>#

[prop-size-<>]:
    The union of 'Bags' adds their sizes.
    
    > prop-size-<>
    >   : ∀ (xs ys : Bag a) → size (xs <> ys) ≡ size xs + size ys
-}
{- $prop-size-fromList
#p:prop-size-fromList#

[prop-size-fromList]:
    'fromList' preserves list length.
    
    > prop-size-fromList
    >   : ∀ (xs : List a)
    >   → size (fromList xs) ≡ length xs
-}
{- $prop-size-mempty
#p:prop-size-mempty#

[prop-size-mempty]:
    The empty 'Bag' has @'size' = 0@.
    
    > prop-size-mempty
    >   : ∀ {a} → size {a} mempty ≡ 0
-}
{- $prop-size-singleton
#p:prop-size-singleton#

[prop-size-singleton]:
    The 'singleton' 'Bag' has @'size' = 1@.
    
    > prop-size-singleton
    >   : ∀ (x : a) → size (singleton x) ≡ 1
-}
-- * Properties
{- $prop-filter-cartesianProduct
#p:prop-filter-cartesianProduct#

[prop-filter-cartesianProduct]:
    Independent filters promote through cartesian product.
    
    > prop-filter-cartesianProduct
    >   : ∀ (p : a → Bool) (q : b → Bool) (xs : Bag a) (ys : Bag b)
    >   → filter (λ xy → p (fst xy) && q (snd xy)) (cartesianProduct xs ys)
    >     ≡ cartesianProduct (filter p xs) (filter q ys)
-}
{- $prop-fromList-++
#p:prop-fromList-++#

[prop-fromList-++]:
    'fromList' maps list concatenation to 'union' of 'Bag's.
    
    > prop-fromList-++
    >   : ∀ (xs ys : List a) 
    >   → fromList (xs ++ ys) ≡ fromList xs <> fromList ys
-}
{- $prop-fromList-empty
#p:prop-fromList-empty#

[prop-fromList-empty]:
    'fromList' maps single element lists to singleton
    
    > prop-fromList-empty : ∀ {a} → fromList {a} [] ≡ mempty
-}
{- $prop-fromList-filter
#p:prop-fromList-filter#

[prop-fromList-filter]:
    'fromList' maps 'Data.List.filter' to 'filter'.
    
    > prop-fromList-filter
    >   : ∀ (p : a → Bool) (xs : List a) 
    >   → fromList (List.filter p xs) ≡ filter p (fromList xs)
-}
{- $prop-morphism-cartesianProduct-1
#p:prop-morphism-cartesianProduct-1#

[prop-morphism-cartesianProduct-1]:
    'cartesianProduct' is a monoid homomorphism in its first argument.
    
    > prop-morphism-cartesianProduct-1
    >   : ∀ (ys : Bag b)
    >   → Monoid.IsHomomorphism (λ xs → cartesianProduct {a} {b} xs ys)
-}
{- $prop-morphism-cartesianProduct-2
#p:prop-morphism-cartesianProduct-2#

[prop-morphism-cartesianProduct-2]:
    'cartesianProduct' is a monoid homomorphism in its second argument.
    
    > prop-morphism-cartesianProduct-2
    >   : ∀ (xs : Bag a)
    >   → Monoid.IsHomomorphism (λ (ys : Bag b) → cartesianProduct {a} {b} xs ys)
-}
{- $prop-morphism-equijoin-1
#p:prop-morphism-equijoin-1#

[prop-morphism-equijoin-1]:
    'equijoin' is a monoid homomorphism in its first argument.
    
    > prop-morphism-equijoin-1
    >   : ∀ {k} ⦃ _ : Eq k ⦄ (f : a → k) (g : b → k) (ys : Bag b)
    >   → Monoid.IsHomomorphism (λ xs → equijoin f g xs ys)
-}
{- $prop-morphism-equijoin-2
#p:prop-morphism-equijoin-2#

[prop-morphism-equijoin-2]:
    'equijoin' is a monoid homomorphism in its second argument.
    
    > prop-morphism-equijoin-2
    >   : ∀ {k} ⦃ _ : Eq k ⦄ (f : a → k) (g : b → k) (xs : Bag a)
    >   → Monoid.IsHomomorphism (λ ys → equijoin f g xs ys)
-}
{- $prop-morphism-filter
#p:prop-morphism-filter#

[prop-morphism-filter]:
    'filter' is a monoid homomorphism.
    
    > prop-morphism-filter
    >   : ∀ (p : a → Bool) → Monoid.IsHomomorphism (filter p)
-}
{- $prop-morphism-fromList
#p:prop-morphism-fromList#

[prop-morphism-fromList]:
    'fromList' is a monoid homomorphism.
    
    > prop-morphism-fromList
    >   : Monoid.IsHomomorphism (fromList {a})
-}
{- $prop-morphism-mmember
#p:prop-morphism-mmember#

[prop-morphism-mmember]:
    'member' is a monoid homomorphism.
    
    > prop-morphism-mmember
    >   : ∀ ⦃ _ : Eq a ⦄ (x : a)
    >   → Monoid.IsHomomorphism ⦃ iMonoidBag {a} ⦄ (mmember x)
-}
{- $prop-morphism-mnull
#p:prop-morphism-mnull#

[prop-morphism-mnull]:
    'null' is a monoid homomorphism.
    
    > prop-morphism-mnull
    >   : Monoid.IsHomomorphism ⦃ iMonoidBag {a} ⦄ mnull
-}
{- $prop-morphism-msize
#p:prop-morphism-msize#

[prop-morphism-msize]:
    'size' is a monoid homomorphism.
    
    > prop-morphism-msize
    >   : Monoid.IsHomomorphism ⦃ iMonoidBag {a} ⦄ msize
-}
{- $prop-null-cartesianProduct
#p:prop-null-cartesianProduct#

[prop-null-cartesianProduct]:
    A 'cartesianProduct' is empty if and only if both arguments are empty.
    
    > prop-null-cartesianProduct
    >   : ∀ (xs : Bag a) (ys : Bag b)
    >   → null (cartesianProduct xs ys) ≡ (null xs || null ys)
-}
{- $prop-size-<>
#p:prop-size-<>#

[prop-size-<>]:
    The union of 'Bags' adds their sizes.
    
    > prop-size-<>
    >   : ∀ (xs ys : Bag a) → size (xs <> ys) ≡ size xs + size ys
-}
{- $prop-size-fromList
#p:prop-size-fromList#

[prop-size-fromList]:
    'fromList' preserves list length.
    
    > prop-size-fromList
    >   : ∀ (xs : List a)
    >   → size (fromList xs) ≡ length xs
-}
{- $prop-size-mempty
#p:prop-size-mempty#

[prop-size-mempty]:
    The empty 'Bag' has @'size' = 0@.
    
    > prop-size-mempty
    >   : ∀ {a} → size {a} mempty ≡ 0
-}
{- $prop-size-singleton
#p:prop-size-singleton#

[prop-size-singleton]:
    The 'singleton' 'Bag' has @'size' = 1@.
    
    > prop-size-singleton
    >   : ∀ (x : a) → size (singleton x) ≡ 1
-}
-- * Properties
{- $prop-filter-cartesianProduct
#p:prop-filter-cartesianProduct#

[prop-filter-cartesianProduct]:
    Independent filters promote through cartesian product.
    
    > prop-filter-cartesianProduct
    >   : ∀ (p : a → Bool) (q : b → Bool) (xs : Bag a) (ys : Bag b)
    >   → filter (λ xy → p (fst xy) && q (snd xy)) (cartesianProduct xs ys)
    >     ≡ cartesianProduct (filter p xs) (filter q ys)
-}
{- $prop-fromList-++
#p:prop-fromList-++#

[prop-fromList-++]:
    'fromList' maps list concatenation to 'union' of 'Bag's.
    
    > prop-fromList-++
    >   : ∀ (xs ys : List a) 
    >   → fromList (xs ++ ys) ≡ fromList xs <> fromList ys
-}
{- $prop-fromList-empty
#p:prop-fromList-empty#

[prop-fromList-empty]:
    'fromList' maps single element lists to singleton
    
    > prop-fromList-empty : ∀ {a} → fromList {a} [] ≡ mempty
-}
{- $prop-fromList-filter
#p:prop-fromList-filter#

[prop-fromList-filter]:
    'fromList' maps 'Data.List.filter' to 'filter'.
    
    > prop-fromList-filter
    >   : ∀ (p : a → Bool) (xs : List a) 
    >   → fromList (List.filter p xs) ≡ filter p (fromList xs)
-}
{- $prop-morphism-cartesianProduct-1
#p:prop-morphism-cartesianProduct-1#

[prop-morphism-cartesianProduct-1]:
    'cartesianProduct' is a monoid homomorphism in its first argument.
    
    > prop-morphism-cartesianProduct-1
    >   : ∀ (ys : Bag b)
    >   → Monoid.IsHomomorphism (λ xs → cartesianProduct {a} {b} xs ys)
-}
{- $prop-morphism-cartesianProduct-2
#p:prop-morphism-cartesianProduct-2#

[prop-morphism-cartesianProduct-2]:
    'cartesianProduct' is a monoid homomorphism in its second argument.
    
    > prop-morphism-cartesianProduct-2
    >   : ∀ (xs : Bag a)
    >   → Monoid.IsHomomorphism (λ (ys : Bag b) → cartesianProduct {a} {b} xs ys)
-}
{- $prop-morphism-equijoin-1
#p:prop-morphism-equijoin-1#

[prop-morphism-equijoin-1]:
    'equijoin' is a monoid homomorphism in its first argument.
    
    > prop-morphism-equijoin-1
    >   : ∀ {k} ⦃ _ : Eq k ⦄ (f : a → k) (g : b → k) (ys : Bag b)
    >   → Monoid.IsHomomorphism (λ xs → equijoin f g xs ys)
-}
{- $prop-morphism-equijoin-2
#p:prop-morphism-equijoin-2#

[prop-morphism-equijoin-2]:
    'equijoin' is a monoid homomorphism in its second argument.
    
    > prop-morphism-equijoin-2
    >   : ∀ {k} ⦃ _ : Eq k ⦄ (f : a → k) (g : b → k) (xs : Bag a)
    >   → Monoid.IsHomomorphism (λ ys → equijoin f g xs ys)
-}
{- $prop-morphism-filter
#p:prop-morphism-filter#

[prop-morphism-filter]:
    'filter' is a monoid homomorphism.
    
    > prop-morphism-filter
    >   : ∀ (p : a → Bool) → Monoid.IsHomomorphism (filter p)
-}
{- $prop-morphism-fromList
#p:prop-morphism-fromList#

[prop-morphism-fromList]:
    'fromList' is a monoid homomorphism.
    
    > prop-morphism-fromList
    >   : Monoid.IsHomomorphism (fromList {a})
-}
{- $prop-morphism-mmember
#p:prop-morphism-mmember#

[prop-morphism-mmember]:
    'member' is a monoid homomorphism.
    
    > prop-morphism-mmember
    >   : ∀ ⦃ _ : Eq a ⦄ (x : a)
    >   → Monoid.IsHomomorphism ⦃ iMonoidBag {a} ⦄ (mmember x)
-}
{- $prop-morphism-mnull
#p:prop-morphism-mnull#

[prop-morphism-mnull]:
    'null' is a monoid homomorphism.
    
    > prop-morphism-mnull
    >   : Monoid.IsHomomorphism ⦃ iMonoidBag {a} ⦄ mnull
-}
{- $prop-morphism-msize
#p:prop-morphism-msize#

[prop-morphism-msize]:
    'size' is a monoid homomorphism.
    
    > prop-morphism-msize
    >   : Monoid.IsHomomorphism ⦃ iMonoidBag {a} ⦄ msize
-}
{- $prop-null-cartesianProduct
#p:prop-null-cartesianProduct#

[prop-null-cartesianProduct]:
    A 'cartesianProduct' is empty if and only if both arguments are empty.
    
    > prop-null-cartesianProduct
    >   : ∀ (xs : Bag a) (ys : Bag b)
    >   → null (cartesianProduct xs ys) ≡ (null xs || null ys)
-}
{- $prop-size-<>
#p:prop-size-<>#

[prop-size-<>]:
    The union of 'Bags' adds their sizes.
    
    > prop-size-<>
    >   : ∀ (xs ys : Bag a) → size (xs <> ys) ≡ size xs + size ys
-}
{- $prop-size-fromList
#p:prop-size-fromList#

[prop-size-fromList]:
    'fromList' preserves list length.
    
    > prop-size-fromList
    >   : ∀ (xs : List a)
    >   → size (fromList xs) ≡ length xs
-}
{- $prop-size-mempty
#p:prop-size-mempty#

[prop-size-mempty]:
    The empty 'Bag' has @'size' = 0@.
    
    > prop-size-mempty
    >   : ∀ {a} → size {a} mempty ≡ 0
-}
{- $prop-size-singleton
#p:prop-size-singleton#

[prop-size-singleton]:
    The 'singleton' 'Bag' has @'size' = 1@.
    
    > prop-size-singleton
    >   : ∀ (x : a) → size (singleton x) ≡ 1
-}
-- * Properties
{- $prop-filter-cartesianProduct
#p:prop-filter-cartesianProduct#

[prop-filter-cartesianProduct]:
    Independent filters promote through cartesian product.
    
    > prop-filter-cartesianProduct
    >   : ∀ (p : a → Bool) (q : b → Bool) (xs : Bag a) (ys : Bag b)
    >   → filter (λ xy → p (fst xy) && q (snd xy)) (cartesianProduct xs ys)
    >     ≡ cartesianProduct (filter p xs) (filter q ys)
-}
{- $prop-fromList-++
#p:prop-fromList-++#

[prop-fromList-++]:
    'fromList' maps list concatenation to 'union' of 'Bag's.
    
    > prop-fromList-++
    >   : ∀ (xs ys : List a) 
    >   → fromList (xs ++ ys) ≡ fromList xs <> fromList ys
-}
{- $prop-fromList-empty
#p:prop-fromList-empty#

[prop-fromList-empty]:
    'fromList' maps single element lists to singleton
    
    > prop-fromList-empty : ∀ {a} → fromList {a} [] ≡ mempty
-}
{- $prop-fromList-filter
#p:prop-fromList-filter#

[prop-fromList-filter]:
    'fromList' maps 'Data.List.filter' to 'filter'.
    
    > prop-fromList-filter
    >   : ∀ (p : a → Bool) (xs : List a) 
    >   → fromList (List.filter p xs) ≡ filter p (fromList xs)
-}
{- $prop-morphism-cartesianProduct-1
#p:prop-morphism-cartesianProduct-1#

[prop-morphism-cartesianProduct-1]:
    'cartesianProduct' is a monoid homomorphism in its first argument.
    
    > prop-morphism-cartesianProduct-1
    >   : ∀ (ys : Bag b)
    >   → Monoid.IsHomomorphism (λ xs → cartesianProduct {a} {b} xs ys)
-}
{- $prop-morphism-cartesianProduct-2
#p:prop-morphism-cartesianProduct-2#

[prop-morphism-cartesianProduct-2]:
    'cartesianProduct' is a monoid homomorphism in its second argument.
    
    > prop-morphism-cartesianProduct-2
    >   : ∀ (xs : Bag a)
    >   → Monoid.IsHomomorphism (λ (ys : Bag b) → cartesianProduct {a} {b} xs ys)
-}
{- $prop-morphism-equijoin-1
#p:prop-morphism-equijoin-1#

[prop-morphism-equijoin-1]:
    'equijoin' is a monoid homomorphism in its first argument.
    
    > prop-morphism-equijoin-1
    >   : ∀ {k} ⦃ _ : Eq k ⦄ (f : a → k) (g : b → k) (ys : Bag b)
    >   → Monoid.IsHomomorphism (λ xs → equijoin f g xs ys)
-}
{- $prop-morphism-equijoin-2
#p:prop-morphism-equijoin-2#

[prop-morphism-equijoin-2]:
    'equijoin' is a monoid homomorphism in its second argument.
    
    > prop-morphism-equijoin-2
    >   : ∀ {k} ⦃ _ : Eq k ⦄ (f : a → k) (g : b → k) (xs : Bag a)
    >   → Monoid.IsHomomorphism (λ ys → equijoin f g xs ys)
-}
{- $prop-morphism-filter
#p:prop-morphism-filter#

[prop-morphism-filter]:
    'filter' is a monoid homomorphism.
    
    > prop-morphism-filter
    >   : ∀ (p : a → Bool) → Monoid.IsHomomorphism (filter p)
-}
{- $prop-morphism-fromList
#p:prop-morphism-fromList#

[prop-morphism-fromList]:
    'fromList' is a monoid homomorphism.
    
    > prop-morphism-fromList
    >   : Monoid.IsHomomorphism (fromList {a})
-}
{- $prop-morphism-mmember
#p:prop-morphism-mmember#

[prop-morphism-mmember]:
    'member' is a monoid homomorphism.
    
    > prop-morphism-mmember
    >   : ∀ ⦃ _ : Eq a ⦄ (x : a)
    >   → Monoid.IsHomomorphism ⦃ iMonoidBag {a} ⦄ (mmember x)
-}
{- $prop-morphism-mnull
#p:prop-morphism-mnull#

[prop-morphism-mnull]:
    'null' is a monoid homomorphism.
    
    > prop-morphism-mnull
    >   : Monoid.IsHomomorphism ⦃ iMonoidBag {a} ⦄ mnull
-}
{- $prop-morphism-msize
#p:prop-morphism-msize#

[prop-morphism-msize]:
    'size' is a monoid homomorphism.
    
    > prop-morphism-msize
    >   : Monoid.IsHomomorphism ⦃ iMonoidBag {a} ⦄ msize
-}
{- $prop-null-cartesianProduct
#p:prop-null-cartesianProduct#

[prop-null-cartesianProduct]:
    A 'cartesianProduct' is empty if and only if both arguments are empty.
    
    > prop-null-cartesianProduct
    >   : ∀ (xs : Bag a) (ys : Bag b)
    >   → null (cartesianProduct xs ys) ≡ (null xs || null ys)
-}
{- $prop-size-<>
#p:prop-size-<>#

[prop-size-<>]:
    The union of 'Bags' adds their sizes.
    
    > prop-size-<>
    >   : ∀ (xs ys : Bag a) → size (xs <> ys) ≡ size xs + size ys
-}
{- $prop-size-fromList
#p:prop-size-fromList#

[prop-size-fromList]:
    'fromList' preserves list length.
    
    > prop-size-fromList
    >   : ∀ (xs : List a)
    >   → size (fromList xs) ≡ length xs
-}
{- $prop-size-mempty
#p:prop-size-mempty#

[prop-size-mempty]:
    The empty 'Bag' has @'size' = 0@.
    
    > prop-size-mempty
    >   : ∀ {a} → size {a} mempty ≡ 0
-}
{- $prop-size-singleton
#p:prop-size-singleton#

[prop-size-singleton]:
    The 'singleton' 'Bag' has @'size' = 1@.
    
    > prop-size-singleton
    >   : ∀ (x : a) → size (singleton x) ≡ 1
-}
-- * Properties
{- $prop-filter-cartesianProduct
#p:prop-filter-cartesianProduct#

[prop-filter-cartesianProduct]:
    Independent filters promote through cartesian product.
    
    > prop-filter-cartesianProduct
    >   : ∀ (p : a → Bool) (q : b → Bool) (xs : Bag a) (ys : Bag b)
    >   → filter (λ xy → p (fst xy) && q (snd xy)) (cartesianProduct xs ys)
    >     ≡ cartesianProduct (filter p xs) (filter q ys)
-}
{- $prop-fromList-++
#p:prop-fromList-++#

[prop-fromList-++]:
    'fromList' maps list concatenation to 'union' of 'Bag's.
    
    > prop-fromList-++
    >   : ∀ (xs ys : List a) 
    >   → fromList (xs ++ ys) ≡ fromList xs <> fromList ys
-}
{- $prop-fromList-empty
#p:prop-fromList-empty#

[prop-fromList-empty]:
    'fromList' maps single element lists to singleton
    
    > prop-fromList-empty : ∀ {a} → fromList {a} [] ≡ mempty
-}
{- $prop-fromList-filter
#p:prop-fromList-filter#

[prop-fromList-filter]:
    'fromList' maps 'Data.List.filter' to 'filter'.
    
    > prop-fromList-filter
    >   : ∀ (p : a → Bool) (xs : List a) 
    >   → fromList (List.filter p xs) ≡ filter p (fromList xs)
-}
{- $prop-morphism-cartesianProduct-1
#p:prop-morphism-cartesianProduct-1#

[prop-morphism-cartesianProduct-1]:
    'cartesianProduct' is a monoid homomorphism in its first argument.
    
    > prop-morphism-cartesianProduct-1
    >   : ∀ (ys : Bag b)
    >   → Monoid.IsHomomorphism (λ xs → cartesianProduct {a} {b} xs ys)
-}
{- $prop-morphism-cartesianProduct-2
#p:prop-morphism-cartesianProduct-2#

[prop-morphism-cartesianProduct-2]:
    'cartesianProduct' is a monoid homomorphism in its second argument.
    
    > prop-morphism-cartesianProduct-2
    >   : ∀ (xs : Bag a)
    >   → Monoid.IsHomomorphism (λ (ys : Bag b) → cartesianProduct {a} {b} xs ys)
-}
{- $prop-morphism-equijoin-1
#p:prop-morphism-equijoin-1#

[prop-morphism-equijoin-1]:
    'equijoin' is a monoid homomorphism in its first argument.
    
    > prop-morphism-equijoin-1
    >   : ∀ {k} ⦃ _ : Eq k ⦄ (f : a → k) (g : b → k) (ys : Bag b)
    >   → Monoid.IsHomomorphism (λ xs → equijoin f g xs ys)
-}
{- $prop-morphism-equijoin-2
#p:prop-morphism-equijoin-2#

[prop-morphism-equijoin-2]:
    'equijoin' is a monoid homomorphism in its second argument.
    
    > prop-morphism-equijoin-2
    >   : ∀ {k} ⦃ _ : Eq k ⦄ (f : a → k) (g : b → k) (xs : Bag a)
    >   → Monoid.IsHomomorphism (λ ys → equijoin f g xs ys)
-}
{- $prop-morphism-filter
#p:prop-morphism-filter#

[prop-morphism-filter]:
    'filter' is a monoid homomorphism.
    
    > prop-morphism-filter
    >   : ∀ (p : a → Bool) → Monoid.IsHomomorphism (filter p)
-}
{- $prop-morphism-fromList
#p:prop-morphism-fromList#

[prop-morphism-fromList]:
    'fromList' is a monoid homomorphism.
    
    > prop-morphism-fromList
    >   : Monoid.IsHomomorphism (fromList {a})
-}
{- $prop-morphism-mmember
#p:prop-morphism-mmember#

[prop-morphism-mmember]:
    'member' is a monoid homomorphism.
    
    > prop-morphism-mmember
    >   : ∀ ⦃ _ : Eq a ⦄ (x : a)
    >   → Monoid.IsHomomorphism ⦃ iMonoidBag {a} ⦄ (mmember x)
-}
{- $prop-morphism-mnull
#p:prop-morphism-mnull#

[prop-morphism-mnull]:
    'null' is a monoid homomorphism.
    
    > prop-morphism-mnull
    >   : Monoid.IsHomomorphism ⦃ iMonoidBag {a} ⦄ mnull
-}
{- $prop-morphism-msize
#p:prop-morphism-msize#

[prop-morphism-msize]:
    'size' is a monoid homomorphism.
    
    > prop-morphism-msize
    >   : Monoid.IsHomomorphism ⦃ iMonoidBag {a} ⦄ msize
-}
{- $prop-null-cartesianProduct
#p:prop-null-cartesianProduct#

[prop-null-cartesianProduct]:
    A 'cartesianProduct' is empty if and only if both arguments are empty.
    
    > prop-null-cartesianProduct
    >   : ∀ (xs : Bag a) (ys : Bag b)
    >   → null (cartesianProduct xs ys) ≡ (null xs || null ys)
-}
{- $prop-size-<>
#p:prop-size-<>#

[prop-size-<>]:
    The union of 'Bags' adds their sizes.
    
    > prop-size-<>
    >   : ∀ (xs ys : Bag a) → size (xs <> ys) ≡ size xs + size ys
-}
{- $prop-size-fromList
#p:prop-size-fromList#

[prop-size-fromList]:
    'fromList' preserves list length.
    
    > prop-size-fromList
    >   : ∀ (xs : List a)
    >   → size (fromList xs) ≡ length xs
-}
{- $prop-size-mempty
#p:prop-size-mempty#

[prop-size-mempty]:
    The empty 'Bag' has @'size' = 0@.
    
    > prop-size-mempty
    >   : ∀ {a} → size {a} mempty ≡ 0
-}
{- $prop-size-singleton
#p:prop-size-singleton#

[prop-size-singleton]:
    The 'singleton' 'Bag' has @'size' = 1@.
    
    > prop-size-singleton
    >   : ∀ (x : a) → size (singleton x) ≡ 1
-}
-- * Properties
{- $prop-filter-cartesianProduct
#p:prop-filter-cartesianProduct#

[prop-filter-cartesianProduct]:
    Independent filters promote through cartesian product.
    
    > prop-filter-cartesianProduct
    >   : ∀ (p : a → Bool) (q : b → Bool) (xs : Bag a) (ys : Bag b)
    >   → filter (λ xy → p (fst xy) && q (snd xy)) (cartesianProduct xs ys)
    >     ≡ cartesianProduct (filter p xs) (filter q ys)
-}
{- $prop-fromList-++
#p:prop-fromList-++#

[prop-fromList-++]:
    'fromList' maps list concatenation to 'union' of 'Bag's.
    
    > prop-fromList-++
    >   : ∀ (xs ys : List a) 
    >   → fromList (xs ++ ys) ≡ fromList xs <> fromList ys
-}
{- $prop-fromList-empty
#p:prop-fromList-empty#

[prop-fromList-empty]:
    'fromList' maps single element lists to singleton
    
    > prop-fromList-empty : ∀ {a} → fromList {a} [] ≡ mempty
-}
{- $prop-fromList-filter
#p:prop-fromList-filter#

[prop-fromList-filter]:
    'fromList' maps 'Data.List.filter' to 'filter'.
    
    > prop-fromList-filter
    >   : ∀ (p : a → Bool) (xs : List a) 
    >   → fromList (List.filter p xs) ≡ filter p (fromList xs)
-}
{- $prop-morphism-cartesianProduct-1
#p:prop-morphism-cartesianProduct-1#

[prop-morphism-cartesianProduct-1]:
    'cartesianProduct' is a monoid homomorphism in its first argument.
    
    > prop-morphism-cartesianProduct-1
    >   : ∀ (ys : Bag b)
    >   → Monoid.IsHomomorphism (λ xs → cartesianProduct {a} {b} xs ys)
-}
{- $prop-morphism-cartesianProduct-2
#p:prop-morphism-cartesianProduct-2#

[prop-morphism-cartesianProduct-2]:
    'cartesianProduct' is a monoid homomorphism in its second argument.
    
    > prop-morphism-cartesianProduct-2
    >   : ∀ (xs : Bag a)
    >   → Monoid.IsHomomorphism (λ (ys : Bag b) → cartesianProduct {a} {b} xs ys)
-}
{- $prop-morphism-equijoin-1
#p:prop-morphism-equijoin-1#

[prop-morphism-equijoin-1]:
    'equijoin' is a monoid homomorphism in its first argument.
    
    > prop-morphism-equijoin-1
    >   : ∀ {k} ⦃ _ : Eq k ⦄ (f : a → k) (g : b → k) (ys : Bag b)
    >   → Monoid.IsHomomorphism (λ xs → equijoin f g xs ys)
-}
{- $prop-morphism-equijoin-2
#p:prop-morphism-equijoin-2#

[prop-morphism-equijoin-2]:
    'equijoin' is a monoid homomorphism in its second argument.
    
    > prop-morphism-equijoin-2
    >   : ∀ {k} ⦃ _ : Eq k ⦄ (f : a → k) (g : b → k) (xs : Bag a)
    >   → Monoid.IsHomomorphism (λ ys → equijoin f g xs ys)
-}
{- $prop-morphism-filter
#p:prop-morphism-filter#

[prop-morphism-filter]:
    'filter' is a monoid homomorphism.
    
    > prop-morphism-filter
    >   : ∀ (p : a → Bool) → Monoid.IsHomomorphism (filter p)
-}
{- $prop-morphism-fromList
#p:prop-morphism-fromList#

[prop-morphism-fromList]:
    'fromList' is a monoid homomorphism.
    
    > prop-morphism-fromList
    >   : Monoid.IsHomomorphism (fromList {a})
-}
{- $prop-morphism-mmember
#p:prop-morphism-mmember#

[prop-morphism-mmember]:
    'member' is a monoid homomorphism.
    
    > prop-morphism-mmember
    >   : ∀ ⦃ _ : Eq a ⦄ (x : a)
    >   → Monoid.IsHomomorphism ⦃ iMonoidBag {a} ⦄ (mmember x)
-}
{- $prop-morphism-mnull
#p:prop-morphism-mnull#

[prop-morphism-mnull]:
    'null' is a monoid homomorphism.
    
    > prop-morphism-mnull
    >   : Monoid.IsHomomorphism ⦃ iMonoidBag {a} ⦄ mnull
-}
{- $prop-morphism-msize
#p:prop-morphism-msize#

[prop-morphism-msize]:
    'size' is a monoid homomorphism.
    
    > prop-morphism-msize
    >   : Monoid.IsHomomorphism ⦃ iMonoidBag {a} ⦄ msize
-}
{- $prop-null-cartesianProduct
#p:prop-null-cartesianProduct#

[prop-null-cartesianProduct]:
    A 'cartesianProduct' is empty if and only if both arguments are empty.
    
    > prop-null-cartesianProduct
    >   : ∀ (xs : Bag a) (ys : Bag b)
    >   → null (cartesianProduct xs ys) ≡ (null xs || null ys)
-}
{- $prop-size-<>
#p:prop-size-<>#

[prop-size-<>]:
    The union of 'Bags' adds their sizes.
    
    > prop-size-<>
    >   : ∀ (xs ys : Bag a) → size (xs <> ys) ≡ size xs + size ys
-}
{- $prop-size-fromList
#p:prop-size-fromList#

[prop-size-fromList]:
    'fromList' preserves list length.
    
    > prop-size-fromList
    >   : ∀ (xs : List a)
    >   → size (fromList xs) ≡ length xs
-}
{- $prop-size-mempty
#p:prop-size-mempty#

[prop-size-mempty]:
    The empty 'Bag' has @'size' = 0@.
    
    > prop-size-mempty
    >   : ∀ {a} → size {a} mempty ≡ 0
-}
{- $prop-size-singleton
#p:prop-size-singleton#

[prop-size-singleton]:
    The 'singleton' 'Bag' has @'size' = 1@.
    
    > prop-size-singleton
    >   : ∀ (x : a) → size (singleton x) ≡ 1
-}
-- * Properties
{- $prop-filter-cartesianProduct
#p:prop-filter-cartesianProduct#

[prop-filter-cartesianProduct]:
    Independent filters promote through cartesian product.
    
    > prop-filter-cartesianProduct
    >   : ∀ (p : a → Bool) (q : b → Bool) (xs : Bag a) (ys : Bag b)
    >   → filter (λ xy → p (fst xy) && q (snd xy)) (cartesianProduct xs ys)
    >     ≡ cartesianProduct (filter p xs) (filter q ys)
-}
{- $prop-fromList-++
#p:prop-fromList-++#

[prop-fromList-++]:
    'fromList' maps list concatenation to 'union' of 'Bag's.
    
    > prop-fromList-++
    >   : ∀ (xs ys : List a) 
    >   → fromList (xs ++ ys) ≡ fromList xs <> fromList ys
-}
{- $prop-fromList-empty
#p:prop-fromList-empty#

[prop-fromList-empty]:
    'fromList' maps single element lists to singleton
    
    > prop-fromList-empty : ∀ {a} → fromList {a} [] ≡ mempty
-}
{- $prop-fromList-filter
#p:prop-fromList-filter#

[prop-fromList-filter]:
    'fromList' maps 'Data.List.filter' to 'filter'.
    
    > prop-fromList-filter
    >   : ∀ (p : a → Bool) (xs : List a) 
    >   → fromList (List.filter p xs) ≡ filter p (fromList xs)
-}
{- $prop-morphism-cartesianProduct-1
#p:prop-morphism-cartesianProduct-1#

[prop-morphism-cartesianProduct-1]:
    'cartesianProduct' is a monoid homomorphism in its first argument.
    
    > prop-morphism-cartesianProduct-1
    >   : ∀ (ys : Bag b)
    >   → Monoid.IsHomomorphism (λ xs → cartesianProduct {a} {b} xs ys)
-}
{- $prop-morphism-cartesianProduct-2
#p:prop-morphism-cartesianProduct-2#

[prop-morphism-cartesianProduct-2]:
    'cartesianProduct' is a monoid homomorphism in its second argument.
    
    > prop-morphism-cartesianProduct-2
    >   : ∀ (xs : Bag a)
    >   → Monoid.IsHomomorphism (λ (ys : Bag b) → cartesianProduct {a} {b} xs ys)
-}
{- $prop-morphism-equijoin-1
#p:prop-morphism-equijoin-1#

[prop-morphism-equijoin-1]:
    'equijoin' is a monoid homomorphism in its first argument.
    
    > prop-morphism-equijoin-1
    >   : ∀ {k} ⦃ _ : Eq k ⦄ (f : a → k) (g : b → k) (ys : Bag b)
    >   → Monoid.IsHomomorphism (λ xs → equijoin f g xs ys)
-}
{- $prop-morphism-equijoin-2
#p:prop-morphism-equijoin-2#

[prop-morphism-equijoin-2]:
    'equijoin' is a monoid homomorphism in its second argument.
    
    > prop-morphism-equijoin-2
    >   : ∀ {k} ⦃ _ : Eq k ⦄ (f : a → k) (g : b → k) (xs : Bag a)
    >   → Monoid.IsHomomorphism (λ ys → equijoin f g xs ys)
-}
{- $prop-morphism-filter
#p:prop-morphism-filter#

[prop-morphism-filter]:
    'filter' is a monoid homomorphism.
    
    > prop-morphism-filter
    >   : ∀ (p : a → Bool) → Monoid.IsHomomorphism (filter p)
-}
{- $prop-morphism-fromList
#p:prop-morphism-fromList#

[prop-morphism-fromList]:
    'fromList' is a monoid homomorphism.
    
    > prop-morphism-fromList
    >   : Monoid.IsHomomorphism (fromList {a})
-}
{- $prop-morphism-mmember
#p:prop-morphism-mmember#

[prop-morphism-mmember]:
    'member' is a monoid homomorphism.
    
    > prop-morphism-mmember
    >   : ∀ ⦃ _ : Eq a ⦄ (x : a)
    >   → Monoid.IsHomomorphism ⦃ iMonoidBag {a} ⦄ (mmember x)
-}
{- $prop-morphism-mnull
#p:prop-morphism-mnull#

[prop-morphism-mnull]:
    'null' is a monoid homomorphism.
    
    > prop-morphism-mnull
    >   : Monoid.IsHomomorphism ⦃ iMonoidBag {a} ⦄ mnull
-}
{- $prop-morphism-msize
#p:prop-morphism-msize#

[prop-morphism-msize]:
    'size' is a monoid homomorphism.
    
    > prop-morphism-msize
    >   : Monoid.IsHomomorphism ⦃ iMonoidBag {a} ⦄ msize
-}
{- $prop-null-cartesianProduct
#p:prop-null-cartesianProduct#

[prop-null-cartesianProduct]:
    A 'cartesianProduct' is empty if and only if both arguments are empty.
    
    > prop-null-cartesianProduct
    >   : ∀ (xs : Bag a) (ys : Bag b)
    >   → null (cartesianProduct xs ys) ≡ (null xs || null ys)
-}
{- $prop-size-<>
#p:prop-size-<>#

[prop-size-<>]:
    The union of 'Bags' adds their sizes.
    
    > prop-size-<>
    >   : ∀ (xs ys : Bag a) → size (xs <> ys) ≡ size xs + size ys
-}
{- $prop-size-fromList
#p:prop-size-fromList#

[prop-size-fromList]:
    'fromList' preserves list length.
    
    > prop-size-fromList
    >   : ∀ (xs : List a)
    >   → size (fromList xs) ≡ length xs
-}
{- $prop-size-mempty
#p:prop-size-mempty#

[prop-size-mempty]:
    The empty 'Bag' has @'size' = 0@.
    
    > prop-size-mempty
    >   : ∀ {a} → size {a} mempty ≡ 0
-}
{- $prop-size-singleton
#p:prop-size-singleton#

[prop-size-singleton]:
    The 'singleton' 'Bag' has @'size' = 1@.
    
    > prop-size-singleton
    >   : ∀ (x : a) → size (singleton x) ≡ 1
-}
-- * Properties
{- $prop-filter-cartesianProduct
#p:prop-filter-cartesianProduct#

[prop-filter-cartesianProduct]:
    Independent filters promote through cartesian product.
    
    > prop-filter-cartesianProduct
    >   : ∀ (p : a → Bool) (q : b → Bool) (xs : Bag a) (ys : Bag b)
    >   → filter (λ xy → p (fst xy) && q (snd xy)) (cartesianProduct xs ys)
    >     ≡ cartesianProduct (filter p xs) (filter q ys)
-}
{- $prop-fromList-++
#p:prop-fromList-++#

[prop-fromList-++]:
    'fromList' maps list concatenation to 'union' of 'Bag's.
    
    > prop-fromList-++
    >   : ∀ (xs ys : List a) 
    >   → fromList (xs ++ ys) ≡ fromList xs <> fromList ys
-}
{- $prop-fromList-empty
#p:prop-fromList-empty#

[prop-fromList-empty]:
    'fromList' maps single element lists to singleton
    
    > prop-fromList-empty : ∀ {a} → fromList {a} [] ≡ mempty
-}
{- $prop-fromList-filter
#p:prop-fromList-filter#

[prop-fromList-filter]:
    'fromList' maps 'Data.List.filter' to 'filter'.
    
    > prop-fromList-filter
    >   : ∀ (p : a → Bool) (xs : List a) 
    >   → fromList (List.filter p xs) ≡ filter p (fromList xs)
-}
{- $prop-morphism-cartesianProduct-1
#p:prop-morphism-cartesianProduct-1#

[prop-morphism-cartesianProduct-1]:
    'cartesianProduct' is a monoid homomorphism in its first argument.
    
    > prop-morphism-cartesianProduct-1
    >   : ∀ (ys : Bag b)
    >   → Monoid.IsHomomorphism (λ xs → cartesianProduct {a} {b} xs ys)
-}
{- $prop-morphism-cartesianProduct-2
#p:prop-morphism-cartesianProduct-2#

[prop-morphism-cartesianProduct-2]:
    'cartesianProduct' is a monoid homomorphism in its second argument.
    
    > prop-morphism-cartesianProduct-2
    >   : ∀ (xs : Bag a)
    >   → Monoid.IsHomomorphism (λ (ys : Bag b) → cartesianProduct {a} {b} xs ys)
-}
{- $prop-morphism-equijoin-1
#p:prop-morphism-equijoin-1#

[prop-morphism-equijoin-1]:
    'equijoin' is a monoid homomorphism in its first argument.
    
    > prop-morphism-equijoin-1
    >   : ∀ {k} ⦃ _ : Eq k ⦄ (f : a → k) (g : b → k) (ys : Bag b)
    >   → Monoid.IsHomomorphism (λ xs → equijoin f g xs ys)
-}
{- $prop-morphism-equijoin-2
#p:prop-morphism-equijoin-2#

[prop-morphism-equijoin-2]:
    'equijoin' is a monoid homomorphism in its second argument.
    
    > prop-morphism-equijoin-2
    >   : ∀ {k} ⦃ _ : Eq k ⦄ (f : a → k) (g : b → k) (xs : Bag a)
    >   → Monoid.IsHomomorphism (λ ys → equijoin f g xs ys)
-}
{- $prop-morphism-filter
#p:prop-morphism-filter#

[prop-morphism-filter]:
    'filter' is a monoid homomorphism.
    
    > prop-morphism-filter
    >   : ∀ (p : a → Bool) → Monoid.IsHomomorphism (filter p)
-}
{- $prop-morphism-fromList
#p:prop-morphism-fromList#

[prop-morphism-fromList]:
    'fromList' is a monoid homomorphism.
    
    > prop-morphism-fromList
    >   : Monoid.IsHomomorphism (fromList {a})
-}
{- $prop-morphism-mmember
#p:prop-morphism-mmember#

[prop-morphism-mmember]:
    'member' is a monoid homomorphism.
    
    > prop-morphism-mmember
    >   : ∀ ⦃ _ : Eq a ⦄ (x : a)
    >   → Monoid.IsHomomorphism ⦃ iMonoidBag {a} ⦄ (mmember x)
-}
{- $prop-morphism-mnull
#p:prop-morphism-mnull#

[prop-morphism-mnull]:
    'null' is a monoid homomorphism.
    
    > prop-morphism-mnull
    >   : Monoid.IsHomomorphism ⦃ iMonoidBag {a} ⦄ mnull
-}
{- $prop-morphism-msize
#p:prop-morphism-msize#

[prop-morphism-msize]:
    'size' is a monoid homomorphism.
    
    > prop-morphism-msize
    >   : Monoid.IsHomomorphism ⦃ iMonoidBag {a} ⦄ msize
-}
{- $prop-null-cartesianProduct
#p:prop-null-cartesianProduct#

[prop-null-cartesianProduct]:
    A 'cartesianProduct' is empty if and only if both arguments are empty.
    
    > prop-null-cartesianProduct
    >   : ∀ (xs : Bag a) (ys : Bag b)
    >   → null (cartesianProduct xs ys) ≡ (null xs || null ys)
-}
{- $prop-size-<>
#p:prop-size-<>#

[prop-size-<>]:
    The union of 'Bags' adds their sizes.
    
    > prop-size-<>
    >   : ∀ (xs ys : Bag a) → size (xs <> ys) ≡ size xs + size ys
-}
{- $prop-size-fromList
#p:prop-size-fromList#

[prop-size-fromList]:
    'fromList' preserves list length.
    
    > prop-size-fromList
    >   : ∀ (xs : List a)
    >   → size (fromList xs) ≡ length xs
-}
{- $prop-size-mempty
#p:prop-size-mempty#

[prop-size-mempty]:
    The empty 'Bag' has @'size' = 0@.
    
    > prop-size-mempty
    >   : ∀ {a} → size {a} mempty ≡ 0
-}
{- $prop-size-singleton
#p:prop-size-singleton#

[prop-size-singleton]:
    The 'singleton' 'Bag' has @'size' = 1@.
    
    > prop-size-singleton
    >   : ∀ (x : a) → size (singleton x) ≡ 1
-}
-- * Properties
{- $prop-filter-cartesianProduct
#p:prop-filter-cartesianProduct#

[prop-filter-cartesianProduct]:
    Independent filters promote through cartesian product.
    
    > prop-filter-cartesianProduct
    >   : ∀ (p : a → Bool) (q : b → Bool) (xs : Bag a) (ys : Bag b)
    >   → filter (λ xy → p (fst xy) && q (snd xy)) (cartesianProduct xs ys)
    >     ≡ cartesianProduct (filter p xs) (filter q ys)
-}
{- $prop-fromList-++
#p:prop-fromList-++#

[prop-fromList-++]:
    'fromList' maps list concatenation to 'union' of 'Bag's.
    
    > prop-fromList-++
    >   : ∀ (xs ys : List a) 
    >   → fromList (xs ++ ys) ≡ fromList xs <> fromList ys
-}
{- $prop-fromList-empty
#p:prop-fromList-empty#

[prop-fromList-empty]:
    'fromList' maps single element lists to singleton
    
    > prop-fromList-empty : ∀ {a} → fromList {a} [] ≡ mempty
-}
{- $prop-fromList-filter
#p:prop-fromList-filter#

[prop-fromList-filter]:
    'fromList' maps 'Data.List.filter' to 'filter'.
    
    > prop-fromList-filter
    >   : ∀ (p : a → Bool) (xs : List a) 
    >   → fromList (List.filter p xs) ≡ filter p (fromList xs)
-}
{- $prop-morphism-cartesianProduct-1
#p:prop-morphism-cartesianProduct-1#

[prop-morphism-cartesianProduct-1]:
    'cartesianProduct' is a monoid homomorphism in its first argument.
    
    > prop-morphism-cartesianProduct-1
    >   : ∀ (ys : Bag b)
    >   → Monoid.IsHomomorphism (λ xs → cartesianProduct {a} {b} xs ys)
-}
{- $prop-morphism-cartesianProduct-2
#p:prop-morphism-cartesianProduct-2#

[prop-morphism-cartesianProduct-2]:
    'cartesianProduct' is a monoid homomorphism in its second argument.
    
    > prop-morphism-cartesianProduct-2
    >   : ∀ (xs : Bag a)
    >   → Monoid.IsHomomorphism (λ (ys : Bag b) → cartesianProduct {a} {b} xs ys)
-}
{- $prop-morphism-equijoin-1
#p:prop-morphism-equijoin-1#

[prop-morphism-equijoin-1]:
    'equijoin' is a monoid homomorphism in its first argument.
    
    > prop-morphism-equijoin-1
    >   : ∀ {k} ⦃ _ : Eq k ⦄ (f : a → k) (g : b → k) (ys : Bag b)
    >   → Monoid.IsHomomorphism (λ xs → equijoin f g xs ys)
-}
{- $prop-morphism-equijoin-2
#p:prop-morphism-equijoin-2#

[prop-morphism-equijoin-2]:
    'equijoin' is a monoid homomorphism in its second argument.
    
    > prop-morphism-equijoin-2
    >   : ∀ {k} ⦃ _ : Eq k ⦄ (f : a → k) (g : b → k) (xs : Bag a)
    >   → Monoid.IsHomomorphism (λ ys → equijoin f g xs ys)
-}
{- $prop-morphism-filter
#p:prop-morphism-filter#

[prop-morphism-filter]:
    'filter' is a monoid homomorphism.
    
    > prop-morphism-filter
    >   : ∀ (p : a → Bool) → Monoid.IsHomomorphism (filter p)
-}
{- $prop-morphism-fromList
#p:prop-morphism-fromList#

[prop-morphism-fromList]:
    'fromList' is a monoid homomorphism.
    
    > prop-morphism-fromList
    >   : Monoid.IsHomomorphism (fromList {a})
-}
{- $prop-morphism-mmember
#p:prop-morphism-mmember#

[prop-morphism-mmember]:
    'member' is a monoid homomorphism.
    
    > prop-morphism-mmember
    >   : ∀ ⦃ _ : Eq a ⦄ (x : a)
    >   → Monoid.IsHomomorphism ⦃ iMonoidBag {a} ⦄ (mmember x)
-}
{- $prop-morphism-mnull
#p:prop-morphism-mnull#

[prop-morphism-mnull]:
    'null' is a monoid homomorphism.
    
    > prop-morphism-mnull
    >   : Monoid.IsHomomorphism ⦃ iMonoidBag {a} ⦄ mnull
-}
{- $prop-morphism-msize
#p:prop-morphism-msize#

[prop-morphism-msize]:
    'size' is a monoid homomorphism.
    
    > prop-morphism-msize
    >   : Monoid.IsHomomorphism ⦃ iMonoidBag {a} ⦄ msize
-}
{- $prop-null-cartesianProduct
#p:prop-null-cartesianProduct#

[prop-null-cartesianProduct]:
    A 'cartesianProduct' is empty if and only if both arguments are empty.
    
    > prop-null-cartesianProduct
    >   : ∀ (xs : Bag a) (ys : Bag b)
    >   → null (cartesianProduct xs ys) ≡ (null xs || null ys)
-}
{- $prop-size-<>
#p:prop-size-<>#

[prop-size-<>]:
    The union of 'Bags' adds their sizes.
    
    > prop-size-<>
    >   : ∀ (xs ys : Bag a) → size (xs <> ys) ≡ size xs + size ys
-}
{- $prop-size-fromList
#p:prop-size-fromList#

[prop-size-fromList]:
    'fromList' preserves list length.
    
    > prop-size-fromList
    >   : ∀ (xs : List a)
    >   → size (fromList xs) ≡ length xs
-}
{- $prop-size-mempty
#p:prop-size-mempty#

[prop-size-mempty]:
    The empty 'Bag' has @'size' = 0@.
    
    > prop-size-mempty
    >   : ∀ {a} → size {a} mempty ≡ 0
-}
{- $prop-size-singleton
#p:prop-size-singleton#

[prop-size-singleton]:
    The 'singleton' 'Bag' has @'size' = 1@.
    
    > prop-size-singleton
    >   : ∀ (x : a) → size (singleton x) ≡ 1
-}
-- * Properties
{- $prop-filter-cartesianProduct
#p:prop-filter-cartesianProduct#

[prop-filter-cartesianProduct]:
    Independent filters promote through cartesian product.
    
    > prop-filter-cartesianProduct
    >   : ∀ (p : a → Bool) (q : b → Bool) (xs : Bag a) (ys : Bag b)
    >   → filter (λ xy → p (fst xy) && q (snd xy)) (cartesianProduct xs ys)
    >     ≡ cartesianProduct (filter p xs) (filter q ys)
-}
{- $prop-fromList-++
#p:prop-fromList-++#

[prop-fromList-++]:
    'fromList' maps list concatenation to 'union' of 'Bag's.
    
    > prop-fromList-++
    >   : ∀ (xs ys : List a) 
    >   → fromList (xs ++ ys) ≡ fromList xs <> fromList ys
-}
{- $prop-fromList-empty
#p:prop-fromList-empty#

[prop-fromList-empty]:
    'fromList' maps single element lists to singleton
    
    > prop-fromList-empty : ∀ {a} → fromList {a} [] ≡ mempty
-}
{- $prop-fromList-filter
#p:prop-fromList-filter#

[prop-fromList-filter]:
    'fromList' maps 'Data.List.filter' to 'filter'.
    
    > prop-fromList-filter
    >   : ∀ (p : a → Bool) (xs : List a) 
    >   → fromList (List.filter p xs) ≡ filter p (fromList xs)
-}
{- $prop-morphism-cartesianProduct-1
#p:prop-morphism-cartesianProduct-1#

[prop-morphism-cartesianProduct-1]:
    'cartesianProduct' is a monoid homomorphism in its first argument.
    
    > prop-morphism-cartesianProduct-1
    >   : ∀ (ys : Bag b)
    >   → Monoid.IsHomomorphism (λ xs → cartesianProduct {a} {b} xs ys)
-}
{- $prop-morphism-cartesianProduct-2
#p:prop-morphism-cartesianProduct-2#

[prop-morphism-cartesianProduct-2]:
    'cartesianProduct' is a monoid homomorphism in its second argument.
    
    > prop-morphism-cartesianProduct-2
    >   : ∀ (xs : Bag a)
    >   → Monoid.IsHomomorphism (λ (ys : Bag b) → cartesianProduct {a} {b} xs ys)
-}
{- $prop-morphism-equijoin-1
#p:prop-morphism-equijoin-1#

[prop-morphism-equijoin-1]:
    'equijoin' is a monoid homomorphism in its first argument.
    
    > prop-morphism-equijoin-1
    >   : ∀ {k} ⦃ _ : Eq k ⦄ (f : a → k) (g : b → k) (ys : Bag b)
    >   → Monoid.IsHomomorphism (λ xs → equijoin f g xs ys)
-}
{- $prop-morphism-equijoin-2
#p:prop-morphism-equijoin-2#

[prop-morphism-equijoin-2]:
    'equijoin' is a monoid homomorphism in its second argument.
    
    > prop-morphism-equijoin-2
    >   : ∀ {k} ⦃ _ : Eq k ⦄ (f : a → k) (g : b → k) (xs : Bag a)
    >   → Monoid.IsHomomorphism (λ ys → equijoin f g xs ys)
-}
{- $prop-morphism-filter
#p:prop-morphism-filter#

[prop-morphism-filter]:
    'filter' is a monoid homomorphism.
    
    > prop-morphism-filter
    >   : ∀ (p : a → Bool) → Monoid.IsHomomorphism (filter p)
-}
{- $prop-morphism-fromList
#p:prop-morphism-fromList#

[prop-morphism-fromList]:
    'fromList' is a monoid homomorphism.
    
    > prop-morphism-fromList
    >   : Monoid.IsHomomorphism (fromList {a})
-}
{- $prop-morphism-mmember
#p:prop-morphism-mmember#

[prop-morphism-mmember]:
    'member' is a monoid homomorphism.
    
    > prop-morphism-mmember
    >   : ∀ ⦃ _ : Eq a ⦄ (x : a)
    >   → Monoid.IsHomomorphism ⦃ iMonoidBag {a} ⦄ (mmember x)
-}
{- $prop-morphism-mnull
#p:prop-morphism-mnull#

[prop-morphism-mnull]:
    'null' is a monoid homomorphism.
    
    > prop-morphism-mnull
    >   : Monoid.IsHomomorphism ⦃ iMonoidBag {a} ⦄ mnull
-}
{- $prop-morphism-msize
#p:prop-morphism-msize#

[prop-morphism-msize]:
    'size' is a monoid homomorphism.
    
    > prop-morphism-msize
    >   : Monoid.IsHomomorphism ⦃ iMonoidBag {a} ⦄ msize
-}
{- $prop-null-cartesianProduct
#p:prop-null-cartesianProduct#

[prop-null-cartesianProduct]:
    A 'cartesianProduct' is empty if and only if both arguments are empty.
    
    > prop-null-cartesianProduct
    >   : ∀ (xs : Bag a) (ys : Bag b)
    >   → null (cartesianProduct xs ys) ≡ (null xs || null ys)
-}
{- $prop-size-<>
#p:prop-size-<>#

[prop-size-<>]:
    The union of 'Bags' adds their sizes.
    
    > prop-size-<>
    >   : ∀ (xs ys : Bag a) → size (xs <> ys) ≡ size xs + size ys
-}
{- $prop-size-fromList
#p:prop-size-fromList#

[prop-size-fromList]:
    'fromList' preserves list length.
    
    > prop-size-fromList
    >   : ∀ (xs : List a)
    >   → size (fromList xs) ≡ length xs
-}
{- $prop-size-mempty
#p:prop-size-mempty#

[prop-size-mempty]:
    The empty 'Bag' has @'size' = 0@.
    
    > prop-size-mempty
    >   : ∀ {a} → size {a} mempty ≡ 0
-}
{- $prop-size-singleton
#p:prop-size-singleton#

[prop-size-singleton]:
    The 'singleton' 'Bag' has @'size' = 1@.
    
    > prop-size-singleton
    >   : ∀ (x : a) → size (singleton x) ≡ 1
-}
-- * Properties
{- $prop-filter-cartesianProduct
#p:prop-filter-cartesianProduct#

[prop-filter-cartesianProduct]:
    Independent filters promote through cartesian product.
    
    > prop-filter-cartesianProduct
    >   : ∀ (p : a → Bool) (q : b → Bool) (xs : Bag a) (ys : Bag b)
    >   → filter (λ xy → p (fst xy) && q (snd xy)) (cartesianProduct xs ys)
    >     ≡ cartesianProduct (filter p xs) (filter q ys)
-}
{- $prop-fromList-++
#p:prop-fromList-++#

[prop-fromList-++]:
    'fromList' maps list concatenation to 'union' of 'Bag's.
    
    > prop-fromList-++
    >   : ∀ (xs ys : List a) 
    >   → fromList (xs ++ ys) ≡ fromList xs <> fromList ys
-}
{- $prop-fromList-empty
#p:prop-fromList-empty#

[prop-fromList-empty]:
    'fromList' maps single element lists to singleton
    
    > prop-fromList-empty : ∀ {a} → fromList {a} [] ≡ mempty
-}
{- $prop-fromList-filter
#p:prop-fromList-filter#

[prop-fromList-filter]:
    'fromList' maps 'Data.List.filter' to 'filter'.
    
    > prop-fromList-filter
    >   : ∀ (p : a → Bool) (xs : List a) 
    >   → fromList (List.filter p xs) ≡ filter p (fromList xs)
-}
{- $prop-morphism-cartesianProduct-1
#p:prop-morphism-cartesianProduct-1#

[prop-morphism-cartesianProduct-1]:
    'cartesianProduct' is a monoid homomorphism in its first argument.
    
    > prop-morphism-cartesianProduct-1
    >   : ∀ (ys : Bag b)
    >   → Monoid.IsHomomorphism (λ xs → cartesianProduct {a} {b} xs ys)
-}
{- $prop-morphism-cartesianProduct-2
#p:prop-morphism-cartesianProduct-2#

[prop-morphism-cartesianProduct-2]:
    'cartesianProduct' is a monoid homomorphism in its second argument.
    
    > prop-morphism-cartesianProduct-2
    >   : ∀ (xs : Bag a)
    >   → Monoid.IsHomomorphism (λ (ys : Bag b) → cartesianProduct {a} {b} xs ys)
-}
{- $prop-morphism-equijoin-1
#p:prop-morphism-equijoin-1#

[prop-morphism-equijoin-1]:
    'equijoin' is a monoid homomorphism in its first argument.
    
    > prop-morphism-equijoin-1
    >   : ∀ {k} ⦃ _ : Eq k ⦄ (f : a → k) (g : b → k) (ys : Bag b)
    >   → Monoid.IsHomomorphism (λ xs → equijoin f g xs ys)
-}
{- $prop-morphism-equijoin-2
#p:prop-morphism-equijoin-2#

[prop-morphism-equijoin-2]:
    'equijoin' is a monoid homomorphism in its second argument.
    
    > prop-morphism-equijoin-2
    >   : ∀ {k} ⦃ _ : Eq k ⦄ (f : a → k) (g : b → k) (xs : Bag a)
    >   → Monoid.IsHomomorphism (λ ys → equijoin f g xs ys)
-}
{- $prop-morphism-filter
#p:prop-morphism-filter#

[prop-morphism-filter]:
    'filter' is a monoid homomorphism.
    
    > prop-morphism-filter
    >   : ∀ (p : a → Bool) → Monoid.IsHomomorphism (filter p)
-}
{- $prop-morphism-fromList
#p:prop-morphism-fromList#

[prop-morphism-fromList]:
    'fromList' is a monoid homomorphism.
    
    > prop-morphism-fromList
    >   : Monoid.IsHomomorphism (fromList {a})
-}
{- $prop-morphism-mmember
#p:prop-morphism-mmember#

[prop-morphism-mmember]:
    'member' is a monoid homomorphism.
    
    > prop-morphism-mmember
    >   : ∀ ⦃ _ : Eq a ⦄ (x : a)
    >   → Monoid.IsHomomorphism ⦃ iMonoidBag {a} ⦄ (mmember x)
-}
{- $prop-morphism-mnull
#p:prop-morphism-mnull#

[prop-morphism-mnull]:
    'null' is a monoid homomorphism.
    
    > prop-morphism-mnull
    >   : Monoid.IsHomomorphism ⦃ iMonoidBag {a} ⦄ mnull
-}
{- $prop-morphism-msize
#p:prop-morphism-msize#

[prop-morphism-msize]:
    'size' is a monoid homomorphism.
    
    > prop-morphism-msize
    >   : Monoid.IsHomomorphism ⦃ iMonoidBag {a} ⦄ msize
-}
{- $prop-null-cartesianProduct
#p:prop-null-cartesianProduct#

[prop-null-cartesianProduct]:
    A 'cartesianProduct' is empty if and only if both arguments are empty.
    
    > prop-null-cartesianProduct
    >   : ∀ (xs : Bag a) (ys : Bag b)
    >   → null (cartesianProduct xs ys) ≡ (null xs || null ys)
-}
{- $prop-size-<>
#p:prop-size-<>#

[prop-size-<>]:
    The union of 'Bags' adds their sizes.
    
    > prop-size-<>
    >   : ∀ (xs ys : Bag a) → size (xs <> ys) ≡ size xs + size ys
-}
{- $prop-size-fromList
#p:prop-size-fromList#

[prop-size-fromList]:
    'fromList' preserves list length.
    
    > prop-size-fromList
    >   : ∀ (xs : List a)
    >   → size (fromList xs) ≡ length xs
-}
{- $prop-size-mempty
#p:prop-size-mempty#

[prop-size-mempty]:
    The empty 'Bag' has @'size' = 0@.
    
    > prop-size-mempty
    >   : ∀ {a} → size {a} mempty ≡ 0
-}
{- $prop-size-singleton
#p:prop-size-singleton#

[prop-size-singleton]:
    The 'singleton' 'Bag' has @'size' = 1@.
    
    > prop-size-singleton
    >   : ∀ (x : a) → size (singleton x) ≡ 1
-}
-- * Properties
{- $prop-filter-cartesianProduct
#p:prop-filter-cartesianProduct#

[prop-filter-cartesianProduct]:
    Independent filters promote through cartesian product.
    
    > prop-filter-cartesianProduct
    >   : ∀ (p : a → Bool) (q : b → Bool) (xs : Bag a) (ys : Bag b)
    >   → filter (λ xy → p (fst xy) && q (snd xy)) (cartesianProduct xs ys)
    >     ≡ cartesianProduct (filter p xs) (filter q ys)
-}
{- $prop-fromList-++
#p:prop-fromList-++#

[prop-fromList-++]:
    'fromList' maps list concatenation to 'union' of 'Bag's.
    
    > prop-fromList-++
    >   : ∀ (xs ys : List a) 
    >   → fromList (xs ++ ys) ≡ fromList xs <> fromList ys
-}
{- $prop-fromList-empty
#p:prop-fromList-empty#

[prop-fromList-empty]:
    'fromList' maps single element lists to singleton
    
    > prop-fromList-empty : ∀ {a} → fromList {a} [] ≡ mempty
-}
{- $prop-fromList-filter
#p:prop-fromList-filter#

[prop-fromList-filter]:
    'fromList' maps 'Data.List.filter' to 'filter'.
    
    > prop-fromList-filter
    >   : ∀ (p : a → Bool) (xs : List a) 
    >   → fromList (List.filter p xs) ≡ filter p (fromList xs)
-}
{- $prop-morphism-cartesianProduct-1
#p:prop-morphism-cartesianProduct-1#

[prop-morphism-cartesianProduct-1]:
    'cartesianProduct' is a monoid homomorphism in its first argument.
    
    > prop-morphism-cartesianProduct-1
    >   : ∀ (ys : Bag b)
    >   → Monoid.IsHomomorphism (λ xs → cartesianProduct {a} {b} xs ys)
-}
{- $prop-morphism-cartesianProduct-2
#p:prop-morphism-cartesianProduct-2#

[prop-morphism-cartesianProduct-2]:
    'cartesianProduct' is a monoid homomorphism in its second argument.
    
    > prop-morphism-cartesianProduct-2
    >   : ∀ (xs : Bag a)
    >   → Monoid.IsHomomorphism (λ (ys : Bag b) → cartesianProduct {a} {b} xs ys)
-}
{- $prop-morphism-equijoin-1
#p:prop-morphism-equijoin-1#

[prop-morphism-equijoin-1]:
    'equijoin' is a monoid homomorphism in its first argument.
    
    > prop-morphism-equijoin-1
    >   : ∀ {k} ⦃ _ : Eq k ⦄ (f : a → k) (g : b → k) (ys : Bag b)
    >   → Monoid.IsHomomorphism (λ xs → equijoin f g xs ys)
-}
{- $prop-morphism-equijoin-2
#p:prop-morphism-equijoin-2#

[prop-morphism-equijoin-2]:
    'equijoin' is a monoid homomorphism in its second argument.
    
    > prop-morphism-equijoin-2
    >   : ∀ {k} ⦃ _ : Eq k ⦄ (f : a → k) (g : b → k) (xs : Bag a)
    >   → Monoid.IsHomomorphism (λ ys → equijoin f g xs ys)
-}
{- $prop-morphism-filter
#p:prop-morphism-filter#

[prop-morphism-filter]:
    'filter' is a monoid homomorphism.
    
    > prop-morphism-filter
    >   : ∀ (p : a → Bool) → Monoid.IsHomomorphism (filter p)
-}
{- $prop-morphism-fromList
#p:prop-morphism-fromList#

[prop-morphism-fromList]:
    'fromList' is a monoid homomorphism.
    
    > prop-morphism-fromList
    >   : Monoid.IsHomomorphism (fromList {a})
-}
{- $prop-morphism-mmember
#p:prop-morphism-mmember#

[prop-morphism-mmember]:
    'member' is a monoid homomorphism.
    
    > prop-morphism-mmember
    >   : ∀ ⦃ _ : Eq a ⦄ (x : a)
    >   → Monoid.IsHomomorphism ⦃ iMonoidBag {a} ⦄ (mmember x)
-}
{- $prop-morphism-mnull
#p:prop-morphism-mnull#

[prop-morphism-mnull]:
    'null' is a monoid homomorphism.
    
    > prop-morphism-mnull
    >   : Monoid.IsHomomorphism ⦃ iMonoidBag {a} ⦄ mnull
-}
{- $prop-morphism-msize
#p:prop-morphism-msize#

[prop-morphism-msize]:
    'size' is a monoid homomorphism.
    
    > prop-morphism-msize
    >   : Monoid.IsHomomorphism ⦃ iMonoidBag {a} ⦄ msize
-}
{- $prop-null-cartesianProduct
#p:prop-null-cartesianProduct#

[prop-null-cartesianProduct]:
    A 'cartesianProduct' is empty if and only if both arguments are empty.
    
    > prop-null-cartesianProduct
    >   : ∀ (xs : Bag a) (ys : Bag b)
    >   → null (cartesianProduct xs ys) ≡ (null xs || null ys)
-}
{- $prop-size-<>
#p:prop-size-<>#

[prop-size-<>]:
    The union of 'Bags' adds their sizes.
    
    > prop-size-<>
    >   : ∀ (xs ys : Bag a) → size (xs <> ys) ≡ size xs + size ys
-}
{- $prop-size-fromList
#p:prop-size-fromList#

[prop-size-fromList]:
    'fromList' preserves list length.
    
    > prop-size-fromList
    >   : ∀ (xs : List a)
    >   → size (fromList xs) ≡ length xs
-}
{- $prop-size-mempty
#p:prop-size-mempty#

[prop-size-mempty]:
    The empty 'Bag' has @'size' = 0@.
    
    > prop-size-mempty
    >   : ∀ {a} → size {a} mempty ≡ 0
-}
{- $prop-size-singleton
#p:prop-size-singleton#

[prop-size-singleton]:
    The 'singleton' 'Bag' has @'size' = 1@.
    
    > prop-size-singleton
    >   : ∀ (x : a) → size (singleton x) ≡ 1
-}
-- * Properties
{- $prop-filter-cartesianProduct
#p:prop-filter-cartesianProduct#

[prop-filter-cartesianProduct]:
    Independent filters promote through cartesian product.
    
    > prop-filter-cartesianProduct
    >   : ∀ (p : a → Bool) (q : b → Bool) (xs : Bag a) (ys : Bag b)
    >   → filter (λ xy → p (fst xy) && q (snd xy)) (cartesianProduct xs ys)
    >     ≡ cartesianProduct (filter p xs) (filter q ys)
-}
{- $prop-fromList-++
#p:prop-fromList-++#

[prop-fromList-++]:
    'fromList' maps list concatenation to 'union' of 'Bag's.
    
    > prop-fromList-++
    >   : ∀ (xs ys : List a) 
    >   → fromList (xs ++ ys) ≡ fromList xs <> fromList ys
-}
{- $prop-fromList-empty
#p:prop-fromList-empty#

[prop-fromList-empty]:
    'fromList' maps single element lists to singleton
    
    > prop-fromList-empty : ∀ {a} → fromList {a} [] ≡ mempty
-}
{- $prop-fromList-filter
#p:prop-fromList-filter#

[prop-fromList-filter]:
    'fromList' maps 'Data.List.filter' to 'filter'.
    
    > prop-fromList-filter
    >   : ∀ (p : a → Bool) (xs : List a) 
    >   → fromList (List.filter p xs) ≡ filter p (fromList xs)
-}
{- $prop-morphism-cartesianProduct-1
#p:prop-morphism-cartesianProduct-1#

[prop-morphism-cartesianProduct-1]:
    'cartesianProduct' is a monoid homomorphism in its first argument.
    
    > prop-morphism-cartesianProduct-1
    >   : ∀ (ys : Bag b)
    >   → Monoid.IsHomomorphism (λ xs → cartesianProduct {a} {b} xs ys)
-}
{- $prop-morphism-cartesianProduct-2
#p:prop-morphism-cartesianProduct-2#

[prop-morphism-cartesianProduct-2]:
    'cartesianProduct' is a monoid homomorphism in its second argument.
    
    > prop-morphism-cartesianProduct-2
    >   : ∀ (xs : Bag a)
    >   → Monoid.IsHomomorphism (λ (ys : Bag b) → cartesianProduct {a} {b} xs ys)
-}
{- $prop-morphism-equijoin-1
#p:prop-morphism-equijoin-1#

[prop-morphism-equijoin-1]:
    'equijoin' is a monoid homomorphism in its first argument.
    
    > prop-morphism-equijoin-1
    >   : ∀ {k} ⦃ _ : Eq k ⦄ (f : a → k) (g : b → k) (ys : Bag b)
    >   → Monoid.IsHomomorphism (λ xs → equijoin f g xs ys)
-}
{- $prop-morphism-equijoin-2
#p:prop-morphism-equijoin-2#

[prop-morphism-equijoin-2]:
    'equijoin' is a monoid homomorphism in its second argument.
    
    > prop-morphism-equijoin-2
    >   : ∀ {k} ⦃ _ : Eq k ⦄ (f : a → k) (g : b → k) (xs : Bag a)
    >   → Monoid.IsHomomorphism (λ ys → equijoin f g xs ys)
-}
{- $prop-morphism-filter
#p:prop-morphism-filter#

[prop-morphism-filter]:
    'filter' is a monoid homomorphism.
    
    > prop-morphism-filter
    >   : ∀ (p : a → Bool) → Monoid.IsHomomorphism (filter p)
-}
{- $prop-morphism-fromList
#p:prop-morphism-fromList#

[prop-morphism-fromList]:
    'fromList' is a monoid homomorphism.
    
    > prop-morphism-fromList
    >   : Monoid.IsHomomorphism (fromList {a})
-}
{- $prop-morphism-mmember
#p:prop-morphism-mmember#

[prop-morphism-mmember]:
    'member' is a monoid homomorphism.
    
    > prop-morphism-mmember
    >   : ∀ ⦃ _ : Eq a ⦄ (x : a)
    >   → Monoid.IsHomomorphism ⦃ iMonoidBag {a} ⦄ (mmember x)
-}
{- $prop-morphism-mnull
#p:prop-morphism-mnull#

[prop-morphism-mnull]:
    'null' is a monoid homomorphism.
    
    > prop-morphism-mnull
    >   : Monoid.IsHomomorphism ⦃ iMonoidBag {a} ⦄ mnull
-}
{- $prop-morphism-msize
#p:prop-morphism-msize#

[prop-morphism-msize]:
    'size' is a monoid homomorphism.
    
    > prop-morphism-msize
    >   : Monoid.IsHomomorphism ⦃ iMonoidBag {a} ⦄ msize
-}
{- $prop-null-cartesianProduct
#p:prop-null-cartesianProduct#

[prop-null-cartesianProduct]:
    A 'cartesianProduct' is empty if and only if both arguments are empty.
    
    > prop-null-cartesianProduct
    >   : ∀ (xs : Bag a) (ys : Bag b)
    >   → null (cartesianProduct xs ys) ≡ (null xs || null ys)
-}
{- $prop-size-<>
#p:prop-size-<>#

[prop-size-<>]:
    The union of 'Bags' adds their sizes.
    
    > prop-size-<>
    >   : ∀ (xs ys : Bag a) → size (xs <> ys) ≡ size xs + size ys
-}
{- $prop-size-fromList
#p:prop-size-fromList#

[prop-size-fromList]:
    'fromList' preserves list length.
    
    > prop-size-fromList
    >   : ∀ (xs : List a)
    >   → size (fromList xs) ≡ length xs
-}
{- $prop-size-mempty
#p:prop-size-mempty#

[prop-size-mempty]:
    The empty 'Bag' has @'size' = 0@.
    
    > prop-size-mempty
    >   : ∀ {a} → size {a} mempty ≡ 0
-}
{- $prop-size-singleton
#p:prop-size-singleton#

[prop-size-singleton]:
    The 'singleton' 'Bag' has @'size' = 1@.
    
    > prop-size-singleton
    >   : ∀ (x : a) → size (singleton x) ≡ 1
-}
-- * Properties
{- $prop-filter-cartesianProduct
#p:prop-filter-cartesianProduct#

[prop-filter-cartesianProduct]:
    Independent filters promote through cartesian product.
    
    > prop-filter-cartesianProduct
    >   : ∀ (p : a → Bool) (q : b → Bool) (xs : Bag a) (ys : Bag b)
    >   → filter (λ xy → p (fst xy) && q (snd xy)) (cartesianProduct xs ys)
    >     ≡ cartesianProduct (filter p xs) (filter q ys)
-}
{- $prop-fromList-++
#p:prop-fromList-++#

[prop-fromList-++]:
    'fromList' maps list concatenation to 'union' of 'Bag's.
    
    > prop-fromList-++
    >   : ∀ (xs ys : List a) 
    >   → fromList (xs ++ ys) ≡ fromList xs <> fromList ys
-}
{- $prop-fromList-empty
#p:prop-fromList-empty#

[prop-fromList-empty]:
    'fromList' maps single element lists to singleton
    
    > prop-fromList-empty : ∀ {a} → fromList {a} [] ≡ mempty
-}
{- $prop-fromList-filter
#p:prop-fromList-filter#

[prop-fromList-filter]:
    'fromList' maps 'Data.List.filter' to 'filter'.
    
    > prop-fromList-filter
    >   : ∀ (p : a → Bool) (xs : List a) 
    >   → fromList (List.filter p xs) ≡ filter p (fromList xs)
-}
{- $prop-morphism-cartesianProduct-1
#p:prop-morphism-cartesianProduct-1#

[prop-morphism-cartesianProduct-1]:
    'cartesianProduct' is a monoid homomorphism in its first argument.
    
    > prop-morphism-cartesianProduct-1
    >   : ∀ (ys : Bag b)
    >   → Monoid.IsHomomorphism (λ xs → cartesianProduct {a} {b} xs ys)
-}
{- $prop-morphism-cartesianProduct-2
#p:prop-morphism-cartesianProduct-2#

[prop-morphism-cartesianProduct-2]:
    'cartesianProduct' is a monoid homomorphism in its second argument.
    
    > prop-morphism-cartesianProduct-2
    >   : ∀ (xs : Bag a)
    >   → Monoid.IsHomomorphism (λ (ys : Bag b) → cartesianProduct {a} {b} xs ys)
-}
{- $prop-morphism-equijoin-1
#p:prop-morphism-equijoin-1#

[prop-morphism-equijoin-1]:
    'equijoin' is a monoid homomorphism in its first argument.
    
    > prop-morphism-equijoin-1
    >   : ∀ {k} ⦃ _ : Eq k ⦄ (f : a → k) (g : b → k) (ys : Bag b)
    >   → Monoid.IsHomomorphism (λ xs → equijoin f g xs ys)
-}
{- $prop-morphism-equijoin-2
#p:prop-morphism-equijoin-2#

[prop-morphism-equijoin-2]:
    'equijoin' is a monoid homomorphism in its second argument.
    
    > prop-morphism-equijoin-2
    >   : ∀ {k} ⦃ _ : Eq k ⦄ (f : a → k) (g : b → k) (xs : Bag a)
    >   → Monoid.IsHomomorphism (λ ys → equijoin f g xs ys)
-}
{- $prop-morphism-filter
#p:prop-morphism-filter#

[prop-morphism-filter]:
    'filter' is a monoid homomorphism.
    
    > prop-morphism-filter
    >   : ∀ (p : a → Bool) → Monoid.IsHomomorphism (filter p)
-}
{- $prop-morphism-fromList
#p:prop-morphism-fromList#

[prop-morphism-fromList]:
    'fromList' is a monoid homomorphism.
    
    > prop-morphism-fromList
    >   : Monoid.IsHomomorphism (fromList {a})
-}
{- $prop-morphism-mmember
#p:prop-morphism-mmember#

[prop-morphism-mmember]:
    'member' is a monoid homomorphism.
    
    > prop-morphism-mmember
    >   : ∀ ⦃ _ : Eq a ⦄ (x : a)
    >   → Monoid.IsHomomorphism ⦃ iMonoidBag {a} ⦄ (mmember x)
-}
{- $prop-morphism-mnull
#p:prop-morphism-mnull#

[prop-morphism-mnull]:
    'null' is a monoid homomorphism.
    
    > prop-morphism-mnull
    >   : Monoid.IsHomomorphism ⦃ iMonoidBag {a} ⦄ mnull
-}
{- $prop-morphism-msize
#p:prop-morphism-msize#

[prop-morphism-msize]:
    'size' is a monoid homomorphism.
    
    > prop-morphism-msize
    >   : Monoid.IsHomomorphism ⦃ iMonoidBag {a} ⦄ msize
-}
{- $prop-null-cartesianProduct
#p:prop-null-cartesianProduct#

[prop-null-cartesianProduct]:
    A 'cartesianProduct' is empty if and only if both arguments are empty.
    
    > prop-null-cartesianProduct
    >   : ∀ (xs : Bag a) (ys : Bag b)
    >   → null (cartesianProduct xs ys) ≡ (null xs || null ys)
-}
{- $prop-size-<>
#p:prop-size-<>#

[prop-size-<>]:
    The union of 'Bags' adds their sizes.
    
    > prop-size-<>
    >   : ∀ (xs ys : Bag a) → size (xs <> ys) ≡ size xs + size ys
-}
{- $prop-size-fromList
#p:prop-size-fromList#

[prop-size-fromList]:
    'fromList' preserves list length.
    
    > prop-size-fromList
    >   : ∀ (xs : List a)
    >   → size (fromList xs) ≡ length xs
-}
{- $prop-size-mempty
#p:prop-size-mempty#

[prop-size-mempty]:
    The empty 'Bag' has @'size' = 0@.
    
    > prop-size-mempty
    >   : ∀ {a} → size {a} mempty ≡ 0
-}
{- $prop-size-singleton
#p:prop-size-singleton#

[prop-size-singleton]:
    The 'singleton' 'Bag' has @'size' = 1@.
    
    > prop-size-singleton
    >   : ∀ (x : a) → size (singleton x) ≡ 1
-}
-- * Properties
{- $prop-filter-cartesianProduct
#p:prop-filter-cartesianProduct#

[prop-filter-cartesianProduct]:
    Independent filters promote through cartesian product.
    
    > prop-filter-cartesianProduct
    >   : ∀ (p : a → Bool) (q : b → Bool) (xs : Bag a) (ys : Bag b)
    >   → filter (λ xy → p (fst xy) && q (snd xy)) (cartesianProduct xs ys)
    >     ≡ cartesianProduct (filter p xs) (filter q ys)
-}
{- $prop-fromList-++
#p:prop-fromList-++#

[prop-fromList-++]:
    'fromList' maps list concatenation to 'union' of 'Bag's.
    
    > prop-fromList-++
    >   : ∀ (xs ys : List a) 
    >   → fromList (xs ++ ys) ≡ fromList xs <> fromList ys
-}
{- $prop-fromList-empty
#p:prop-fromList-empty#

[prop-fromList-empty]:
    'fromList' maps single element lists to singleton
    
    > prop-fromList-empty : ∀ {a} → fromList {a} [] ≡ mempty
-}
{- $prop-fromList-filter
#p:prop-fromList-filter#

[prop-fromList-filter]:
    'fromList' maps 'Data.List.filter' to 'filter'.
    
    > prop-fromList-filter
    >   : ∀ (p : a → Bool) (xs : List a) 
    >   → fromList (List.filter p xs) ≡ filter p (fromList xs)
-}
{- $prop-morphism-cartesianProduct-1
#p:prop-morphism-cartesianProduct-1#

[prop-morphism-cartesianProduct-1]:
    'cartesianProduct' is a monoid homomorphism in its first argument.
    
    > prop-morphism-cartesianProduct-1
    >   : ∀ (ys : Bag b)
    >   → Monoid.IsHomomorphism (λ xs → cartesianProduct {a} {b} xs ys)
-}
{- $prop-morphism-cartesianProduct-2
#p:prop-morphism-cartesianProduct-2#

[prop-morphism-cartesianProduct-2]:
    'cartesianProduct' is a monoid homomorphism in its second argument.
    
    > prop-morphism-cartesianProduct-2
    >   : ∀ (xs : Bag a)
    >   → Monoid.IsHomomorphism (λ (ys : Bag b) → cartesianProduct {a} {b} xs ys)
-}
{- $prop-morphism-equijoin-1
#p:prop-morphism-equijoin-1#

[prop-morphism-equijoin-1]:
    'equijoin' is a monoid homomorphism in its first argument.
    
    > prop-morphism-equijoin-1
    >   : ∀ {k} ⦃ _ : Eq k ⦄ (f : a → k) (g : b → k) (ys : Bag b)
    >   → Monoid.IsHomomorphism (λ xs → equijoin f g xs ys)
-}
{- $prop-morphism-equijoin-2
#p:prop-morphism-equijoin-2#

[prop-morphism-equijoin-2]:
    'equijoin' is a monoid homomorphism in its second argument.
    
    > prop-morphism-equijoin-2
    >   : ∀ {k} ⦃ _ : Eq k ⦄ (f : a → k) (g : b → k) (xs : Bag a)
    >   → Monoid.IsHomomorphism (λ ys → equijoin f g xs ys)
-}
{- $prop-morphism-filter
#p:prop-morphism-filter#

[prop-morphism-filter]:
    'filter' is a monoid homomorphism.
    
    > prop-morphism-filter
    >   : ∀ (p : a → Bool) → Monoid.IsHomomorphism (filter p)
-}
{- $prop-morphism-fromList
#p:prop-morphism-fromList#

[prop-morphism-fromList]:
    'fromList' is a monoid homomorphism.
    
    > prop-morphism-fromList
    >   : Monoid.IsHomomorphism (fromList {a})
-}
{- $prop-morphism-mmember
#p:prop-morphism-mmember#

[prop-morphism-mmember]:
    'member' is a monoid homomorphism.
    
    > prop-morphism-mmember
    >   : ∀ ⦃ _ : Eq a ⦄ (x : a)
    >   → Monoid.IsHomomorphism ⦃ iMonoidBag {a} ⦄ (mmember x)
-}
{- $prop-morphism-mnull
#p:prop-morphism-mnull#

[prop-morphism-mnull]:
    'null' is a monoid homomorphism.
    
    > prop-morphism-mnull
    >   : Monoid.IsHomomorphism ⦃ iMonoidBag {a} ⦄ mnull
-}
{- $prop-morphism-msize
#p:prop-morphism-msize#

[prop-morphism-msize]:
    'size' is a monoid homomorphism.
    
    > prop-morphism-msize
    >   : Monoid.IsHomomorphism ⦃ iMonoidBag {a} ⦄ msize
-}
{- $prop-null-cartesianProduct
#p:prop-null-cartesianProduct#

[prop-null-cartesianProduct]:
    A 'cartesianProduct' is empty if and only if both arguments are empty.
    
    > prop-null-cartesianProduct
    >   : ∀ (xs : Bag a) (ys : Bag b)
    >   → null (cartesianProduct xs ys) ≡ (null xs || null ys)
-}
{- $prop-size-<>
#p:prop-size-<>#

[prop-size-<>]:
    The union of 'Bags' adds their sizes.
    
    > prop-size-<>
    >   : ∀ (xs ys : Bag a) → size (xs <> ys) ≡ size xs + size ys
-}
{- $prop-size-fromList
#p:prop-size-fromList#

[prop-size-fromList]:
    'fromList' preserves list length.
    
    > prop-size-fromList
    >   : ∀ (xs : List a)
    >   → size (fromList xs) ≡ length xs
-}
{- $prop-size-mempty
#p:prop-size-mempty#

[prop-size-mempty]:
    The empty 'Bag' has @'size' = 0@.
    
    > prop-size-mempty
    >   : ∀ {a} → size {a} mempty ≡ 0
-}
{- $prop-size-singleton
#p:prop-size-singleton#

[prop-size-singleton]:
    The 'singleton' 'Bag' has @'size' = 1@.
    
    > prop-size-singleton
    >   : ∀ (x : a) → size (singleton x) ≡ 1
-}
-- * Properties
{- $prop-filter-cartesianProduct
#p:prop-filter-cartesianProduct#

[prop-filter-cartesianProduct]:
    Independent filters promote through cartesian product.
    
    > prop-filter-cartesianProduct
    >   : ∀ (p : a → Bool) (q : b → Bool) (xs : Bag a) (ys : Bag b)
    >   → filter (λ xy → p (fst xy) && q (snd xy)) (cartesianProduct xs ys)
    >     ≡ cartesianProduct (filter p xs) (filter q ys)
-}
{- $prop-fromList-++
#p:prop-fromList-++#

[prop-fromList-++]:
    'fromList' maps list concatenation to 'union' of 'Bag's.
    
    > prop-fromList-++
    >   : ∀ (xs ys : List a) 
    >   → fromList (xs ++ ys) ≡ fromList xs <> fromList ys
-}
{- $prop-fromList-empty
#p:prop-fromList-empty#

[prop-fromList-empty]:
    'fromList' maps single element lists to singleton
    
    > prop-fromList-empty : ∀ {a} → fromList {a} [] ≡ mempty
-}
{- $prop-fromList-filter
#p:prop-fromList-filter#

[prop-fromList-filter]:
    'fromList' maps 'Data.List.filter' to 'filter'.
    
    > prop-fromList-filter
    >   : ∀ (p : a → Bool) (xs : List a) 
    >   → fromList (List.filter p xs) ≡ filter p (fromList xs)
-}
{- $prop-morphism-cartesianProduct-1
#p:prop-morphism-cartesianProduct-1#

[prop-morphism-cartesianProduct-1]:
    'cartesianProduct' is a monoid homomorphism in its first argument.
    
    > prop-morphism-cartesianProduct-1
    >   : ∀ (ys : Bag b)
    >   → Monoid.IsHomomorphism (λ xs → cartesianProduct {a} {b} xs ys)
-}
{- $prop-morphism-cartesianProduct-2
#p:prop-morphism-cartesianProduct-2#

[prop-morphism-cartesianProduct-2]:
    'cartesianProduct' is a monoid homomorphism in its second argument.
    
    > prop-morphism-cartesianProduct-2
    >   : ∀ (xs : Bag a)
    >   → Monoid.IsHomomorphism (λ (ys : Bag b) → cartesianProduct {a} {b} xs ys)
-}
{- $prop-morphism-equijoin-1
#p:prop-morphism-equijoin-1#

[prop-morphism-equijoin-1]:
    'equijoin' is a monoid homomorphism in its first argument.
    
    > prop-morphism-equijoin-1
    >   : ∀ {k} ⦃ _ : Eq k ⦄ (f : a → k) (g : b → k) (ys : Bag b)
    >   → Monoid.IsHomomorphism (λ xs → equijoin f g xs ys)
-}
{- $prop-morphism-equijoin-2
#p:prop-morphism-equijoin-2#

[prop-morphism-equijoin-2]:
    'equijoin' is a monoid homomorphism in its second argument.
    
    > prop-morphism-equijoin-2
    >   : ∀ {k} ⦃ _ : Eq k ⦄ (f : a → k) (g : b → k) (xs : Bag a)
    >   → Monoid.IsHomomorphism (λ ys → equijoin f g xs ys)
-}
{- $prop-morphism-filter
#p:prop-morphism-filter#

[prop-morphism-filter]:
    'filter' is a monoid homomorphism.
    
    > prop-morphism-filter
    >   : ∀ (p : a → Bool) → Monoid.IsHomomorphism (filter p)
-}
{- $prop-morphism-fromList
#p:prop-morphism-fromList#

[prop-morphism-fromList]:
    'fromList' is a monoid homomorphism.
    
    > prop-morphism-fromList
    >   : Monoid.IsHomomorphism (fromList {a})
-}
{- $prop-morphism-mmember
#p:prop-morphism-mmember#

[prop-morphism-mmember]:
    'member' is a monoid homomorphism.
    
    > prop-morphism-mmember
    >   : ∀ ⦃ _ : Eq a ⦄ (x : a)
    >   → Monoid.IsHomomorphism ⦃ iMonoidBag {a} ⦄ (mmember x)
-}
{- $prop-morphism-mnull
#p:prop-morphism-mnull#

[prop-morphism-mnull]:
    'null' is a monoid homomorphism.
    
    > prop-morphism-mnull
    >   : Monoid.IsHomomorphism ⦃ iMonoidBag {a} ⦄ mnull
-}
{- $prop-morphism-msize
#p:prop-morphism-msize#

[prop-morphism-msize]:
    'size' is a monoid homomorphism.
    
    > prop-morphism-msize
    >   : Monoid.IsHomomorphism ⦃ iMonoidBag {a} ⦄ msize
-}
{- $prop-null-cartesianProduct
#p:prop-null-cartesianProduct#

[prop-null-cartesianProduct]:
    A 'cartesianProduct' is empty if and only if both arguments are empty.
    
    > prop-null-cartesianProduct
    >   : ∀ (xs : Bag a) (ys : Bag b)
    >   → null (cartesianProduct xs ys) ≡ (null xs || null ys)
-}
{- $prop-size-<>
#p:prop-size-<>#

[prop-size-<>]:
    The union of 'Bags' adds their sizes.
    
    > prop-size-<>
    >   : ∀ (xs ys : Bag a) → size (xs <> ys) ≡ size xs + size ys
-}
{- $prop-size-fromList
#p:prop-size-fromList#

[prop-size-fromList]:
    'fromList' preserves list length.
    
    > prop-size-fromList
    >   : ∀ (xs : List a)
    >   → size (fromList xs) ≡ length xs
-}
{- $prop-size-mempty
#p:prop-size-mempty#

[prop-size-mempty]:
    The empty 'Bag' has @'size' = 0@.
    
    > prop-size-mempty
    >   : ∀ {a} → size {a} mempty ≡ 0
-}
{- $prop-size-singleton
#p:prop-size-singleton#

[prop-size-singleton]:
    The 'singleton' 'Bag' has @'size' = 1@.
    
    > prop-size-singleton
    >   : ∀ (x : a) → size (singleton x) ≡ 1
-}
-- * Properties
{- $prop-filter-cartesianProduct
#p:prop-filter-cartesianProduct#

[prop-filter-cartesianProduct]:
    Independent filters promote through cartesian product.
    
    > prop-filter-cartesianProduct
    >   : ∀ (p : a → Bool) (q : b → Bool) (xs : Bag a) (ys : Bag b)
    >   → filter (λ xy → p (fst xy) && q (snd xy)) (cartesianProduct xs ys)
    >     ≡ cartesianProduct (filter p xs) (filter q ys)
-}
{- $prop-fromList-++
#p:prop-fromList-++#

[prop-fromList-++]:
    'fromList' maps list concatenation to 'union' of 'Bag's.
    
    > prop-fromList-++
    >   : ∀ (xs ys : List a) 
    >   → fromList (xs ++ ys) ≡ fromList xs <> fromList ys
-}
{- $prop-fromList-empty
#p:prop-fromList-empty#

[prop-fromList-empty]:
    'fromList' maps single element lists to singleton
    
    > prop-fromList-empty : ∀ {a} → fromList {a} [] ≡ mempty
-}
{- $prop-fromList-filter
#p:prop-fromList-filter#

[prop-fromList-filter]:
    'fromList' maps 'Data.List.filter' to 'filter'.
    
    > prop-fromList-filter
    >   : ∀ (p : a → Bool) (xs : List a) 
    >   → fromList (List.filter p xs) ≡ filter p (fromList xs)
-}
{- $prop-morphism-cartesianProduct-1
#p:prop-morphism-cartesianProduct-1#

[prop-morphism-cartesianProduct-1]:
    'cartesianProduct' is a monoid homomorphism in its first argument.
    
    > prop-morphism-cartesianProduct-1
    >   : ∀ (ys : Bag b)
    >   → Monoid.IsHomomorphism (λ xs → cartesianProduct {a} {b} xs ys)
-}
{- $prop-morphism-cartesianProduct-2
#p:prop-morphism-cartesianProduct-2#

[prop-morphism-cartesianProduct-2]:
    'cartesianProduct' is a monoid homomorphism in its second argument.
    
    > prop-morphism-cartesianProduct-2
    >   : ∀ (xs : Bag a)
    >   → Monoid.IsHomomorphism (λ (ys : Bag b) → cartesianProduct {a} {b} xs ys)
-}
{- $prop-morphism-equijoin-1
#p:prop-morphism-equijoin-1#

[prop-morphism-equijoin-1]:
    'equijoin' is a monoid homomorphism in its first argument.
    
    > prop-morphism-equijoin-1
    >   : ∀ {k} ⦃ _ : Eq k ⦄ (f : a → k) (g : b → k) (ys : Bag b)
    >   → Monoid.IsHomomorphism (λ xs → equijoin f g xs ys)
-}
{- $prop-morphism-equijoin-2
#p:prop-morphism-equijoin-2#

[prop-morphism-equijoin-2]:
    'equijoin' is a monoid homomorphism in its second argument.
    
    > prop-morphism-equijoin-2
    >   : ∀ {k} ⦃ _ : Eq k ⦄ (f : a → k) (g : b → k) (xs : Bag a)
    >   → Monoid.IsHomomorphism (λ ys → equijoin f g xs ys)
-}
{- $prop-morphism-filter
#p:prop-morphism-filter#

[prop-morphism-filter]:
    'filter' is a monoid homomorphism.
    
    > prop-morphism-filter
    >   : ∀ (p : a → Bool) → Monoid.IsHomomorphism (filter p)
-}
{- $prop-morphism-fromList
#p:prop-morphism-fromList#

[prop-morphism-fromList]:
    'fromList' is a monoid homomorphism.
    
    > prop-morphism-fromList
    >   : Monoid.IsHomomorphism (fromList {a})
-}
{- $prop-morphism-mmember
#p:prop-morphism-mmember#

[prop-morphism-mmember]:
    'member' is a monoid homomorphism.
    
    > prop-morphism-mmember
    >   : ∀ ⦃ _ : Eq a ⦄ (x : a)
    >   → Monoid.IsHomomorphism ⦃ iMonoidBag {a} ⦄ (mmember x)
-}
{- $prop-morphism-mnull
#p:prop-morphism-mnull#

[prop-morphism-mnull]:
    'null' is a monoid homomorphism.
    
    > prop-morphism-mnull
    >   : Monoid.IsHomomorphism ⦃ iMonoidBag {a} ⦄ mnull
-}
{- $prop-morphism-msize
#p:prop-morphism-msize#

[prop-morphism-msize]:
    'size' is a monoid homomorphism.
    
    > prop-morphism-msize
    >   : Monoid.IsHomomorphism ⦃ iMonoidBag {a} ⦄ msize
-}
{- $prop-null-cartesianProduct
#p:prop-null-cartesianProduct#

[prop-null-cartesianProduct]:
    A 'cartesianProduct' is empty if and only if both arguments are empty.
    
    > prop-null-cartesianProduct
    >   : ∀ (xs : Bag a) (ys : Bag b)
    >   → null (cartesianProduct xs ys) ≡ (null xs || null ys)
-}
{- $prop-size-<>
#p:prop-size-<>#

[prop-size-<>]:
    The union of 'Bags' adds their sizes.
    
    > prop-size-<>
    >   : ∀ (xs ys : Bag a) → size (xs <> ys) ≡ size xs + size ys
-}
{- $prop-size-fromList
#p:prop-size-fromList#

[prop-size-fromList]:
    'fromList' preserves list length.
    
    > prop-size-fromList
    >   : ∀ (xs : List a)
    >   → size (fromList xs) ≡ length xs
-}
{- $prop-size-mempty
#p:prop-size-mempty#

[prop-size-mempty]:
    The empty 'Bag' has @'size' = 0@.
    
    > prop-size-mempty
    >   : ∀ {a} → size {a} mempty ≡ 0
-}
{- $prop-size-singleton
#p:prop-size-singleton#

[prop-size-singleton]:
    The 'singleton' 'Bag' has @'size' = 1@.
    
    > prop-size-singleton
    >   : ∀ (x : a) → size (singleton x) ≡ 1
-}
-- * Properties
{- $prop-filter-cartesianProduct
#p:prop-filter-cartesianProduct#

[prop-filter-cartesianProduct]:
    Independent filters promote through cartesian product.
    
    > prop-filter-cartesianProduct
    >   : ∀ (p : a → Bool) (q : b → Bool) (xs : Bag a) (ys : Bag b)
    >   → filter (λ xy → p (fst xy) && q (snd xy)) (cartesianProduct xs ys)
    >     ≡ cartesianProduct (filter p xs) (filter q ys)
-}
{- $prop-fromList-++
#p:prop-fromList-++#

[prop-fromList-++]:
    'fromList' maps list concatenation to 'union' of 'Bag's.
    
    > prop-fromList-++
    >   : ∀ (xs ys : List a) 
    >   → fromList (xs ++ ys) ≡ fromList xs <> fromList ys
-}
{- $prop-fromList-empty
#p:prop-fromList-empty#

[prop-fromList-empty]:
    'fromList' maps single element lists to singleton
    
    > prop-fromList-empty : ∀ {a} → fromList {a} [] ≡ mempty
-}
{- $prop-fromList-filter
#p:prop-fromList-filter#

[prop-fromList-filter]:
    'fromList' maps 'Data.List.filter' to 'filter'.
    
    > prop-fromList-filter
    >   : ∀ (p : a → Bool) (xs : List a) 
    >   → fromList (List.filter p xs) ≡ filter p (fromList xs)
-}
{- $prop-morphism-cartesianProduct-1
#p:prop-morphism-cartesianProduct-1#

[prop-morphism-cartesianProduct-1]:
    'cartesianProduct' is a monoid homomorphism in its first argument.
    
    > prop-morphism-cartesianProduct-1
    >   : ∀ (ys : Bag b)
    >   → Monoid.IsHomomorphism (λ xs → cartesianProduct {a} {b} xs ys)
-}
{- $prop-morphism-cartesianProduct-2
#p:prop-morphism-cartesianProduct-2#

[prop-morphism-cartesianProduct-2]:
    'cartesianProduct' is a monoid homomorphism in its second argument.
    
    > prop-morphism-cartesianProduct-2
    >   : ∀ (xs : Bag a)
    >   → Monoid.IsHomomorphism (λ (ys : Bag b) → cartesianProduct {a} {b} xs ys)
-}
{- $prop-morphism-equijoin-1
#p:prop-morphism-equijoin-1#

[prop-morphism-equijoin-1]:
    'equijoin' is a monoid homomorphism in its first argument.
    
    > prop-morphism-equijoin-1
    >   : ∀ {k} ⦃ _ : Eq k ⦄ (f : a → k) (g : b → k) (ys : Bag b)
    >   → Monoid.IsHomomorphism (λ xs → equijoin f g xs ys)
-}
{- $prop-morphism-equijoin-2
#p:prop-morphism-equijoin-2#

[prop-morphism-equijoin-2]:
    'equijoin' is a monoid homomorphism in its second argument.
    
    > prop-morphism-equijoin-2
    >   : ∀ {k} ⦃ _ : Eq k ⦄ (f : a → k) (g : b → k) (xs : Bag a)
    >   → Monoid.IsHomomorphism (λ ys → equijoin f g xs ys)
-}
{- $prop-morphism-filter
#p:prop-morphism-filter#

[prop-morphism-filter]:
    'filter' is a monoid homomorphism.
    
    > prop-morphism-filter
    >   : ∀ (p : a → Bool) → Monoid.IsHomomorphism (filter p)
-}
{- $prop-morphism-fromList
#p:prop-morphism-fromList#

[prop-morphism-fromList]:
    'fromList' is a monoid homomorphism.
    
    > prop-morphism-fromList
    >   : Monoid.IsHomomorphism (fromList {a})
-}
{- $prop-morphism-mmember
#p:prop-morphism-mmember#

[prop-morphism-mmember]:
    'member' is a monoid homomorphism.
    
    > prop-morphism-mmember
    >   : ∀ ⦃ _ : Eq a ⦄ (x : a)
    >   → Monoid.IsHomomorphism ⦃ iMonoidBag {a} ⦄ (mmember x)
-}
{- $prop-morphism-mnull
#p:prop-morphism-mnull#

[prop-morphism-mnull]:
    'null' is a monoid homomorphism.
    
    > prop-morphism-mnull
    >   : Monoid.IsHomomorphism ⦃ iMonoidBag {a} ⦄ mnull
-}
{- $prop-morphism-msize
#p:prop-morphism-msize#

[prop-morphism-msize]:
    'size' is a monoid homomorphism.
    
    > prop-morphism-msize
    >   : Monoid.IsHomomorphism ⦃ iMonoidBag {a} ⦄ msize
-}
{- $prop-null-cartesianProduct
#p:prop-null-cartesianProduct#

[prop-null-cartesianProduct]:
    A 'cartesianProduct' is empty if and only if both arguments are empty.
    
    > prop-null-cartesianProduct
    >   : ∀ (xs : Bag a) (ys : Bag b)
    >   → null (cartesianProduct xs ys) ≡ (null xs || null ys)
-}
{- $prop-size-<>
#p:prop-size-<>#

[prop-size-<>]:
    The union of 'Bags' adds their sizes.
    
    > prop-size-<>
    >   : ∀ (xs ys : Bag a) → size (xs <> ys) ≡ size xs + size ys
-}
{- $prop-size-fromList
#p:prop-size-fromList#

[prop-size-fromList]:
    'fromList' preserves list length.
    
    > prop-size-fromList
    >   : ∀ (xs : List a)
    >   → size (fromList xs) ≡ length xs
-}
{- $prop-size-mempty
#p:prop-size-mempty#

[prop-size-mempty]:
    The empty 'Bag' has @'size' = 0@.
    
    > prop-size-mempty
    >   : ∀ {a} → size {a} mempty ≡ 0
-}
{- $prop-size-singleton
#p:prop-size-singleton#

[prop-size-singleton]:
    The 'singleton' 'Bag' has @'size' = 1@.
    
    > prop-size-singleton
    >   : ∀ (x : a) → size (singleton x) ≡ 1
-}
