module Data.Bag 
    (
    -- * Type
    Bag,
    singleton,
    foldBag,
    -- * Operations
    -- ** Query
    null,
    size,
    count,
    member,
    -- ** Construction
    fromMaybe,
    fromList,
    -- ** Deletion
    deleteOne,
    -- ** Combine
    union,
    cartesianProduct,
    equijoin,
    -- ** Traversal
    map,
    concatMap,
    filter,
    -- * Properties
    -- ** Query
    -- $prop-size-mempty
    
    -- $prop-size-singleton
    
    -- $prop-size-<>
    
    -- ** Deletion
    -- $prop-deleteOne-member-True
    
    -- $prop-deleteOne-member-False
    
    )
    where

import Prelude hiding (null, filter, map, concatMap)

import Data.Bag.Def
import Data.Bag.Quotient
import Data.Bag.Found (deleteOne)

-- * Properties
{- $prop-deleteOne-member-False
#p:prop-deleteOne-member-False#

[prop-deleteOne-member-False]:
    If the given item is a 'member' of the 'Bag',
    'deleteOne' will leave the 'Bag' unchanged.
    
    > prop-deleteOne-member-False
    >   : ∀ ⦃ _ : Eq a ⦄ ⦃ _ : IsLawfulEq a ⦄ (x : a) (xs : Bag a)
    >   → member x xs ≡ False
    >   → xs ≡ deleteOne x xs
-}
{- $prop-deleteOne-member-True
#p:prop-deleteOne-member-True#

[prop-deleteOne-member-True]:
    If the given item is a 'member' of the 'Bag',
    'deleteOne' will remove it once.
    
    > @0 prop-deleteOne-member-True
    >   : ∀ ⦃ _ : Eq a ⦄ ⦃ @0 _ : IsLawfulEq a ⦄ (x : a) (xs : Bag a)
    >   → member x xs ≡ True
    >   → xs ≡ singleton x <> deleteOne x xs
-}
{- $prop-size-<>
#p:prop-size-<>#

[prop-size-<>]:
    The union of 'Bags' adds their sizes.
    
    > prop-size-<>
    >   : ∀ (xs ys : Bag a) → size (xs <> ys) ≡ size xs + size ys
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
