{-# OPTIONS_GHC -Wno-unused-imports -Wno-dodgy-exports #-}

module Data.Bag 
    (
    -- * Type and Definitional Properties
    Bag,
    singleton,
    foldBag,
    -- * Operations
    -- ** Query
    null,
    mnull,
    size,
    msize,
    count,
    member,
    mmember,
    -- ** Construction
    fromMaybe,
    fromList,
    -- ** Deletion
    deleteOne,
    -- $prop-deleteOne-member-True
    
    -- $prop-deleteOne-member-False
    
    -- ** Combine
    union,
    cartesianProduct,
    equijoin,
    -- ** Traversal
    map,
    concatMap,
    filter,
    -- * Properties
    module Data.Bag.Prop,
    )
    where

import Prelude hiding (null, filter, lookup, map, concatMap)


import Data.Bag.Def
import Data.Bag.Quotient
import Data.Bag.Found (deleteOne)
import Data.Bag.Prop

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
