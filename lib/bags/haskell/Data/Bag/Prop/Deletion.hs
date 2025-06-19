{-# OPTIONS_GHC -Wno-unused-top-binds #-}

module Data.Bag.Prop.Deletion 
    (
    -- * Deletion
    -- ** deleteOne
    -- $prop-deleteOne-member-True
    
    -- $prop-deleteOne-member-False
    
    )
    where

import Prelude hiding (null, filter, lookup, map, concatMap, replicate)

dummyPropDeletion :: ()
dummyPropDeletion = ()

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
