{-# OPTIONS_GHC -Wno-unused-imports -Wno-dodgy-exports #-}

module Data.Bag 
    (
    -- * Type and Definitional Properties
    Bag,
    singleton,
    foldBag,
    -- $prop-morphism-foldBag
    
    -- $prop-foldBag-singleton
    
    -- $prop-foldBag-unique
    
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
    module Data.Bag.Prop.Core,
    module Data.Bag.Prop.Deletion,
    module Data.Bag.Prop.Operations,
    )
    where

import Prelude hiding (null, filter, lookup, map, concatMap, replicate)


import Data.Bag.Def
import Data.Bag.Quotient
import Data.Bag.Found (deleteOne)
import Data.Bag.Prop.Core
import Data.Bag.Prop.Deletion
import Data.Bag.Prop.Operations

-- * Properties
{- $prop-foldBag-singleton
#p:prop-foldBag-singleton#

[prop-foldBag-singleton]:
    Universal property: Every 'Monoid' homomorphism
    (see "Data.Monoid.Morphism#g:1")
    factors through 'foldBag' and 'singleton'.
    
    > prop-foldBag-singleton
    >   : ∀ ⦃ _ : Monoid.Commutative b ⦄ (f : a → b) (x : a)
    >   → foldBag f (singleton x) ≡ f x
-}
{- $prop-foldBag-unique
#p:prop-foldBag-unique#

[prop-foldBag-unique]:
    Universal property: 'foldBag' is the unique homomorphism
    (see "Data.Monoid.Morphism#g:1").
    
    > prop-foldBag-unique
    >   : ∀ ⦃ _ : Monoid.Commutative b ⦄ ⦃ _ : IsLawfulMonoid b ⦄ (g : Bag a → b)
    >   → @0 Monoid.IsHomomorphism g
    >   → ∀ (xs : Bag a) → foldBag (g ∘ singleton) xs ≡ g xs
-}
{- $prop-morphism-foldBag
#p:prop-morphism-foldBag#

[prop-morphism-foldBag]:
    Universal property: 'foldBag' is a homomorphism
    (see "Data.Monoid.Morphism#g:1") of 'Monoid'.
    
    > prop-morphism-foldBag
    >   : ∀ ⦃ _ : Monoid.Commutative b ⦄ (f : a → b)
    >   → Monoid.IsHomomorphism (foldBag f)
-}
