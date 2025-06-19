module Data.Bag.Found where

import Prelude hiding (null, filter, lookup, map, concatMap, replicate)
import Data.Bag.Quotient (Bag, foldBag, singleton)
import qualified Data.Monoid.Refinement (Commutative)

{-|
Find a known item in a 'Bag',
and also return a 'Bag' without that item.

The item is part of the type, but erased.
-}
data Found a = MkFound{found :: Maybe a, rest :: Bag a}

emptyFound :: Found a
emptyFound = MkFound Nothing mempty

unionFound :: Found a -> Found a -> Found a
unionFound (MkFound Nothing r1) (MkFound Nothing r2)
  = MkFound Nothing (r1 <> r2)
unionFound (MkFound Nothing r1) (MkFound (Just y2) r2)
  = MkFound (Just y2) (r1 <> r2)
unionFound (MkFound (Just y1) r1) (MkFound Nothing r2)
  = MkFound (Just y1) (r1 <> r2)
unionFound (MkFound (Just y1) r1) (MkFound (Just y2) r2)
  = MkFound (Just y1) (r1 <> singleton y2 <> r2)

instance Semigroup (Found a) where
    (<>) = unionFound

instance Monoid (Found a) where
    mempty = emptyFound

{-|
We have found the item.
-}
here :: a -> Found a
here x = MkFound (Just x) mempty

{-|
We have an item, but the item that we are looking for is elsewhere.
-}
elsewhere :: a -> Found a
elsewhere y = MkFound Nothing (singleton y)

{-|
Put the item back into the 'Bag'.
-}
putBack :: Found a -> Bag a
putBack (MkFound Nothing xs) = xs
putBack (MkFound (Just x) xs) = singleton x <> xs

instance (Eq a) => Data.Monoid.Refinement.Commutative (Found a)
         where

{-|
'deleteOne' on a 'singleton' 'Bag'.
-}
findOne :: Eq a => a -> a -> Found a
findOne x y = if x == y then here y else elsewhere y

{-|
Delete a given item from the given 'Bag' once.
-}
deleteOne :: Eq a => a -> Bag a -> Bag a
deleteOne x = (\ r -> rest r) . foldBag (findOne x)

-- * Properties
{- $prop-Found-<>-sym
#p:prop-Found-<>-sym#

[prop-Found-<>-sym]:
    The monoid 'Found' is commutative.
    
    We rely on the crucial fact that the found item is always the same.
    
    > @0 prop-Found-<>-sym
    >   : ∀ {@0 z : a} ⦃ _ : Eq a ⦄ ⦃ @0 _ : IsLawfulEq a ⦄
    >   → (x y : Found a z) → x <> y ≡ y <> x
-}
{- $prop-morphism-foundIt
#p:prop-morphism-foundIt#

[prop-morphism-foundIt]:
    'foundIt' is a monoid homomorphism.
    
    > prop-morphism-foundIt
    >   : ∀ {@0 z : a} → Monoid.IsHomomorphism (foundIt {z = z})
-}
{- $prop-morphism-putBack
#p:prop-morphism-putBack#

[prop-morphism-putBack]:
    'putBack' is a homomorphism of 'Monoid'.
    
    > prop-morphism-putBack
    >   : ∀ {@0 z : a} → Monoid.IsHomomorphism (putBack {z = z})
-}
{- $prop-putBack-findOne
#p:prop-putBack-findOne#

[prop-putBack-findOne]:
    Finding an item and putting it back is equivalent to no change.
    
    > prop-putBack-findOne
    >   : ∀ ⦃ _ : Eq a ⦄ ⦃ _ : IsLawfulEq a ⦄ (x : a) (xs : Bag a)
    >   → putBack (foldBag (findOne x) xs) ≡ xs
-}
