module Data.Bag.Raw where

import Prelude hiding (null, filter, lookup, map, concatMap, replicate)

data Bag a = Single a
           | Empty
           | Union (Bag a) (Bag a)

singleton :: a -> Bag a
singleton = Single

empty :: Bag a
empty = Empty

union :: Bag a -> Bag a -> Bag a
union Empty ys = ys
union xs Empty = xs
union xs ys = Union xs ys

foldBag :: Monoid b => (a -> b) -> Bag a -> b
foldBag _ Empty = mempty
foldBag f (Single x) = f x
foldBag f (Union xs ys) = foldBag f xs <> foldBag f ys

-- * Properties
{- $prop-foldBag-unique
#p:prop-foldBag-unique#

[prop-foldBag-unique]:
    Any homomorphism to a monoid (not necessarily commutative)
    that respects the equivalence relation is equal to 'foldBag'.
    
    > prop-foldBag-unique
    >   : ∀ ⦃ _ : Monoid b ⦄ ⦃ _ : IsLawfulMonoid b ⦄ (g : Bag a → b)
    >   → (∀ {x x'} → x ~ x' → g x ≡ g x')
    >   → (g empty ≡ mempty)
    >   → (∀ {xs ys} → g (union xs ys) ≡ g xs <> g ys)
    >   → ∀ (xs : Bag a) → foldBag (g ∘ singleton) xs ≡ g xs
-}
{- $prop-~-foldBag
#p:prop-~-foldBag#

[prop-~-foldBag]:
    'foldBag' preserves equivalences
    when mapping to a commutative monoid
    
    > prop-~-foldBag
    >   : ∀ ⦃ _ : Monoid b ⦄ ⦃ _ : IsLawfulMonoid b ⦄ {x x' : Bag a} (f : a → b)
    >   → (∀ (r s : b) → r <> s ≡ s <> r)
    >   → x ~ x'
    >   → foldBag f x ≡ foldBag f x'
-}
{- $prop-~-union-1
#p:prop-~-union-1#

[prop-~-union-1]:
    'union' preserves equivalences in its second argument.
    
    > prop-~-union-1
    >   : ∀ (x x' y : Bag a)
    >   → x ~ x' → union x y ~ union x' y
-}
{- $prop-~-union-2
#p:prop-~-union-2#

[prop-~-union-2]:
    'union' preserves equivalences in its second argument.
    
    > prop-~-union-2
    >   : ∀ (x y y' : Bag a)
    >   → y ~ y' → union x y ~ union x y'
-}
