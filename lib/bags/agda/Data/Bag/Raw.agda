-- | Type and operations, before taking the quotient.
module Data.Bag.Raw where

open import Haskell.Prelude

{-----------------------------------------------------------------------------
    Type
------------------------------------------------------------------------------}
data Bag a : Type where
  Single : a → Bag a
  Empty  : Bag a
  Union  : Bag a → Bag a → Bag a

singleton : a → Bag a
singleton = Single

empty : Bag a
empty = Empty

union : Bag a → Bag a → Bag a
union Empty ys = ys
union xs Empty = xs
union xs ys    = Union xs ys

foldBag : ⦃ _ : Monoid b ⦄ → (a → b) → Bag a → b
foldBag _ Empty         = mempty
foldBag f (Single x)    = f x
foldBag f (Union xs ys) = foldBag f xs <> foldBag f ys

{-# COMPILE AGDA2HS Bag #-}
{-# COMPILE AGDA2HS singleton #-}
{-# COMPILE AGDA2HS empty #-}
{-# COMPILE AGDA2HS union #-}
{-# COMPILE AGDA2HS foldBag #-}
