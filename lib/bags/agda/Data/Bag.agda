module Data.Bag
  {-|
  -- * Type
  ; Bag
  ; singleton
  ; foldBag

  -- * Operations
  -- ** Query
  ; null
  ; mnull
  ; size
  ; msize
  ; count
  ; member
  ; mmember

  -- ** Construction
  ; fromMaybe
  ; fromList

  -- ** Deletion
  ; deleteOne
    ; prop-deleteOne-member-True
    ; prop-deleteOne-member-False

  -- ** Combine
  ; union
  ; cartesianProduct
  ; equijoin

  -- ** Traversal
  ; map
  ; concatMap
  ; filter

  -- * Properties
  ; module Data.Bag.Prop
  -} where

{-# FOREIGN AGDA2HS
  {-# OPTIONS_GHC -Wno-unused-imports -Wno-dodgy-exports #-}
  import Data.Bag.Def
  import Data.Bag.Quotient
  import Data.Bag.Found (deleteOne)
  import Data.Bag.Prop
#-}

open import Data.Bag.Def            public
open import Data.Bag.Quotient.Prop  public
open import Data.Bag.Prop           public
open import Data.Bag.Found          public using (deleteOne)

open import Haskell.Prelude
open import Haskell.Law.Eq

{-----------------------------------------------------------------------------
    Copy & Paste of relevant properties
    for documentation purposes.
------------------------------------------------------------------------------}
-- | If the given item is a 'member' of the 'Bag',
-- 'deleteOne' will remove it once.
@0 prop-deleteOne-member-True
  : ∀ ⦃ _ : Eq a ⦄ ⦃ @0 _ : IsLawfulEq a ⦄ (x : a) (xs : Bag a)
  → member x xs ≡ True
  → xs ≡ singleton x <> deleteOne x xs
--
prop-deleteOne-member-True =
    Data.Bag.Found.prop-deleteOne-member-True

-- | If the given item is a 'member' of the 'Bag',
-- 'deleteOne' will leave the 'Bag' unchanged.
prop-deleteOne-member-False
  : ∀ ⦃ _ : Eq a ⦄ ⦃ _ : IsLawfulEq a ⦄ (x : a) (xs : Bag a)
  → member x xs ≡ False
  → xs ≡ deleteOne x xs
--
prop-deleteOne-member-False =
    Data.Bag.Found.prop-deleteOne-member-False
