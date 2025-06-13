-- | Proofs on 'Bag'.
module Data.Bag.Prop.Deletion
  {-|
  -- * Deletion
  -- ** deleteOne
  ; prop-deleteOne-member-True
  ; prop-deleteOne-member-False
  -} where

open import Data.Bag.Def            public
open import Data.Bag.Quotient.Prop  public
open import Data.Bag.Found          public using (deleteOne)

open import Haskell.Prelude
open import Haskell.Law.Eq

{-# FOREIGN AGDA2HS
{-# OPTIONS_GHC -Wno-unused-top-binds #-}
#-}
dummy : ⊤
dummy = tt
{-# COMPILE AGDA2HS dummy #-}

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
