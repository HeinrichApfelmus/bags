
-- | Operations on 'Bag' defined in terms of the axiomatization.
module Data.Bag.Def where

open import Haskell.Prelude hiding (null; filter; map; concatMap)

open import Haskell.Prim
open import Haskell.Prim.Alternative
open import Haskell.Prim.Applicative
open import Haskell.Prim.Eq
open import Haskell.Prim.Foldable using (foldMap)
open import Haskell.Prim.Functor
open import Haskell.Prim.Int
open import Haskell.Prim.Maybe
open import Haskell.Prim.Monad
open import Haskell.Prim.MonadPlus
open import Haskell.Prim.Monoid
open import Haskell.Prim.Num
open import Haskell.Prim.Ord
open import Haskell.Prim.Tuple

open import Haskell.Law.Function
open import Haskell.Law.Num

open import Haskell.Data.Bag.Quotient
open import Data.Monoid.Extra
import      Data.Monoid.Refinement as Monoid

{-# FOREIGN AGDA2HS
{-# OPTIONS_GHC -Wno-orphans #-}

import Control.Monad (guard, MonadPlus)
import Control.Applicative (Alternative (..))

#-}

{-----------------------------------------------------------------------------
    Operations
    basic
------------------------------------------------------------------------------}
-- | Test whether the 'Bag' is empty, 'Monoid' version.
mnull : Bag a → Conj
mnull = foldBag (λ _ → MkConj False)

{-# COMPILE AGDA2HS mnull #-}

-- | Is the given 'Bag' empty?
null : Bag a → Bool
null = getConj ∘ mnull

{-# COMPILE AGDA2HS null #-}

-- | Union of all items from the two argument 'Bag's.
-- Synonym for '(<>)'.
union : Bag a → Bag a → Bag a
union = _<>_

{-# COMPILE AGDA2HS union #-}

-- | Construct a 'Bag' that may be empty or contains a single item.
fromMaybe : Maybe a → Bag a
fromMaybe Nothing  = mempty
fromMaybe (Just x) = singleton x

{-# COMPILE AGDA2HS fromMaybe #-}

-- | The number of items in the Bag, Monoid version
msize : Bag a → Sum' Int
msize = foldBag (λ _ → MkSum 1)

{-# COMPILE AGDA2HS msize #-}

-- | The number of items in the Bag.
size : Bag a → Int
size = getSum' ∘ msize

{-# COMPILE AGDA2HS size #-}

-- | Apply a function to all items in the 'Bag'
-- and take the 'union' of the results.
concatMap : (a → Bag b) → Bag a → Bag b
concatMap = foldBag

{-# COMPILE AGDA2HS concatMap #-}

-- | Apply a function to all items in the 'Bag'.
map : (a → b) → Bag a → Bag b
map f = concatMap (singleton ∘ f)

{-# COMPILE AGDA2HS map #-}

-- | Construct a 'Bag' with the same items as the given list.
fromList : List a → Bag a
fromList = foldMap singleton

{-# COMPILE AGDA2HS fromList #-}

{-----------------------------------------------------------------------------
    Operations
    functorial type classes
------------------------------------------------------------------------------}
instance
  iDefaultFunctorBag : DefaultFunctor Bag
  iDefaultFunctorBag .DefaultFunctor.fmap = map

  iFunctorBag : Functor Bag
  iFunctorBag = record{DefaultFunctor iDefaultFunctorBag}

  iDefaultApplicativeBag : DefaultApplicative Bag
  iDefaultApplicativeBag .DefaultApplicative.pure = singleton
  iDefaultApplicativeBag .DefaultApplicative._<*>_ fs xs =
    concatMap (λ f → map f xs) fs

  iApplicativeBag : Applicative Bag
  iApplicativeBag = record{DefaultApplicative iDefaultApplicativeBag}

  iDefaultMonadBag : DefaultMonad Bag
  iDefaultMonadBag .DefaultMonad._>>=_ = flip concatMap

  iMonadBag : Monad Bag
  iMonadBag = record{DefaultMonad iDefaultMonadBag}

  iAlternativeBag : Alternative Bag
  iAlternativeBag .Alternative.empty = mempty
  iAlternativeBag .Alternative._<|>_ = _<>_

  iMonadPlusBag : MonadPlus Bag
  iMonadPlusBag = record { unique-applicative = refl }

{-# COMPILE AGDA2HS iFunctorBag #-}
{-# FOREIGN AGDA2HS
-- Workaround instance for issue in Agda2hs.
-- Issue: Definitions of `pure` and `<*>` are duplicated for some reason.
instance Applicative Bag where
  pure = singleton
  fs <*> xs = concatMap (\ f -> map f xs) fs
#-}

{-# COMPILE AGDA2HS iMonadBag #-}
{-# COMPILE AGDA2HS iAlternativeBag #-}

{-# FOREIGN AGDA2HS
-- Workaround instance for issue in Agda2hs
instance MonadPlus Bag
#-}

{------------------------------------------------------------------------------
    Operations
    Definitions using do-notation
------------------------------------------------------------------------------}
-- | Keep those elements that satisfy a predicate.
filter : (a → Bool) → Bag a → Bag a
filter p xs = do x ← xs; guard (p x); pure x

{-# COMPILE AGDA2HS filter #-}

-- | Count the number of times that an item is contained in the 'Bag'.
count : ⦃ Eq a ⦄ → a → Bag a → Int
count x = size ∘ filter (x ==_)

{-# COMPILE AGDA2HS count #-}

-- | Test whether an item is contained in the 'Bag' at least once,
-- 'Monoid' version.
mmember : ⦃ Eq a ⦄ → a → Bag a → Disj
mmember x = foldBag (λ y → if x == y then MkDisj True else mempty)

{-# COMPILE AGDA2HS mmember #-}

-- | Is the given item contain in the 'Bag' at least once?
member : ⦃ Eq a ⦄ → a → Bag a → Bool
member x = getDisj ∘ mmember x

{-# COMPILE AGDA2HS member #-}

-- | Construct the 'Bag' containing all possible pairs of items.
cartesianProduct : Bag a → Bag b → Bag (a × b)
cartesianProduct xs ys = do x ← xs; y ← ys; pure (x , y)

{-# COMPILE AGDA2HS cartesianProduct #-}

-- | Construct the 'Bag' containing all possible pairs of items where
-- the functions yield the same result.
equijoin
    : ∀ {k} ⦃ _ : Eq k ⦄
    → (a → k) → (b → k) → Bag a → Bag b → Bag (a × b)
equijoin f g xs ys = do x ← xs; y ← ys; guard (f x == g y); pure (x , y)

{-# COMPILE AGDA2HS equijoin #-}
