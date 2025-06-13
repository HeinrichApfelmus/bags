module Data.Bag
  {-|
  -- * Type and Definitional Properties
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
  ; module Data.Bag.Prop.Deletion
  -} where

{-# FOREIGN AGDA2HS
  {-# OPTIONS_GHC -Wno-unused-imports -Wno-dodgy-exports #-}
  import Data.Bag.Def
  import Data.Bag.Quotient
  import Data.Bag.Found (deleteOne)
  import Data.Bag.Prop
  import Data.Bag.Prop.Deletion
#-}

open import Data.Bag.Def            public
open import Data.Bag.Quotient.Prop  public
open import Data.Bag.Prop           public
open import Data.Bag.Found          public using (deleteOne)

open import Haskell.Prelude
open import Haskell.Law.Eq
