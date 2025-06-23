{-# OPTIONS_GHC -Wno-unused-top-binds #-}

module Data.Bag.Prop.Conversion 
    (
    -- * Conversion
    -- $prop-morphism-mtoCounts
    
    -- $prop-morphism-mfromCounts
    
    -- $prop-mfromCounts-mtoCounts
    
    )
    where

import Prelude hiding (null, filter, lookup, map, concatMap, replicate)

dummyPropConversion :: ()
dummyPropConversion = ()

-- * Properties
{- $prop-Bag-fold-<>
#p:prop-Bag-fold-<>#

[prop-Bag-fold-<>]:
    @'foldMap' 'id'@ commutes with 'Bag'.
    
    > prop-Bag-fold-<>
    >   : ∀ {k} ⦃ _ : Ord k ⦄ (xs ys : Map k (Bag a))
    >   → foldMap id (Map.unionWith (_<>_) xs ys)
    >     ≡ foldMap id xs <> foldMap id ys
-}
{- $prop-Bag-fold-mempty
#p:prop-Bag-fold-mempty#

[prop-Bag-fold-mempty]:
    @'foldMap' 'id'@ on an empty 'Map' gives the empty 'Bag'.
    
    > prop-Bag-fold-mempty
    >   : ∀ {k} ⦃ _ : Ord k ⦄
    >   → foldMap id (Map.empty {k}) ≡ mempty {Bag a}
-}
{- $prop-mfromCounts-mtoCounts
#p:prop-mfromCounts-mtoCounts#

[prop-mfromCounts-mtoCounts]:
    'mfromCounts' is a left-inverse of 'mtoCounts'.
    
    > prop-mfromCounts-mtoCounts
    >   : ∀ ⦃ _ : Ord a ⦄ ⦃ _ : IsLawfulEq a ⦄ (xs : Bag a)
    >   → mfromCounts (mtoCounts xs) ≡ xs
-}
{- $prop-morphism-mfromCounts
#p:prop-morphism-mfromCounts#

[prop-morphism-mfromCounts]:
    'Data.Bag.Counts.mfromCounts' is a monoid homomorphism.
    
    > prop-morphism-mfromCounts
    >   : ⦃ _ : Ord a ⦄ → Monoid.IsHomomorphism (mfromCounts {a})
-}
{- $prop-morphism-mtoCounts
#p:prop-morphism-mtoCounts#

[prop-morphism-mtoCounts]:
    'Data.Bag.Counts.mtoCounts' is a monoid homomorphism.
    
    > prop-morphism-mtoCounts
    >   : ⦃ _ : Ord a ⦄ → Monoid.IsHomomorphism (mtoCounts {a})
-}
