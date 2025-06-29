{-# OPTIONS --erasure #-}

-- | Monoids with additional properties.
module Data.Monoid.Refinement
  {-|
  ; Commutative
  ; prop-<>-sym
  -} where

open import Haskell.Prim
open import Haskell.Prim.Monoid
open import Haskell.Prim.Num
open import Haskell.Prim.Ord
open import Haskell.Prim.Tuple

open import Haskell.Law
open import Haskell.Law.Extensionality
open import Haskell.Law.Num

open import Data.Set using (Set; iSetMonoid)
open import Data.Monoid.Extra

-------------------------------------------------------------------------------
-- Commutative monoids

-- | Commutative monoids.
record Commutative (a : Type) : Type where
  field
    overlap ⦃ monoid ⦄ : Monoid a

    @0 commutative : ∀ (x y : a) → x <> y ≡ y <> x

open Commutative ⦃...⦄ public

{-# COMPILE AGDA2HS Commutative class #-}

-- | For a 'Commutative' monoid,
-- interchanging the two arguments of the monoid operation '(<>)'
-- does not change the result.
@0 prop-<>-sym
  : ∀ ⦃ _ : Commutative a ⦄ (x y : a)
  → x <> y ≡ y <> x 
--
prop-<>-sym = commutative

-------------------------------------------------------------------------------
-- Instances

instance
  iCommutativeFun : ⦃ Commutative b ⦄ → Commutative (a → b)
  iCommutativeFun .monoid = iMonoidFun
  iCommutativeFun .commutative f g = ext (λ x → commutative (f x) (g x))

  iCommutativeUnit : Commutative ⊤
  iCommutativeUnit .monoid = iMonoidUnit
  iCommutativeUnit .commutative x y = refl

  iCommutativeTuple₂
    : ⦃ Commutative a ⦄ → ⦃ Commutative b ⦄ → Commutative (a × b)
  iCommutativeTuple₂ .monoid = iMonoidTuple₂
  iCommutativeTuple₂ .commutative (x1 , x2) (y1 , y2)
    rewrite commutative x1 y1
    rewrite commutative x2 y2
    = refl

  iCommutativeTuple₃
    : ⦃ Commutative a ⦄ → ⦃ Commutative b ⦄ → ⦃ Commutative c ⦄
    → Commutative (a × b × c)
  iCommutativeTuple₃ .monoid = iMonoidTuple₃
  iCommutativeTuple₃ .commutative (x1 , x2 , x3) (y1 , y2 , y3)
    rewrite commutative x1 y1
    rewrite commutative x2 y2
    rewrite commutative x3 y3
    = refl

  iCommutativeConj : Commutative Conj
  iCommutativeConj .monoid = iMonoidConj
  iCommutativeConj .commutative record{getConj = x} record{getConj = y}
    = cong (λ o → record{getConj = o}) (prop-&&-sym x y)

  iCommutativeDisj : Commutative Disj
  iCommutativeDisj .monoid = iMonoidDisj
  iCommutativeDisj .commutative record{getDisj = x} record{getDisj = y}
    = cong (λ o → record{getDisj = o}) (prop-||-sym x y)

  iCommutativeSum' : ⦃ _ : Num a ⦄ → @0 ⦃ IsLawfulNum a ⦄ → Commutative (Sum' a)
  iCommutativeSum' .monoid = iMonoidSum'
  iCommutativeSum' .commutative record{getSum' = x} record{getSum' = y}
    = cong (λ o → record { getSum' = o }) (+-comm x y)

  iCommutativeSet : ⦃ _ : Ord a ⦄ → @0 ⦃ IsLawfulEq a ⦄ → Commutative (Set a) 
  iCommutativeSet .monoid = iSetMonoid
  iCommutativeSet {a} .commutative x y = Data.Set.prop-union-sym {a} {x} {y}

{-# COMPILE AGDA2HS iCommutativeUnit #-}
{-# COMPILE AGDA2HS iCommutativeTuple₂ #-}
{-# COMPILE AGDA2HS iCommutativeTuple₃ #-}
{-# COMPILE AGDA2HS iCommutativeConj #-}
{-# COMPILE AGDA2HS iCommutativeDisj #-}
{-# COMPILE AGDA2HS iCommutativeSum' #-}
{-# COMPILE AGDA2HS iCommutativeSet #-}

{- *-comm is not part of IsLawfulNum yet?!

CommutativeProduct : ⦃ _ : Num a ⦄ → ⦃ _ : IsLawfulNum a ⦄ → Commutative a
CommutativeProduct .monoid = MonoidProduct
CommutativeProduct .commutative = *-comm
-}
