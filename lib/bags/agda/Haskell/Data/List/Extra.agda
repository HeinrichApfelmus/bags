module Haskell.Data.List.Extra where

open import Haskell.Prim
open import Haskell.Prim.List
open import Haskell.Prim.Num

{-----------------------------------------------------------------------------
    Operations
------------------------------------------------------------------------------}

replicateNat : Nat → a → List a
replicateNat zero    _ = []
replicateNat (suc n) x = x ∷ replicateNat n x

{-----------------------------------------------------------------------------
    Properties
------------------------------------------------------------------------------}
-- | 'replicateNat' maps '(+)' to '(++)'.
prop-replicateNat-+
  : ∀ (m n : Nat) (x : a)
  → replicateNat (m + n) x ≡ replicateNat m x ++ replicateNat n x
--
prop-replicateNat-+ zero    n x = refl
prop-replicateNat-+ (suc m) n x
  rewrite prop-replicateNat-+ m n x = refl
