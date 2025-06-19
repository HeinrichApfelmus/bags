module Haskell.Data.List.Extra where

open import Haskell.Prim

replicateNat : Nat → a → List a
replicateNat zero    _ = []
replicateNat (suc n) x = x ∷ replicateNat n x
