module Haskell.Law.Extensionality.Extra where

open import Haskell.Prim
open import Haskell.Law.Extensionality using (ext)

-- | Convenience:
-- Function extensionality for functions with two arguments
ext₂
  : ∀ {f g : a → b → c}
  → (∀ (x : a) (y : b) → f x y ≡ g x y) → f ≡ g
ext₂ eq = ext (λ x → ext (eq x))
