
-- | Proving monad laws
module Control.Monad.Prop where

open import Haskell.Prelude

open import Haskell.Prim.Monad
open import Haskell.Prim.Applicative

open import Haskell.Law.Monad
open import Haskell.Law.Equality
open import Haskell.Law.Extensionality
open import Haskell.Law.Functor

-- | Substitution in the second argument of '(>>=)'.
cong-monad
  : ∀ ⦃ _ : Monad m ⦄ (mx : m a) {f g : a → m b}
  → (∀ x → f x ≡ g x)
  → (do x ← mx; f x) ≡ (do x ← mx; g x)
cong-monad mx {f} {g} eq = cong (mx >>=_) (ext eq)

{-----------------------------------------------------------------------------
    Monad laws
------------------------------------------------------------------------------}

record MinimalIsLawfulMonad (m : Type → Type) ⦃ _ : Monad m ⦄ : Type₁ where
  field
    leftIdentity  : ∀ {a} (x : a) (k : a → m b) → (return x >>= k) ≡ k x
    rightIdentity : ∀ {a} (ma : m a) → (ma >>= return) ≡ ma
    associativity : ∀ {a b c} (ma : m a) (f : a → m b) (g : b → m c)
      → (ma >>= (λ x → f x >>= g)) ≡ ((ma >>= f) >>= g)

{-----------------------------------------------------------------------------
    Monad → Functor
------------------------------------------------------------------------------}

-- | Given a 'Monad', construct the 'Functor' instance.
record Monad→Functor (m : Type → Type) ⦃ _ : Monad m ⦄ : Type₁ where
  field
    fmap->>= : ∀ {a b} (f : a → b) (ma : m a)
      → fmap f ma ≡ (ma >>= (return ∘ f))

-- | Monad laws → Functor laws
prop-IsLawfulMonad→IsLawfulFunctor
  : ∀ ⦃ _ : Monad m ⦄
  → MinimalIsLawfulMonad m
  → Monad→Functor m
  → IsLawfulFunctor m
--
prop-IsLawfulMonad→IsLawfulFunctor laws-m laws-f .identity fa
  rewrite Monad→Functor.fmap->>= laws-f id fa
  = MinimalIsLawfulMonad.rightIdentity laws-m fa
prop-IsLawfulMonad→IsLawfulFunctor laws-m laws-f .composition fa f g
  rewrite Monad→Functor.fmap->>= laws-f g (fmap f fa)
  | Monad→Functor.fmap->>= laws-f f fa
  | Monad→Functor.fmap->>= laws-f (g ∘ f) fa
  = begin
    fa >>= (return ∘ g ∘ f)
  ≡⟨ cong-monad fa (λ x → sym (MinimalIsLawfulMonad.leftIdentity laws-m (f x) _)) ⟩
    fa >>= (λ x → return (f x) >>= (return ∘ g))
  ≡⟨ MinimalIsLawfulMonad.associativity laws-m _ _ _ ⟩
    (fa >>= (return ∘ f)) >>= (return ∘ g)
  ∎

{-----------------------------------------------------------------------------
    Monad → Applicative
------------------------------------------------------------------------------}

-- | Given a 'Monad', construct the 'Applicative' instance.
record Monad→Applicative (m : Type → Type) ⦃ iMonad : Monad m ⦄ : Type₁ where
  field
    pure-return : ∀ (x : a) → pure ⦃ iMonad .super ⦄ x ≡ return x

    <*>->>= : ∀ {a b} → (mf : m (a → b)) (ma : m a)
      → (mf <*> ma) ≡ (mf >>= (λ f → (ma >>= (λ x → return (f x)))))

-- | Prove that the default definitions imply that
-- '(*>)' equals '(>>)'.
prop-*>->>
  : ∀ ⦃ _ : Monad m ⦄
  → MinimalIsLawfulMonad m
  → Monad→Applicative m
  → Monad→Functor m
  → (∀ (ma : m a) (mb : m b) → (ma >> mb) ≡ (ma >>= λ x → mb) )
  → (∀ (ma : m a) (mb : m b) → (ma *> mb) ≡ (const id <$> ma <*> mb) )
  →  ∀ (ma : m a) (mb : m b) → (ma *> mb) ≡ (ma >> mb)
--
prop-*>->> laws-m laws-a laws-f eq->> eq-*> ma mb
  rewrite eq-*> ma mb
  | (Monad→Applicative.<*>->>= laws-a (const id <$> ma) mb)
  | eq->> ma mb
  = begin
    fmap (const id) ma >>= (λ f → mb >>= λ x → return (f x))
  ≡⟨ cong (_>>= _) (Monad→Functor.fmap->>= laws-f _ _) ⟩
    (ma >>= (return ∘ const id)) >>= (λ f → mb >>= λ x → return (f x))
  ≡⟨ sym (MinimalIsLawfulMonad.associativity laws-m ma _ _) ⟩
    ma >>= (λ x → return (const id x) >>= (λ g → mb >>= λ x → return (g x)))
  ≡⟨ cong (ma >>=_) (ext λ x → MinimalIsLawfulMonad.leftIdentity laws-m _ _) ⟩
    ma >>= (λ x → (mb >>= λ y → return (const id x y)))
  ≡⟨ cong (ma >>=_) (ext λ x → MinimalIsLawfulMonad.rightIdentity laws-m _) ⟩
    ma >>= (λ x → mb)
  ∎
