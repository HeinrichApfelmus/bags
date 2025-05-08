
-- | Proving monad laws
module Control.Monad.Prop where

open import Haskell.Prelude

open import Haskell.Prim.Monad
open import Haskell.Prim.Applicative

open import Haskell.Law.Applicative
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

-- | Monad laws → Applicative laws
prop-IsLawfulMonad→IsLawfulApplicative
  : ∀ ⦃ _ : Monad m ⦄
  → MinimalIsLawfulMonad m
  → Monad→Functor m
  → Monad→Applicative m
  → IsLawfulApplicative m
--
prop-IsLawfulMonad→IsLawfulApplicative {m} laws-m laws-f laws-a = record
    { super = prop-IsLawfulMonad→IsLawfulFunctor laws-m laws-f
    ; identity = midentity
    ; composition = mcomposition
    ; homomorphism = mhomomorphism
    ; interchange = minterchange
    ; functor = mfunctor
    }
  where
    open Monad→Applicative laws-a
    open Monad→Functor laws-f
    massociativity = MinimalIsLawfulMonad.associativity laws-m
    mleftIdentity  = MinimalIsLawfulMonad.leftIdentity laws-m

    midentity : ∀ {a} (ma : m a) → (pure id <*> ma) ≡ ma
    midentity {a} ma
      rewrite pure-return (id {a})
      | <*>->>= (return id) ma
      = begin
        return id >>= (λ f → ma >>= (λ x → return (f x)))
      ≡⟨ MinimalIsLawfulMonad.leftIdentity laws-m _ _ ⟩
        ma >>= (λ x → return (id x))
      ≡⟨ MinimalIsLawfulMonad.rightIdentity laws-m _ ⟩
        ma
      ∎

    mfunctor : ∀ {a b} (f : a → b) (u : m a) → fmap f u ≡ (pure f <*> u)
    mfunctor f u = begin
        fmap f u
      ≡⟨ fmap->>= _ _ ⟩
        (do x ← u; return (f x))
      ≡⟨ sym (mleftIdentity _ _) ⟩
        (do f' ← return f; x ← u; return (f' x))
      ≡⟨ cong (λ o → o >>= _) (sym (pure-return _)) ⟩
        (do f' ← pure f; x ← u; return (f' x))
      ≡⟨ sym (<*>->>= _ _) ⟩
        pure f <*> u
      ∎

    mcomposition
      : ∀ {a b c} (u : m (b → c)) (v : m (a → b)) (w : m a)
      → (pure _∘_ <*> u <*> v <*> w) ≡ (u <*> (v <*> w))
    mcomposition u v w
      = begin
        pure _∘_ <*> u <*> v <*> w
      ≡⟨ cong (λ o → o <*> u <*> v <*> w) (pure-return _∘_) ⟩
        return _∘_ <*> u <*> v <*> w
      ≡⟨ cong (λ o → o <*> v <*> w) (<*>->>= _ _ ) ⟩
        (do comp ← return _∘_; g ← u; return (comp g)) <*> v <*> w
      ≡⟨ cong (λ o → o <*> v <*> w) (mleftIdentity _ _) ⟩
        (do g ← u; return (_∘_ g)) <*> v <*> w
      ≡⟨ cong (λ o → o <*> w) (<*>->>= _ _ ) ⟩
        (do g' ← (do g ← u; return (_∘_ g)); f ← v; return (g' f)) <*> w
      ≡⟨ cong (λ o → o <*> w) (sym (massociativity u _ _)) ⟩
        (do g ← u; g' ← return (_∘_ g); f ← v; return (g' f)) <*> w
      ≡⟨ cong (λ o → o <*> w) (cong-monad u (λ g → mleftIdentity _ _)) ⟩
        (do g ← u; f ← v; return (g ∘ f)) <*> w
      ≡⟨ <*>->>= _ _ ⟩
        (do gf ← (do g ← u; f ← v; return (g ∘ f)); x ← w; return (gf x))
      ≡⟨ sym (massociativity u _ _) ⟩
        (do g ← u; gf ← (do f ← v; return (g ∘ f)); x ← w; return (gf x))
      ≡⟨ cong-monad u (λ g → sym (massociativity v _ _)) ⟩
        (do g ← u; do f ← v; gf ← return (g ∘ f); x ← w; return (gf x))
      ≡⟨ cong-monad u (λ g → cong-monad v (λ f → mleftIdentity _ _)) ⟩
        (do g ← u; f ← v; x ← w; return (g (f x)))
      ≡⟨ cong-monad u (λ g → cong-monad v λ f → cong-monad w (λ x → sym (mleftIdentity _ _))) ⟩
        (do g ← u; f ← v; x ← w; y ← return (f x); return (g y))
      ≡⟨ cong-monad u (λ g → cong-monad v λ x → massociativity _ _ _) ⟩
        (do g ← u; f ← v; y ← (do x ← w; return (f x)); return (g y))
      ≡⟨ cong-monad u (λ g → massociativity _ _ _) ⟩
        (do g ← u; y ← (do f ← v; x ← w; return (f x)); return (g y))
      ≡⟨ sym (<*>->>= _ _) ⟩
        u <*> (do f ← v; x ← w; return (f x))
      ≡⟨ cong (λ o → u <*> o) (sym (<*>->>= _ _)) ⟩
        u <*> (v <*> w)
      ∎

    mhomomorphism
      : ∀ {a b} (f : a → b) (x : a)
      → (pure {m} f <*> pure x) ≡ pure (f x)
    mhomomorphism f x = begin
        pure {m} f <*> pure x
      ≡⟨ cong₂ (_<*>_) (pure-return f) (pure-return x) ⟩
        return {m} f <*> return x
      ≡⟨ <*>->>= _ _ ⟩
        (do f' ← return f; x' ← return x; return (f' x'))
      ≡⟨ mleftIdentity _ _ ⟩
        (do x' ← return x; return (f x'))
      ≡⟨ mleftIdentity _ _ ⟩
        return (f x)
      ≡⟨ sym (pure-return _) ⟩
        pure (f x)
      ∎

    minterchange
      : ∀ {a b} (u : m (a → b)) (y : a)
      → (u <*> pure y) ≡ (pure (_$ y) <*> u)
    minterchange u y = begin
        u <*> pure y
      ≡⟨ cong (u <*>_) (pure-return _) ⟩
        u <*> return y
      ≡⟨ <*>->>= _ _ ⟩
        (do f ← u; y' ← return y; return (f y'))
      ≡⟨ cong-monad u (λ f → mleftIdentity y _) ⟩
        (do f ← u; return (f y))
      ≡⟨ sym (mleftIdentity _ _) ⟩
        (do y'' ← return (_$ y); f ← u; return (y'' f))
      ≡⟨ sym (<*>->>= _ _) ⟩
        return (_$ y) <*> u
      ≡⟨ sym (cong (_<*> u) (pure-return _)) ⟩
        pure (_$ y) <*> u
      ∎


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
