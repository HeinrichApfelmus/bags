-- | Type and operations, before taking the quotient.
module Data.Bag.Raw where

open import Haskell.Prelude

open import Haskell.Law.Monoid
open import Haskell.Law.Equality

{-----------------------------------------------------------------------------
    Type
------------------------------------------------------------------------------}
data Bag a : Type where
  Single : a → Bag a
  Empty  : Bag a
  Union  : Bag a → Bag a → Bag a

singleton : a → Bag a
singleton = Single

empty : Bag a
empty = Empty

union : Bag a → Bag a → Bag a
union Empty ys = ys
union xs Empty = xs
union xs ys    = Union xs ys

foldBag : ⦃ _ : Monoid b ⦄ → (a → b) → Bag a → b
foldBag _ Empty         = mempty
foldBag f (Single x)    = f x
foldBag f (Union xs ys) = foldBag f xs <> foldBag f ys

{-# COMPILE AGDA2HS Bag #-}
{-# COMPILE AGDA2HS singleton #-}
{-# COMPILE AGDA2HS empty #-}
{-# COMPILE AGDA2HS union #-}
{-# COMPILE AGDA2HS foldBag #-}

{-----------------------------------------------------------------------------
    Equational reasoning for equivalence relations
------------------------------------------------------------------------------}
module
  ~-Reasoning (a : Type) (_~_ : a → a → Type₁)
    (Eq-Refl  : ∀ {x : a} → x ~ x)
    (Eq-Trans : ∀ {x y z : a} → x ~ y → y ~ z → x ~ z)
    where

  infix  1 begin~_
  infixr 2 _~⟨⟩_ step-~
  infix  3 _~∎

  begin~_ : ∀{x y : a} → x ~ y → x ~ y
  begin~_ x~y = x~y

  _~⟨⟩_ : ∀ (x {y} : a) → x ~ y → x ~ y
  _ ~⟨⟩ x~y = x~y

  step-~ : ∀ (x {y z} : a) → y ~ z → x ~ y → x ~ z
  step-~ _ y~z x~y = Eq-Trans x~y y~z

  _~∎ : ∀ (x : a) → x ~ x
  _~∎ _ = Eq-Refl

  syntax step-~  x y~z x~y = x ~⟨ x~y ⟩ y~z

{-----------------------------------------------------------------------------
    Equivalence relation
------------------------------------------------------------------------------}
data _~_ : Bag a → Bag a → Type₁ where
  Eq-Empty-1 : ∀ (y : Bag a) → Union Empty y ~ y
  Eq-Empty-2 : ∀ (x : Bag a) → Union x Empty ~ x
  Eq-Assoc   : ∀ (x y  z  : Bag a) → Union (Union x y) z ~ Union x (Union y z)
  Eq-Cong-1  : ∀ (x x' y  : Bag a) → x ~ x' → Union x y ~ Union x' y
  Eq-Cong-2  : ∀ (x y  y' : Bag a) → y ~ y' → Union x y ~ Union x y'

  Eq-Union-Sym : ∀ (x y : Bag a) → Union x y ~ Union y x

  Eq-Refl  : ∀ {x : Bag a} → x ~ x
  Eq-Sym   : ∀ {x y : Bag a} → x ~ y → y ~ x
  Eq-Trans : ∀ {x y z : Bag a} → x ~ y → y ~ z → x ~ z

-- import syntax for ~-Reasoning
open module ~-Reasoning-Bag {a : Type} =
  ~-Reasoning (Bag a) (_~_) Eq-Refl Eq-Trans

-- The definition of 'union' is chosen such that the result
-- is equivalent to the application of the constructor 'Union'.
--
prop-union-constructor
  : ∀ (x y : Bag a)
  → union x y ~ Union x y
--
prop-union-constructor (Single x) (Single y)     = Eq-Refl
prop-union-constructor (Single x) Empty          = Eq-Sym (Eq-Empty-2 _)
prop-union-constructor (Single x) (Union y y₁)   = Eq-Refl
prop-union-constructor Empty      y              = Eq-Sym (Eq-Empty-1 _)
prop-union-constructor (Union x x₁) (Single x₂)  = Eq-Refl
prop-union-constructor (Union x x₁) Empty        = Eq-Sym (Eq-Empty-2 _)
prop-union-constructor (Union x x₁) (Union y y₁) = Eq-Refl

-- | 'union' preserves equivalences in its second argument.
prop-~-union-1
  : ∀ (x x' y : Bag a)
  → x ~ x' → union x y ~ union x' y
--
prop-~-union-1 x x' y rel = begin~
  union x  y  ~⟨ prop-union-constructor x y ⟩
  Union x  y  ~⟨ Eq-Cong-1 x x' y rel ⟩
  Union x' y  ~⟨ Eq-Sym (prop-union-constructor x' y) ⟩
  union x' y  ~∎

-- | 'union' preserves equivalences in its second argument.
prop-~-union-2
  : ∀ (x y y' : Bag a)
  → y ~ y' → union x y ~ union x y'
--
prop-~-union-2 x y y' rel = begin~
  union x y   ~⟨ prop-union-constructor x y ⟩
  Union x y   ~⟨ Eq-Cong-2 x y y' rel ⟩
  Union x y'  ~⟨ Eq-Sym (prop-union-constructor x y') ⟩
  union x y'  ~∎

-- | 'foldBag' preserves equivalences
-- when mapping to a commutative monoid
prop-~-foldBag
  : ∀ ⦃ _ : Monoid b ⦄ ⦃ _ : IsLawfulMonoid b ⦄ {x x' : Bag a} (f : a → b)
  → (∀ (r s : b) → r <> s ≡ s <> r)
  → x ~ x'
  → foldBag f x ≡ foldBag f x'
--
prop-~-foldBag f comm (Eq-Empty-1 _) = leftIdentity _
prop-~-foldBag f comm (Eq-Empty-2 _) = rightIdentity _
prop-~-foldBag f comm (Eq-Assoc _ _ _) = sym (associativity _ _ _)
prop-~-foldBag f comm (Eq-Cong-1 x y z rel) =
  cong (_<> foldBag f z) (prop-~-foldBag f comm rel)
prop-~-foldBag f comm (Eq-Cong-2 x y z rel) =
  cong (foldBag f x <>_) (prop-~-foldBag f comm rel)
prop-~-foldBag f comm (Eq-Union-Sym x₁ y) = comm _ _
prop-~-foldBag f comm Eq-Refl = refl
prop-~-foldBag f comm (Eq-Sym rel) = sym (prop-~-foldBag f comm rel)
prop-~-foldBag f comm (Eq-Trans rel1 rel2) =
  trans (prop-~-foldBag f comm rel1) (prop-~-foldBag f comm rel2)
