
module Data.Map.Prop.Extra where

open import Haskell.Prelude hiding (lookup; null; map; filter)

open import Data.Map
import Haskell.Prelude as List using (lookup)

import Data.Monoid.Refinement as Monoid

open import Haskell.Law.Eq
open import Haskell.Law.Equality
open import Haskell.Law.Monoid

------------------------------------------------------------------------------
-- Move out: Properties of if_then_else

prop-if-apply
  : ∀ (f : a → c) (b : Bool) (t e : a)
  → f (if b then t else e) ≡ (if b then f t else f e)
prop-if-apply f True = λ t e → refl
prop-if-apply f False = λ t e → refl

------------------------------------------------------------------------------
-- Move out: Utilities for using transitivity of `==`

-- Utlity for transitivity.
prop-if2then3 : Bool → Bool → Bool → Type
prop-if2then3 True  True  False = ⊥
prop-if2then3 True  False True  = ⊥
prop-if2then3 False True  True  = ⊥
prop-if2then3 x     y     z     = ⊤

-- | Utility for ruling out cases in 'with' expressions on '(==)'.
guard-eq-trans
  : ∀ ⦃ iEq : Eq e ⦄ ⦃ _ : IsLawfulEq e ⦄ (x y z : e)
  → prop-if2then3 (x == y) (y == z) (x == z)
--
guard-eq-trans x y z
  with x == y in eqxy | y == z in eqyz
... | False | False = tt
... | False | True  rewrite sym (equality y z eqyz) | eqxy = tt
... | True  | False rewrite sym (equality x y eqxy) | eqyz = tt
... | True  | True  rewrite sym (equality y z eqyz) | eqxy = tt

{-----------------------------------------------------------------------------
    Proofs
    toAscList
------------------------------------------------------------------------------}
module _ {k : Type} ⦃ _ : Ord k ⦄ where

  postulate
   prop-lookup-toAscList
    : ∀ (ma : Map k a) (key : k)
    → List.lookup key (toAscList ma)
      ≡ lookup key ma

  postulate
   prop-fromList-toAscList
    : ∀ (ma : Map k a)
    → fromList (toAscList ma) ≡ ma

  -- | For commutative monoids,
  -- @'unionWith' (<>)@ commutes with 'fold'.
  postulate
    prop-fold-unionWith
      : ∀ ⦃ _ : Monoid.Commutative a ⦄ (ma mb : Map k a)
      → let fold = foldMap id
        in  fold (unionWith (_<>_) ma mb)
              ≡ fold ma <> fold mb

  postulate
   prop-toAscList-singleton
    : ∀ (key : k) (x : a)
    → toAscList (singleton key x) ≡ (key , x) ∷ []

  postulate
   prop-toAscList-empty
    : toAscList (empty {k} {a}) ≡ []

{-----------------------------------------------------------------------------
    Proofs
    foldMap id
------------------------------------------------------------------------------}
module _ {k : Type} ⦃ _ : Ord k ⦄ where

  --
  prop-fold-singleton
    : ∀ ⦃ _ : Monoid a ⦄ ⦃ _ : IsLawfulMonoid a ⦄ (key : k) (x : a)
    → let fold = foldMap id
      in  fold (singleton key x) ≡ x
  --
  prop-fold-singleton key x
    rewrite prop-toAscList-singleton key x
    = rightIdentity _

{-----------------------------------------------------------------------------
    Proofs
    unionWith
------------------------------------------------------------------------------}
module _ {k : Type} ⦃ _ : Ord k ⦄ where

  --
  prop-unionWith-empty-x
    : ∀ {f : a → a → a} {ma : Map k a}
    → unionWith f empty ma ≡ ma
  --
  prop-unionWith-empty-x {a} {f} {ma} = prop-equality eq-key
    where
      eq-key
        : ∀ (key : k)
        → lookup key (unionWith f empty ma)
          ≡ lookup key ma
      eq-key key
        rewrite prop-lookup-unionWith key f empty ma
        rewrite prop-lookup-empty {k} {a} key
        = refl

  --
  prop-unionWith-x-empty
    : ∀ {f : a → a → a} {ma : Map k a}
    → unionWith f ma empty ≡ ma
  --
  prop-unionWith-x-empty {a} {f} {ma} = prop-equality eq-key
    where
      eq-key
        : ∀ (key : k)
        → lookup key (unionWith f ma empty)
          ≡ lookup key ma
      eq-key key
        rewrite prop-lookup-unionWith key f ma empty
        rewrite prop-lookup-empty {k} {a} key
        with lookup key ma
      ... | Nothing = refl
      ... | Just x  = refl

  --
  prop-unionWith-assoc
    : ∀ {f : a → a → a} {ma mb mc : Map k a}
    → (∀ x y z → f (f x y) z ≡ f x (f y z))
    → unionWith f (unionWith f ma mb) mc
      ≡ unionWith f ma (unionWith f mb mc)
  --
  prop-unionWith-assoc {a} {f} {ma} {mb} {mc} f-assoc = prop-equality eq-key
    where
      eq-key
        : ∀ (key : k)
        → lookup key (unionWith f (unionWith f ma mb) mc)
          ≡ lookup key (unionWith f ma (unionWith f mb mc))
      eq-key key
        rewrite prop-lookup-unionWith key f (unionWith f ma mb) mc
        rewrite prop-lookup-unionWith key f ma (unionWith f mb mc)
        rewrite prop-lookup-unionWith key f ma mb
        rewrite prop-lookup-unionWith key f mb mc
        with lookup key ma | lookup key mb
      ... | Nothing | Nothing = refl
      ... | Nothing | Just y  = refl
      ... | Just x  | Nothing = refl
      ... | Just x  | Just y
          with lookup key mc
      ...   | Nothing = refl
      ...   | Just z  = cong Just (f-assoc x y z)

{-----------------------------------------------------------------------------
    Proofs
    intersectionWith
------------------------------------------------------------------------------}
module _ {k : Type} ⦃ _ : Ord k ⦄ where

  -- | 'intersectionWith' an empty 'Map' yields again an empty 'Map'.
  prop-intersectionWith-empty-x
    : ∀ (f : a → b → c) (ys : Map k b)
    → intersectionWith f (empty {k} {a}) ys ≡ empty
  --
  prop-intersectionWith-empty-x {a} {b} {c} f ys =
      prop-equality lemma
    where
      lemma
        : ∀ (key : k)
        → lookup key (intersectionWith f (empty {k} {a}) ys)
          ≡ lookup key empty
      lemma key
        rewrite prop-lookup-intersectionWith key empty ys f
        rewrite prop-lookup-empty {k} {a} key
        rewrite prop-lookup-empty {k} {c} key
        = refl

  -- | 'intersectionWith' an empty 'Map' yields again an empty 'Map'.
  prop-intersectionWith-x-empty
    : ∀ (f : a → b → c) (xs : Map k a)
    → intersectionWith f xs (empty {k} {b}) ≡ empty
  --
  prop-intersectionWith-x-empty {a} {b} {c} f xs =
      prop-equality lemma
    where
      lemma
        : ∀ (key : k)
        → lookup key (intersectionWith f xs (empty {k} {b}))
          ≡ lookup key empty
      lemma key
        rewrite prop-lookup-intersectionWith key xs empty f
        rewrite prop-lookup-empty {k} {b} key
        rewrite prop-lookup-empty {k} {c} key
        with lookup key xs
      ... | Nothing = refl
      ... | Just x  = refl

  -- | 'intersectionWith' on singletons.
  prop-intersectionWith-singleton
    : ∀ ⦃ _ : IsLawfulEq k ⦄ (f : a → b → c) (keyx : k) (x : a) (keyy : k) (y : b)
    → intersectionWith f (singleton keyx x) (singleton keyy y)
      ≡ (if keyx == keyy then singleton keyx (f x y) else empty)
  --
  prop-intersectionWith-singleton {a} {b} {c} f keyx x keyy y =
      prop-equality lemma
    where
      lemma
        : ∀ (key : k)
        → lookup key (intersectionWith f (singleton keyx x) (singleton keyy y))
          ≡ lookup key (if keyx == keyy then singleton keyx (f x y) else empty)
      lemma key
        rewrite prop-lookup-intersectionWith key (singleton keyx x) (singleton keyy y) f
        rewrite prop-lookup-singleton key keyx x
        rewrite prop-lookup-singleton key keyy y
        rewrite prop-if-apply (lookup key) (keyx == keyy) (singleton keyx (f x y)) empty
        rewrite prop-lookup-singleton key keyx (f x y)
        rewrite prop-lookup-empty {k} {c} key
        rewrite eqSymmetry key keyx
        with _ ← guard-eq-trans keyx key keyy
        with keyx == key | key == keyy | keyx == keyy
      ... | False | False | False = refl
      ... | False | False | True  = refl
      ... | False | True  | False = refl
      ... | True  | False | False = refl
      ... | True  | True  | True  = refl

  -- | 'intersectionWith' distributes over 'unionWith' in the second argument
  -- if the involved functions distribute over each other.
  prop-intersectionWith-x-unionWith
    : ∀ (f : a → b → c) (xs : Map k a) (g : b → b → b) (ys zs : Map k b)
        (g' : c → c → c)
    → (∀ x y z → f x (g y z) ≡ g' (f x y) (f x z))
    → intersectionWith f xs (unionWith g ys zs)
      ≡ unionWith g' (intersectionWith f xs ys) (intersectionWith f xs zs)
  --
  prop-intersectionWith-x-unionWith f xs g ys zs g' cond =
      prop-equality lemma
    where
      lemma
        : ∀ (key : k)
        → lookup key (intersectionWith f xs (unionWith g ys zs))
          ≡ lookup key (unionWith g' (intersectionWith f xs ys) (intersectionWith f xs zs))
      lemma key
        rewrite prop-lookup-intersectionWith key xs (unionWith g ys zs) f
        rewrite prop-lookup-unionWith key g ys zs
        rewrite prop-lookup-unionWith key g' (intersectionWith f xs ys) (intersectionWith f xs zs)
        rewrite prop-lookup-intersectionWith key xs ys f
        rewrite prop-lookup-intersectionWith key xs zs f
        with lookup key xs
      ... | Nothing = refl 
      ... | Just x
          with lookup key ys | lookup key zs
      ...   | Nothing | Nothing = refl
      ...   | Nothing | Just z  = refl
      ...   | Just y  | Nothing = refl
      ...   | Just y  | Just z  = cong Just (cond x y z)

  -- | 'intersectionWith' distributes over 'unionWith' in the second argument
  -- if the involved functions distribute over each other.
  prop-intersectionWith-unionWith-x
    : ∀ (f : a → b → c) (xs ys : Map k a) (g : a → a → a) (zs : Map k b)
        (g' : c → c → c)
    → (∀ x y z → f (g x y) z ≡ g' (f x z) (f y z))
    → intersectionWith f (unionWith g xs ys) zs
      ≡ unionWith g' (intersectionWith f xs zs) (intersectionWith f ys zs)
  --
  prop-intersectionWith-unionWith-x f xs ys g zs g' cond =
      prop-equality lemma
    where
      lemma
        : ∀ (key : k)
        → lookup key (intersectionWith f (unionWith g xs ys) zs)
          ≡ lookup key (unionWith g' (intersectionWith f xs zs) (intersectionWith f ys zs))
      lemma key
        rewrite prop-lookup-intersectionWith key (unionWith g xs ys) zs f
        rewrite prop-lookup-unionWith key g xs ys
        rewrite prop-lookup-unionWith key g' (intersectionWith f xs zs) (intersectionWith f ys zs)
        rewrite prop-lookup-intersectionWith key xs zs f
        rewrite prop-lookup-intersectionWith key ys zs f
        with lookup key xs | lookup key ys | lookup key zs
      ... | Nothing | Nothing | Nothing = refl 
      ... | Nothing | Nothing | Just z  = refl 
      ... | Nothing | Just y  | Nothing = refl 
      ... | Nothing | Just y  | Just z  = refl 
      ... | Just x  | Nothing | Nothing = refl 
      ... | Just x  | Nothing | Just z  = refl 
      ... | Just x  | Just y  | Nothing = refl 
      ... | Just x  | Just y  | Just z  = cong Just (cond x y z) 

{-----------------------------------------------------------------------------
    Proofs
    mapWithKey
------------------------------------------------------------------------------}
module _ {k : Type} ⦃ _ : Ord k ⦄ where

  -- | 'mapWithKey' on a singleton maps the element of the singleton.
  prop-mapWithKey-singleton
    : ∀ ⦃ _ : IsLawfulEq k ⦄ (f : k → a → b) (key : k) (x : a)
    → mapWithKey f (singleton key x) ≡ singleton key (f key x) 
  --
  prop-mapWithKey-singleton {a = a} {b = b} f key x = prop-equality lemma
    where
      lemma
        : ∀ (key2 : k)
        → lookup key2 (mapWithKey f (singleton key x))
          ≡ lookup key2 (singleton key (f key x))
      lemma key2
        rewrite prop-lookup-mapWithKey key2 (singleton key x) f
        rewrite prop-lookup-insert {a = a} key2 key x empty
        rewrite prop-lookup-empty {a = a} key2
        rewrite prop-lookup-insert {a = b} key2 key (f key x) empty
        rewrite prop-lookup-empty {a = b} key2
        with key2 == key in eq
      ... | False = refl
      ... | True  rewrite equality key2 key eq = refl

  -- | 'mapWithKey' an an empty map gives the empty map.
  prop-mapWithKey-empty
    : ∀ (f : k → a → b)
    → mapWithKey f empty ≡ empty
  --
  prop-mapWithKey-empty {a = a} {b = b} f = prop-equality lemma
    where
      lemma
        : ∀ (key : k) → lookup key (mapWithKey f empty) ≡ lookup key empty
      lemma key
        rewrite prop-lookup-mapWithKey key empty f
        rewrite prop-lookup-empty {a = a} key
        rewrite prop-lookup-empty {a = b} key
        = refl

  -- | 'mapWithKey' distributes over 'unionWith' if the
  -- involved functions distribue over each other.
  prop-mapWithKey-unionWith
    : ∀ (f : k → a → b) (g : a → a → a) (xs ys : Map k a)
        (g' : b → b → b)
    → (∀ key x y → f key (g x y) ≡ g' (f key x) (f key y))
    → mapWithKey f (unionWith g xs ys)
      ≡ unionWith g' (mapWithKey f xs) (mapWithKey f ys)
  --
  prop-mapWithKey-unionWith f g xs ys g' cond = prop-equality lemma
    where
      lemma
        : ∀ (key : k)
        → lookup key (mapWithKey f (unionWith g xs ys))
          ≡ lookup key (unionWith g' (mapWithKey f xs) (mapWithKey f ys))
      lemma key
        rewrite prop-lookup-mapWithKey key (unionWith g xs ys) f
        rewrite prop-lookup-unionWith key g xs ys
        rewrite prop-lookup-unionWith key g' (mapWithKey f xs) (mapWithKey f ys)
        rewrite prop-lookup-mapWithKey key xs f
        rewrite prop-lookup-mapWithKey key ys f
        with lookup key xs | lookup key ys
      ... | Nothing | Nothing = refl
      ... | Nothing | Just y  = refl
      ... | Just x  | Nothing = refl
      ... | Just x  | Just y  = cong Just (cond key x y)
