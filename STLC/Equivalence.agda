{-# OPTIONS --prop --safe #-}
module STLC.Equivalence where
open import Agda.Primitive
open import Agda.Builtin.Equality
open import Function.Base using (_$_; _∘_; id; _∋_) public
open import Data.Empty using (⊥) public

private variable
    ℓ ℓ' : Level
    A B C : Set ℓ
    P Q R : Prop ℓ

infixl 10 _⊚_
_⊚_ :  -- The _∘_ from stdlib doesn't work on Props
    (P -> Q) -> (R -> P) -> (R -> Q)
(f ⊚ g) z = f (g z)
{-# INLINE _⊚_ #-}

-- We develop the theory of equivalence closures once and for all.
data Equivalence {A : Set ℓ} (_~_ : A -> A -> Prop ℓ') : A -> A -> Prop (ℓ ⊔ ℓ') where
    refl : ∀ {a} -> Equivalence _~_ a a
    step : ∀ {a b c} -> a ~ b -> Equivalence _~_ b c -> Equivalence _~_ a c
    back : ∀ {a b c} -> b ~ a -> Equivalence _~_ b c -> Equivalence _~_ a c

pattern single r = step r refl
pattern _⟶_ r R = step r R
pattern _⟵_ r R = back r R
infixr 3 _⟶_ _⟵_

private variable
    a b c : A
    _~_ _-_ : A -> A -> Prop ℓ

-- Concatenation:
_⁀_ : Equivalence _~_ a b -> Equivalence _~_ b c -> Equivalence _~_ a c
refl ⁀ R' = R'
step r R ⁀ R' = step r (R ⁀ R')
back r R ⁀ R' = back r (R ⁀ R')
infixl 5 _⁀_

-- Reversal:
_⁻¹ : Equivalence _~_ a b -> Equivalence _~_ b a
R ⁻¹ = helper refl R
    where
        helper : Equivalence _~_ b a
            -> Equivalence _~_ b c
            -> Equivalence _~_ c a
        helper R refl = R
        helper R (step r R') = helper (back r R) R'
        helper R (back r R') = helper (step r R) R'
infixl 20 _⁻¹

-- Maps
map : {f : A -> B} (F : ∀ {a b} -> a ~ b -> f a - f b)
    -> Equivalence _~_ a b -> Equivalence _-_ (f a) (f b)
map F refl = refl
map F (step r R) = step (F r) (map F R)
map F (back r R) = back (F r) (map F R)

record Subset (A : Set ℓ) (B : A -> Prop ℓ') : Set (ℓ ⊔ ℓ') where
    constructor ι
    field
        object : A
        witness : B object
syntax Subset A (λ a -> B) = [ a ∈ A ∣ B ]

data _∧_ (A : Prop ℓ) (B : Prop ℓ') : Prop (ℓ ⊔ ℓ') where
    ⟨_,_⟩ : A -> B -> A ∧ B
infixl 3 _∧_
