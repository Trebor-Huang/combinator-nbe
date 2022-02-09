{-# OPTIONS --prop --safe #-}
module combinator where
open import Agda.Builtin.Nat using (Nat; suc; zero)

-- We work with the natural numbers as a base type.
data Type : Set where
    ℕ : Type
    _⇒_ : Type -> Type -> Type
infixr 10 _⇒_

private variable
    α β γ : Type
    n : Nat

-- Now the combinators.
data Term : Type -> Set where
    O : Term ℕ
    S : Term (ℕ ⇒ ℕ)
    ℝ : Term (ℕ ⇒ α ⇒ (ℕ ⇒ α ⇒ α) ⇒ α)
    𝕂 : Term (α ⇒ β ⇒ α)
    𝕊 : Term ((α ⇒ β ⇒ γ) ⇒ (α ⇒ β) ⇒ (α ⇒ γ))
    _∙_ : Term (α ⇒ β) -> Term α -> Term β
infixl 16 _∙_

private variable
    M N A B C : Term α

-- Each natural number in Agda corresponds to a term S (S .. (S O))
-- in our combinator language.
# : Nat -> Term ℕ
# zero = O
# (suc n) = S ∙ # n

-- Some familiar combinators:
𝕀 : Term (α ⇒ α)
𝕀 = 𝕊 ∙ 𝕂 ∙ 𝕂 {β = ℕ}
-- Here since β could be anything (it doesn't change the behaviour), Agda
-- needs us to pick a specific type.

ℂ : Term ((α ⇒ β ⇒ γ) ⇒ (β ⇒ α ⇒ γ))
ℂ = 𝕊 ∙ (𝕊 ∙ (𝕂 ∙ (𝕊 ∙ (𝕂 ∙ 𝕊) ∙ 𝕂)) ∙ 𝕊) ∙ (𝕂 ∙ 𝕂)

𝔹 : Term ((β ⇒ γ) ⇒ (α ⇒ β) ⇒ (α ⇒ γ))
𝔹 = 𝕊 ∙ (𝕂 ∙ 𝕊) ∙ 𝕂

-- Using ℝ we can construct arithmetical functions:
Add : Term (ℕ ⇒ ℕ ⇒ ℕ)
Add = 𝕊 ∙ (𝕊 ∙ (𝕂 ∙ 𝕊) ∙ ℝ) ∙ (𝕂 ∙ (𝕂 ∙ (𝕂 ∙ S)))

Mult : Term (ℕ ⇒ ℕ ⇒ ℕ)
Mult = 𝕊 ∙ (𝕂 ∙ (𝕊 ∙ (𝕊 ∙ ℝ ∙ (𝕂 ∙ O)))) ∙ (𝕊 ∙ (𝕂 ∙ 𝕂) ∙ (𝕊 ∙ (𝕂 ∙ 𝕂) ∙ Add))

Fact : Term (ℕ ⇒ ℕ)
Fact = 𝕊 ∙ (𝕊 ∙ ℝ ∙ (𝕂 ∙ (S ∙ O))) ∙ (𝕂 ∙ (𝕊 ∙ (𝕂 ∙ Mult) ∙ S))

-- We need to define a set of normal forms.
-- NF M means "M is in normal form".
data NF : Term α -> Set where
    -- Numerals are normal.
    ℕ : ∀ n -> NF (# n)
    -- Note that instead of this we could have declared
    --    O₀ : NF O
    --    S₁ : NF A -> NF (S ∙ A)
    -- Exercise: what are the pros and cons for this choice?
    S₀ : NF S
    -- We also need to take care of partially applied combinators.
    -- The subscripts say how many arguments are already supplied.
    ℝ₀ : NF (ℝ {α = α})
    ℝ₁ : NF A -> NF (ℝ {α = α} ∙ A)
    ℝ₂ : NF A -> NF B -> NF (ℝ ∙ A ∙ B)
    𝕂₀ : NF (𝕂 {α = α} {β = β})
    𝕂₁ : NF A -> NF (𝕂 {β = β} ∙ A)
    𝕊₀ : NF (𝕊 {α = α} {β = β} {γ = γ})
    𝕊₁ : NF A -> NF (𝕊 ∙ A)
    𝕊₂ : NF A -> NF B -> NF (𝕊 ∙ A ∙ B)

-- Next, we define reduction.
infix 3 _~>_ _⟶₁_ _⟶_
-- _~>_ describes redexes, i.e. terms that can be reduced directly.
data _~>_ : Term α -> Term α -> Prop where
    ℝ0 : ℝ ∙ O ∙ A ∙ B ~> A
    ℝS : ℝ ∙ (S ∙ A) ∙ B ∙ C ~> C ∙ A ∙ (ℝ ∙ A ∙ B ∙ C)
    𝕂 : 𝕂 ∙ A ∙ B ~> A
    𝕊 : 𝕊 ∙ A ∙ B ∙ C ~> (A ∙ C) ∙ (B ∙ C)

-- _⟶₁_ describes single-step reductions.
data _⟶₁_ {α} : Term α -> Term α -> Prop where
    red : A ~> B -> A ⟶₁ B
    appₗ : A ⟶₁ B -> A ∙ C ⟶₁ B ∙ C
    appᵣ : A ⟶₁ B -> C ∙ A ⟶₁ C ∙ B

-- _⟶_ is the transitive closure of _⟶₁_.
data _⟶_ {α} : Term α -> Term α -> Prop where
    refl : A ⟶ A
    step : A ⟶₁ B -> B ⟶ C -> A ⟶ C

-- Auxiliary functions:
-- Corresponds to singleton lists, list concatenation and maps.
single : A ⟶₁ B -> A ⟶ B
single r = step r refl
{-# INLINE single #-}

_⁀_ : A ⟶ B -> B ⟶ C -> A ⟶ C
refl ⁀ R' = R'
step r R ⁀ R' = step r (R ⁀ R')

map : {F : Term α -> Term β}
    -> (∀ {A B} -> (A ⟶₁ B) -> (F A ⟶₁ F B))
    -> (∀ {A B} -> (A ⟶  B) -> (F A ⟶  F B))
map f refl = refl
map f (step r R) = step (f r) (map f R)

-- WN A stores a normal form, and a proof that A reduces to that form.
-- In other words, WN A means "A is weakly normalizing".
data WN (A : Term α) : Set where  -- Glue!
    wn : NF B -> A ⟶ B -> WN A

-- SN A means "A is strongly normalizing", i.e. 𝑒𝑣𝑒𝑟𝑦 way to reduce A
-- must eventually reach a normal form.
data SN (A : Term α) : Set where
    sn : (∀ {B} -> A ⟶₁ B -> SN B) -> SN A

open import Function.Base using (_$_) public

infixl 10 _∘_
_∘_ : {P Q R : Prop}  -- The _∘_ from stdlib doesn't work on Props
    -> (P -> Q) -> (R -> P) -> (R -> Q)
(f ∘ g) z = f (g z)
{-# INLINE _∘_ #-}
