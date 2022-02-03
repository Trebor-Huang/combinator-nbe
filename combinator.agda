{-# OPTIONS --prop #-}
module combinator where
open import Agda.Builtin.Nat using (Nat; suc; zero)

data Type : Set where
    ℕ : Type
    _⇒_ : Type -> Type -> Type
infixr 10 _⇒_

variable
    α β γ : Type
    n : Nat

data Term : Type -> Set where
    O : Term ℕ
    S : Term (ℕ ⇒ ℕ)
    ℝ : Term (ℕ ⇒ α ⇒ (α ⇒ α) ⇒ α)
    𝕂 : Term (α ⇒ β ⇒ α)
    𝕊 : Term ((α ⇒ β ⇒ γ) ⇒ (α ⇒ β) ⇒ (α ⇒ γ))
    _∙_ : Term (α ⇒ β) -> Term α -> Term β
infixl 9 _∙_

variable
    M N A B C : Term α

# : Nat -> Term ℕ
# zero = O
# (suc n) = S ∙ # n

𝕀 : Term (α ⇒ α)
𝕀 = 𝕊 ∙ 𝕂 ∙ 𝕂 {β = ℕ}

ℂ : Term ((α ⇒ β ⇒ γ) ⇒ (β ⇒ α ⇒ γ))
ℂ = 𝕊 ∙ (𝕊 ∙ (𝕂 ∙ (𝕊 ∙ (𝕂 ∙ 𝕊) ∙ 𝕂)) ∙ 𝕊) ∙ (𝕂 ∙ 𝕂)

𝔹 : Term ((β ⇒ γ) ⇒ (α ⇒ β) ⇒ (α ⇒ γ))
𝔹 = 𝕊 ∙ (𝕂 ∙ 𝕊) ∙ 𝕂

Add : Term (ℕ ⇒ ℕ ⇒ ℕ)
Add = 𝕊 ∙ (𝕊 ∙ (𝕂 ∙ 𝕊) ∙ ℝ) ∙ (𝕂 ∙ (𝕂 ∙ S))

Mult : Term (ℕ ⇒ ℕ ⇒ ℕ)
Mult = 𝕊 ∙ (𝕊 ∙ (𝕂 ∙ 𝕊) ∙ (𝕊 ∙ (𝕂 ∙ 𝕂) ∙ (ℂ ∙ ℝ ∙ O))) ∙ (𝕂 ∙ Add)

data NF : Term α -> Set where  -- Glue!
    ℕ : ∀ n -> NF (# n)
    S₀ : NF S
    ℝ₀ : NF (ℝ {α = α})
    ℝ₁ : NF A -> NF (ℝ {α = α} ∙ A)
    ℝ₂ : NF A -> NF B -> NF (ℝ ∙ A ∙ B)
    𝕂₀ : NF (𝕂 {α = α} {β = β})
    𝕂₁ : NF A -> NF (𝕂 {β = β} ∙ A)
    𝕊₀ : NF (𝕊 {α = α} {β = β} {γ = γ})
    𝕊₁ : NF A -> NF (𝕊 ∙ A)
    𝕊₂ : NF A -> NF B -> NF (𝕊 ∙ A ∙ B)

infix 3 _~>_ _->₁_ _⟶_
data _~>_ : Term α -> Term α -> Prop where
    ℝ0 : ℝ ∙ O ∙ A ∙ B ~> A
    ℝS : ℝ ∙ (S ∙ A) ∙ B ∙ C ~> C ∙ (ℝ ∙ A ∙ B ∙ C)
    𝕂 : 𝕂 ∙ A ∙ B ~> A
    𝕊 : 𝕊 ∙ A ∙ B ∙ C ~> (A ∙ C) ∙ (B ∙ C)

data _->₁_ {α} : Term α -> Term α -> Prop where
    red : A ~> B -> A ->₁ B
    appₗ : A ->₁ B -> A ∙ C ->₁ B ∙ C
    appᵣ : A ->₁ B -> C ∙ A ->₁ C ∙ B

data _⟶_ {α} : Term α -> Term α -> Prop where
    refl : A ⟶ A
    step : A ->₁ B -> B ⟶ C -> A ⟶ C

single : A ->₁ B -> A ⟶ B
single r = step r refl

_⁀_ : A ⟶ B -> B ⟶ C -> A ⟶ C
refl ⁀ R' = R'
step r R ⁀ R' = step r (R ⁀ R')

map : {F : Term α -> Term β}
    -> (∀ {A B} -> (A ->₁ B) -> (F A ->₁ F B))
    -> (∀ {A B} -> (A ⟶ B) -> (F A ⟶ F B))
map f refl = refl
map f (step r R) = step (f r) (map f R)

data WN (A : Term α) : Set where  -- Glue!
    wn : NF B -> A ⟶ B -> WN A

