{-# OPTIONS --prop --postfix-projections --safe #-}
module SystemF.SystemF where
open import Agda.Builtin.Equality
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Fin.Base using (Fin; zero; suc)
open import Function.Base using (id; _∘_)

variable
    m n : ℕ
    i j : Fin n

data Raw : ℕ -> Set where
    var : Fin n -> Raw n
    Π_∙_ : Raw n -> Raw (suc n) -> Raw n
    ^_∙_ : Raw n -> Raw (suc n) -> Raw n
    _∙_ : Raw n -> Raw n -> Raw n
    ⋆ □ : Raw n

data _⊆_ : ℕ -> ℕ -> Set where
    stop : 0 ⊆ 0
    keep : m ⊆ n -> suc m ⊆ suc n
    drop : m ⊆ n -> m ⊆ suc n

⊆-id : ∀ m -> m ⊆ m
⊆-id zero = stop
⊆-id (suc m) = keep (⊆-id m)

↑ : m ⊆ suc m
↑ = drop (⊆-id _)

[_] : m ⊆ n -> Fin m -> Fin n
[ keep ρ ] zero = zero
[ keep ρ ] (suc i) = suc ([ ρ ] i)
[ drop ρ ] i = suc ([ ρ ] i)

ren : m ⊆ n -> Raw m -> Raw n
ren ρ (var i) = var ([ ρ ] i)
ren ρ (Π s ∙ t) = Π ren ρ s ∙ ren (keep ρ) t
ren ρ (^ s ∙ t) = ^ ren ρ s ∙ ren (keep ρ) t
ren ρ (t ∙ s) = ren ρ t ∙ ren ρ s
ren ρ ⋆ = ⋆
ren ρ □ = □

Sub : ℕ -> ℕ -> Set
Sub m n = Fin m -> Raw n

infixl 5 _≪_
_≪_ : Sub m n -> Raw n -> Sub (suc m) n
(ρ ≪ t) zero = t
(ρ ≪ t) (suc i) = ρ i

sub : Sub m n -> Raw m -> Raw n
sub ρ (var i) = ρ i
sub ρ (Π s ∙ t) = Π sub ρ s ∙ sub (ren ↑ ∘ ρ ≪ var zero) t
sub ρ (^ s ∙ t) = ^ sub ρ s ∙ sub (ren ↑ ∘ ρ ≪ var zero) t
sub ρ (t ∙ s) = sub ρ t ∙ sub ρ s
sub ρ ⋆ = ⋆
sub ρ □ = □

𝕫/ : Raw m -> Sub (suc m) m
𝕫/ t = var ∘ [ ⊆-id _ ] ≪ t

data Sort {n} : Raw n -> Set where
    instance ⋆ : Sort ⋆
    instance □ : Sort □

data Axiom {n} : Raw n -> Raw n -> Set where
    instance ⋆:□ : Axiom ⋆ □

data Product {n} : Raw n -> Raw (suc n) -> Raw n -> Set where
    instance func : Product ⋆ ⋆ ⋆

infixr 10 Π_∙_ ^_∙_
infixl 15 _∙_

data Context : ℕ -> Set where
    ∅ : Context 0
    _◂_ : Context n -> Raw n -> Context (suc n)
infixl 5 _◂_

variable
    Γ Δ : Context n
    s s₁ s₂ s₃ t t₁ t₂ t₃ : Raw n

infix 3 _⊢ctx _⊢_∈_

data _⊢ctx : Context n -> Prop
data _⊢_∈_ : (Γ : Context n) -> Raw n -> Raw n -> Prop

data _⊢ctx where
    ∅ : ∅ ⊢ctx
    _◂[_]_ : ∀ {Γ : Context n} -> Γ ⊢ctx
        -> ∀ s ⦃ _ : Sort s ⦄
        -> ∀ {t} -> Γ ⊢ t ∈ s
        -> Γ ◂ t ⊢ctx

data Var : Context n -> Fin n -> Raw n -> Prop where
    𝕫 : Γ ⊢ctx
        -> ∀ s ⦃ _ : Sort s ⦄
        -> ∀ {t} -> Γ ⊢ t ∈ s
        -> Var (Γ ◂ t) zero (ren ↑ t)
    𝕤 : Var Γ i t
        -> ∀ s ⦃ _ : Sort s ⦄
        -> ∀ {t'} -> Γ ⊢ t' ∈ s
        -> Var (Γ ◂ t') (suc i) (ren ↑ t)

data _⊢_∈_ where
    axiom : ⦃ Axiom s₁ s₂ ⦄
        -> Γ ⊢ctx
        -> Γ ⊢ s₁ ∈ s₂
    var : Var Γ i t -> Γ ⊢ var i ∈ t
    prod : Γ ⊢ t ∈ s₁
        -> Γ ◂ t ⊢ s ∈ s₂
        -> ⦃ Product s₁ s₂ s₃ ⦄
        -> Γ ⊢ Π t ∙ s ∈ s₃
    abs : Γ ◂ t₁ ⊢ s ∈ t₂
        -> Γ ⊢ Π t₁ ∙ t₂ ∈ s₁
        -> Γ ⊢ ^ t₁ ∙ s ∈ Π t₁ ∙ t₂
    app : Γ ⊢ t ∈ Π t₁ ∙ t₂
        -> Γ ⊢ s ∈ t₁
        -> Γ ⊢ t ∙ s ∈ sub (𝕫/ s) t₂

infixr 13 _⇒_
_⇒_ : Raw n -> Raw n -> Raw n
t ⇒ s = Π t ∙ ren ↑ s

𝕀 : Raw 1
𝕀 = ^ var zero ∙ var zero

ℑ : ∅ ◂ ⋆ ⊢ 𝕀 ∈ var zero ⇒ var zero
ℑ = abs
    (var (𝕫 (∅ ◂[ □ ] (axiom ∅)) ⋆
        (var (𝕫 ∅ □ (axiom ∅)))))
    (prod (var (𝕫 ∅ □ (axiom ∅)))
        (var (𝕤 (𝕫 ∅ □ (axiom ∅)) ⋆
            (var (𝕫 ∅ □ (axiom ∅))))))
