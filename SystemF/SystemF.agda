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
    instance poly : Product □ ⋆ ⋆

infixr 10 Π_∙_ ^_∙_
infixl 15 _∙_

data Context : ℕ -> Set where
    ∅ : Context 0
    _◂_ : Context n -> Raw n -> Context (suc n)
infixl 5 _◂_

variable
    Γ Δ : Context n
    s s₁ s₂ s₃ t t₁ t₂ t₃ u v w : Raw n

infix 3 _⊢ctx _⊢_∈_ _⊢_~>_∈_ _⊢_⟶_∈_ _⊢_==_∈_

data _⊢ctx : Context n -> Prop
data _⊢_∈_ : (Γ : Context n) -> Raw n -> Raw n -> Prop
data _⊢_~>_∈_ : (Γ : Context n) -> Raw n -> Raw n -> Raw n -> Prop
data _⊢_⟶_∈_ : (Γ : Context n) -> Raw n -> Raw n -> Raw n -> Prop
data _⊢_==_∈_ (Γ : Context n) : Raw n -> Raw n -> Raw n -> Prop

data _⊢ctx where
    ∅ : ∅ ⊢ctx
    _◂[_]_ : ∀ {Γ : Context n} -> Γ ⊢ctx
        -> ∀ s ⦃ _ : Sort s ⦄
        -> ∀ {t} -> Γ ⊢ t ∈ s
        -> Γ ◂ t ⊢ctx

data Var : Context n -> Fin n -> Raw n -> Prop where
    𝕫 : ∀ s ⦃ _ : Sort s ⦄
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
        -> ⦃ _ : Product s₁ s₂ s₃ ⦄
        -> Γ ⊢ Π t ∙ s ∈ s₃
    abs : Γ ◂ t₁ ⊢ s ∈ t₂
        -> Γ ⊢ Π t₁ ∙ t₂ ∈ s₁
        -> Γ ⊢ ^ t₁ ∙ s ∈ Π t₁ ∙ t₂
    app : Γ ⊢ t ∈ Π t₁ ∙ t₂
        -> Γ ⊢ s ∈ t₁
        -> Γ ⊢ t ∙ s ∈ sub (𝕫/ s) t₂
    conv : Γ ⊢ t ∈ s₁
        -> Γ ⊢ s₁ == s₂ ∈ s
        -> Γ ⊢ t ∈ s₂

data _⊢_~>_∈_ where
    β! : Γ ◂ u ⊢ t ∈ v
        -> Γ ⊢ s ∈ u
        -> Γ ⊢ (^ u ∙ t) ∙ s ~> sub (𝕫/ s) t ∈ sub (𝕫/ s) v
    η! : Γ ⊢ t ∈ Π u ∙ v
        -> Γ ⊢ t ~> (^ u ∙ (ren ↑ t ∙ var zero)) ∈ Π u ∙ v

data _⊢_⟶_∈_ where
    red : Γ ◂ u ⊢ t ∈ v
        -> Γ ⊢ s₁ ~> s₂ ∈ u
        -> Γ ⊢ sub (𝕫/ s₁) t ⟶ sub (𝕫/ s₂) t ∈ sub (𝕫/ s₁) v

data _⊢_==_∈_ Γ where
    step : Γ ⊢ t₁ ⟶ t₂ ∈ u
        -> Γ ⊢ t₁ == t₂ ∈ u
    refl : Γ ⊢ t ∈ u
        -> Γ ⊢ t == t ∈ u
    symm : Γ ⊢ t == s ∈ u
        -> Γ ⊢ s == t ∈ u
    tran : Γ ⊢ s₁ == s₂ ∈ u
        -> Γ ⊢ s₂ == s₃ ∈ u
        -> Γ ⊢ s₁ == s₂ ∈ u
    conv : Γ ⊢ t₁ == t₂ ∈ u
        -> Γ ⊢ u == v ∈ s
        -> Γ ⊢ t₁ == t₂ ∈ v

infixr 13 _⇒_
_⇒_ : Raw n -> Raw n -> Raw n
t ⇒ s = Π t ∙ ren ↑ s

ℐ : Raw 1
ℐ = ^ var zero ∙ var zero

𝐼 : ∅ ◂ ⋆ ⊢ ℐ ∈ var zero ⇒ var zero
𝐼 = let α = 𝕫 □ (axiom ∅) in
    abs
        (var (𝕫 ⋆ (var α)))
        (prod (var α) (var (𝕤 α ⋆ (var α))))

𝓘 : Raw 0
𝓘 = ^ ⋆ ∙ ℐ

𝑰 : ∅ ⊢ 𝓘 ∈ Π ⋆ ∙ var zero ⇒ var zero
𝑰 = let α = 𝕫 □ (axiom ∅) in
    abs 𝐼 (prod {s₁ = □} (axiom ∅)
        (prod (var α)
            (var (𝕤 α ⋆
                (var α)))))
