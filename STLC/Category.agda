{-# OPTIONS --prop --postfix-projections --safe #-}
module STLC.Category where
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Sum using (_⊎_; inj₁; inj₂)

open import STLC.Equivalence
open import STLC.STLC
open import STLC.Substitution

private variable
    α β γ : Type
    Γ Δ Ξ : Context
    σ τ σ₁ σ₂ σ₃ : Substitution Γ Δ

Obj : Set
Obj = Context

Mor : Obj -> Obj -> Set
Mor Γ Δ = {α : Type} -> Var Δ α -> Term Γ α

idMor : Mor Γ Γ
idMor = var

compMor : Mor Γ Δ -> Mor Ξ Γ -> Mor Ξ Δ
compMor σ τ = sub τ ∘ σ

-- To prevent Agda inserting implicit arguments.
-- Also to avoid function extensionality.
_==_ : Mor Γ Δ -> Mor Γ Δ -> Set
σ == τ = ∀ {α} {v : Var _ α} -> σ v ≡ τ v
infix 3 _==_

idₗ : compMor idMor σ == σ
idₗ = refl

idᵣ : compMor σ idMor == σ
idᵣ = sub-var _

assoc : compMor (compMor σ₁ σ₂) σ₃ == compMor σ₁ (compMor σ₂ σ₃)
assoc {σ₁ = σ₁} {σ₂ = σ₂} {σ₃ = σ₃} {v = v}
    = sub-sub σ₃ σ₂ (σ₁ v)

_×_ : Obj -> Obj -> Obj
Γ × ∅ = Γ
Γ × (Δ ◂ α) = (Γ ◂ α) × Δ
infixl 20 _×_

private
    p₁ : Renaming Γ (Γ × Δ)
    p₁ {Δ = ∅} v = v
    p₁ {Δ = Δ ◂ _} v = p₁ {Δ = Δ} (𝕤 v)

    p₂ : Renaming Δ (Γ × Δ)
    p₂ {Δ = Δ ◂ _} 𝕫 = p₁ {Δ = Δ} 𝕫
    p₂ {Δ = Δ ◂ _} (𝕤 v) = p₂ v

    split : Var (Γ × Δ) α -> Var Γ α ⊎ Var Δ α
    split {Δ = ∅} v = inj₁ v
    split {Δ = Δ ◂ _} v with split {Δ = Δ} v
    ... | inj₁ 𝕫 = inj₂ 𝕫
    ... | inj₁ (𝕤 v) = inj₁ v
    ... | inj₂ v = inj₂ (𝕤 v)

π₁ : Mor (Γ × Δ) Γ
π₁ {Δ = Δ₀} x = var (p₁ {Δ = Δ₀} x)

π₂ : Mor (Γ × Δ) Δ
π₂ v = var (p₂ v)

⟨_×_⟩ : Mor Ξ Γ -> Mor Ξ Δ -> Mor Ξ (Γ × Δ)
⟨_×_⟩ {Δ = Δ} σ τ v with split {Δ = Δ} v
... | inj₁ v = σ v
... | inj₂ v = τ v

𝟏 : Obj
𝟏 = ∅

Telescope : Context -> Type -> Type
Telescope ∅ α = α
Telescope (Γ ◂ β) α = β ⇒ Telescope Γ α

abs : Term (Δ × Γ) α -> Term Δ (Telescope Γ α)
abs {Γ = ∅} t = t
abs {Γ = Γ ◂ _} t = ^ abs t

Hom : Obj -> Obj -> Obj
Hom Γ ∅ = ∅
Hom Γ (Δ ◂ α) = Hom Γ Δ ◂ Telescope Γ α

uncurry : Mor Γ (Hom Ξ Δ) -> Mor (Γ × Ξ) Δ
uncurry {Ξ = Ξ} σ 𝕫 = {!   !}
uncurry σ (𝕤 p) = uncurry (σ ∘ 𝕤_) p
