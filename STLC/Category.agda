{-# OPTIONS --prop --postfix-projections --safe #-}
module STLC.Category where
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
_==_ : Mor Γ Δ -> Mor Γ Δ -> Prop
σ == τ = ∀ {α} {v : Var _ α} -> σ v ≈ τ v
infix 3 _==_

idₗ : compMor idMor σ == σ
idₗ = refl

idᵣ : compMor σ idMor == σ
idᵣ {σ = σ} {v = v} rewrite sub-var (σ v) = refl

assoc : compMor (compMor σ₁ σ₂) σ₃ == compMor σ₁ (compMor σ₂ σ₃)
assoc {σ₁ = σ₁} {σ₂ = σ₂} {σ₃ = σ₃} {v = v}
    rewrite sub-sub σ₃ σ₂ (σ₁ v) = refl

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
π₁ {Δ = Δ} x = var (p₁ {Δ = Δ} x)

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

private
    abs : Term (Δ × Γ) α -> Term Δ (Telescope Γ α)
    abs {Γ = ∅} t = t
    abs {Γ = Γ ◂ _} t = ^ abs t

    app : Term Δ (Telescope Γ α) -> Term (Δ × Γ) α
    app {Γ = ∅} t = t
    app {Γ = Γ ◂ _} t = app {Γ = Γ} (ren 𝕤_ t ∙ var 𝕫)

Hom : Obj -> Obj -> Obj
Hom Γ ∅ = ∅
Hom Γ (Δ ◂ α) = Hom Γ Δ ◂ Telescope Γ α

uncurry : Mor Γ (Hom Ξ Δ) -> Mor (Γ × Ξ) Δ
uncurry σ 𝕫 = app (σ 𝕫)
uncurry σ (𝕤 v) = uncurry (σ ∘ 𝕤_) v

curry : Mor (Γ × Ξ) Δ -> Mor Γ (Hom Ξ Δ)
curry {Δ = Δ ◂ _} σ 𝕫 = abs (σ 𝕫)
curry {Δ = Δ ◂ _} σ (𝕤 v) = curry (σ ∘ 𝕤_) v
