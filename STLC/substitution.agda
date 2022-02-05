{-# OPTIONS --prop --postfix-projections #-}
module STLC.substitution where
open import Agda.Builtin.Equality using (_≡_; refl)

open import STLC.Equivalence
open import STLC.stlc

open import Agda.Builtin.Equality.Erase
open import Agda.Builtin.TrustMe

private variable
    α β γ : Type
    Γ Δ Ξ : Context

private
    wren-idᵉ-◃ᵣ-𝕫 : {f : Renaming Γ Γ} (eq : ∀ {α} (v : Var Γ α) -> f v ≡ v)
        -> ∀ {β α} (v : Var (Γ ◂ β) α) -> (wren f ◃ᵣ 𝕫) v ≡ v
    wren-idᵉ-◃ᵣ-𝕫 eq 𝕫 = refl
    wren-idᵉ-◃ᵣ-𝕫 eq (𝕤 v) rewrite eq v = refl

    ren-idᵉ : {f : Renaming Γ Γ} (eq : ∀ {α} (v : Var Γ α) -> f v ≡ v) (t : Term Γ α)
        -> ren f t ≡ t
    ren-idᵉ eq (var v) rewrite eq v = refl
    ren-idᵉ eq (^ t)
        rewrite ren-idᵉ (wren-idᵉ-◃ᵣ-𝕫 eq) t = refl
    ren-idᵉ eq (t ∙ s) rewrite ren-idᵉ eq t | ren-idᵉ eq s = refl

ren-id : (t : Term Γ α) -> ren id t ≡ t
ren-id t = primEraseEquality (ren-idᵉ (λ _ -> refl) t)

private
    wren-compᵉ-◃ᵣ-𝕫 : (σ : Renaming Δ Ξ) (τ : Renaming Γ Δ) (σ∘τ : Renaming Γ Ξ)
        -> (∀ {α} (v : Var Γ α) -> σ (τ v) ≡ σ∘τ v)
        -> ∀ {β α} (v : Var (Γ ◂ β) α)
        -> (wren σ ◃ᵣ 𝕫) ((wren τ ◃ᵣ 𝕫) v) ≡ (wren σ∘τ ◃ᵣ 𝕫) v
    wren-compᵉ-◃ᵣ-𝕫 σ τ σ∘τ eq 𝕫 = refl
    wren-compᵉ-◃ᵣ-𝕫 σ τ σ∘τ eq (𝕤 v) rewrite eq v = refl

    ren-compᵉ : (σ : Renaming Δ Ξ) (τ : Renaming Γ Δ) (σ∘τ : Renaming Γ Ξ)
        -> (∀ {α} (v : Var Γ α) -> σ (τ v) ≡ σ∘τ v)
        -> (t : Term Γ α) -> ren σ (ren τ t) ≡ ren σ∘τ t
    ren-compᵉ σ τ σ∘τ eq (var v) rewrite eq v = refl
    ren-compᵉ σ τ σ∘τ eq (^ t)
        rewrite ren-compᵉ (wren σ ◃ᵣ 𝕫) (wren τ ◃ᵣ 𝕫) _
            (wren-compᵉ-◃ᵣ-𝕫 σ τ σ∘τ eq) t = refl
    ren-compᵉ σ τ σ∘τ eq (t ∙ s)
        rewrite ren-compᵉ σ τ σ∘τ eq t | ren-compᵉ σ τ σ∘τ eq s = refl

ren-comp : (σ : Renaming Δ Ξ) (τ : Renaming Γ Δ) (t : Term Γ α)
    -> ren σ (ren τ t) ≡ ren (σ ∘ τ) t
ren-comp σ τ t = primEraseEquality (ren-compᵉ σ τ (σ ∘ τ) (λ _ -> refl) t)


