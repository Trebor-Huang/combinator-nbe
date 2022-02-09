{-# OPTIONS --prop --postfix-projections --safe #-}
module STLC.substitution where
open import Agda.Builtin.Equality using (_≡_; refl)

open import STLC.Equivalence
open import STLC.stlc

open import Agda.Builtin.Equality.Erase

private variable
    α β γ : Type
    Γ Δ Ξ : Context

private
    ren-id-auxᵉ : {f : Renaming Γ Γ} (eq : ∀ {α} (v : Var Γ α) -> f v ≡ v)
        -> ∀ {β α} (v : Var (Γ ◂ β) α) -> (wren f ◃ᵣ 𝕫) v ≡ v
    ren-id-auxᵉ eq 𝕫 = refl
    ren-id-auxᵉ eq (𝕤 v) rewrite eq v = refl

    ren-idᵉ : {f : Renaming Γ Γ} (eq : ∀ {α} (v : Var Γ α) -> f v ≡ v) (t : Term Γ α)
        -> ren f t ≡ t
    ren-idᵉ eq (var v) rewrite eq v = refl
    ren-idᵉ eq (^ t)
        rewrite ren-idᵉ (ren-id-auxᵉ eq) t = refl
    ren-idᵉ eq (t ∙ s) rewrite ren-idᵉ eq t | ren-idᵉ eq s = refl

ren-id : (t : Term Γ α) -> ren id t ≡ t
ren-id t = primEraseEquality (ren-idᵉ (λ _ -> refl) t)

private
    wren-comp-auxᵉ : (σ : Renaming Δ Ξ) (τ : Renaming Γ Δ) (σ∘τ : Renaming Γ Ξ)
        -> (∀ {α} (v : Var Γ α) -> σ (τ v) ≡ σ∘τ v)
        -> ∀ {β α} (v : Var (Γ ◂ β) α)
        -> (wren σ ◃ᵣ 𝕫) ((wren τ ◃ᵣ 𝕫) v) ≡ (wren σ∘τ ◃ᵣ 𝕫) v
    wren-comp-auxᵉ σ τ σ∘τ eq 𝕫 = refl
    wren-comp-auxᵉ σ τ σ∘τ eq (𝕤 v) rewrite eq v = refl

    ren-compᵉ : (σ : Renaming Δ Ξ) (τ : Renaming Γ Δ) (σ∘τ : Renaming Γ Ξ)
        -> (∀ {α} (v : Var Γ α) -> σ (τ v) ≡ σ∘τ v)
        -> (t : Term Γ α) -> ren σ (ren τ t) ≡ ren σ∘τ t
    ren-compᵉ σ τ σ∘τ eq (var v) rewrite eq v = refl
    ren-compᵉ σ τ σ∘τ eq (^ t)
        rewrite ren-compᵉ (wren σ ◃ᵣ 𝕫) (wren τ ◃ᵣ 𝕫) _
            (wren-comp-auxᵉ σ τ σ∘τ eq) t = refl
    ren-compᵉ σ τ σ∘τ eq (t ∙ s)
        rewrite ren-compᵉ σ τ σ∘τ eq t | ren-compᵉ σ τ σ∘τ eq s = refl

ren-comp : (σ : Renaming Δ Ξ) (τ : Renaming Γ Δ) (t : Term Γ α)
    -> ren σ (ren τ t) ≡ ren (σ ∘ τ) t
ren-comp σ τ t = primEraseEquality (ren-compᵉ σ τ (σ ∘ τ) (λ _ -> refl) t)

private
    wren-𝕤-aux : ∀ (ρ : Renaming Γ Δ) {α β} (s : Term Γ α)
        -> ren (wren ρ ◃ᵣ 𝕫) (ren 𝕤_ s) ≡ ren (𝕤_ {β = β}) (ren ρ s)
    wren-𝕤-aux ρ {β = β} s
        rewrite ren-comp (wren ρ ◃ᵣ 𝕫) (𝕤_ {β = β}) s
        | ren-comp (𝕤_ {β = β}) ρ s = refl

wren-𝕤 : ∀ (ρ : Renaming Γ Δ) {α β} (s : Term Γ α)
    -> ren (wren ρ ◃ᵣ 𝕫) (ren 𝕤_ s) ≡ ren (𝕤_ {β = β}) (ren ρ s)
wren-𝕤 ρ s = primEraseEquality (wren-𝕤-aux ρ s)

private
    ren-sub-auxᵉ : ∀ (ρ : Renaming Δ Ξ) (σ : Substitution Γ Δ)
        (renρ∘σ : Substitution Γ Ξ)
        (eq : ∀ {α} (v : Var Γ α) -> ren ρ (σ v) ≡ renρ∘σ v)
        {α β} (v : Var (Γ ◂ α) β)
        -> ren (wren ρ ◃ᵣ 𝕫) ((wsub σ ◃ₛ var 𝕫) v) ≡
            (wsub renρ∘σ ◃ₛ var 𝕫) v
    ren-sub-auxᵉ ρ σ renρ∘σ eq 𝕫 = refl
    ren-sub-auxᵉ ρ σ renρ∘σ eq {α = α} (𝕤 v)
        rewrite wren-𝕤 ρ {β = α} (σ v) | eq v = refl

    ren-subᵉ : (ρ : Renaming Δ Ξ) (σ : Substitution Γ Δ)
        -> (renρ∘σ : Substitution Γ Ξ)
        -> (eq : ∀ {α} (v : Var Γ α) -> ren ρ (σ v) ≡ renρ∘σ v)
        -> (t : Term Γ α)
        -> ren ρ (sub σ t) ≡ sub renρ∘σ t
    ren-subᵉ ρ σ renρ∘σ eq (var v) = eq v
    ren-subᵉ ρ σ renρ∘σ eq (^ t)
        rewrite ren-subᵉ
            (wren ρ ◃ᵣ 𝕫)
            (wsub σ ◃ₛ var 𝕫)
            (wsub renρ∘σ ◃ₛ var 𝕫)
            (ren-sub-auxᵉ ρ σ renρ∘σ eq) t
            = refl
    ren-subᵉ ρ σ renρ∘σ eq (t ∙ s)
        rewrite ren-subᵉ ρ σ renρ∘σ eq t
        | ren-subᵉ ρ σ renρ∘σ eq s = refl

ren-sub : (ρ : Renaming Δ Ξ) (σ : Substitution Γ Δ) (t : Term Γ α)
    -> ren ρ (sub σ t) ≡ sub (ren ρ ∘ σ) t
ren-sub ρ σ t = primEraseEquality (ren-subᵉ ρ σ (ren ρ ∘ σ) (λ _ -> refl) t)

private
    sub-ren-auxᵉ : (σ : Substitution Δ Ξ) (ρ : Renaming Γ Δ)
        -> (σ∘ρ : Substitution Γ Ξ)
        -> (eq : ∀ {α} (v : Var Γ α) -> σ (ρ v) ≡ σ∘ρ v)
        -> ∀ {α β} (v : Var (Γ ◂ α) β)
        -> (wsub σ ◃ₛ var 𝕫) ((wren ρ ◃ᵣ 𝕫) v) ≡ (wsub σ∘ρ ◃ₛ var 𝕫) v
    sub-ren-auxᵉ σ ρ σ∘ρ eq 𝕫 = refl
    sub-ren-auxᵉ σ ρ σ∘ρ eq (𝕤 v) rewrite eq v = refl

    sub-renᵉ : (σ : Substitution Δ Ξ) (ρ : Renaming Γ Δ)
        -> (σ∘ρ : Substitution Γ Ξ)
        -> (eq : ∀ {α} (v : Var Γ α) -> σ (ρ v) ≡ σ∘ρ v)
        -> (t : Term Γ α)
        -> sub σ (ren ρ t) ≡ sub σ∘ρ t
    sub-renᵉ σ ρ σ∘ρ eq (var v) = eq v
    sub-renᵉ σ ρ σ∘ρ eq (^ t)
        rewrite sub-renᵉ
            (wsub σ ◃ₛ var 𝕫)
            (wren ρ ◃ᵣ 𝕫)
            (wsub σ∘ρ ◃ₛ var 𝕫)
            (sub-ren-auxᵉ σ ρ σ∘ρ eq) t
            = refl
    sub-renᵉ σ ρ σ∘ρ eq (t ∙ s)
        rewrite sub-renᵉ σ ρ σ∘ρ eq t
        | sub-renᵉ σ ρ σ∘ρ eq s = refl

sub-ren : (σ : Substitution Δ Ξ) (ρ : Renaming Γ Δ)
    -> (t : Term Γ α)
    -> sub σ (ren ρ t) ≡ sub (σ ∘ ρ) t
sub-ren σ ρ t = primEraseEquality (sub-renᵉ σ ρ (σ ∘ ρ) (λ _ -> refl) t)

-- 𝕫:= ren ρ s ∘ (wren ρ ◃ᵣ 𝕫) ≡ ren ρ ∘ (var ◃ₛ s)
