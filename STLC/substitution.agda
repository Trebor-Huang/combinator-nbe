{-# OPTIONS --prop --postfix-projections --safe #-}
module STLC.Substitution where
open import Agda.Builtin.Equality using (_≡_; refl)

open import STLC.Equivalence
open import STLC.STLC

-- open import Agda.Builtin.Equality.Erase

primEraseEquality : {A : Set} -> A -> A
primEraseEquality a = a

private variable
    α β γ : Type
    Γ Δ Ξ : Context

private
    ren-auxᵉ : {ρ ρ' : Renaming Γ Δ}
        -> (eq : ∀ {α} (v : Var Γ α) -> ρ v ≡ ρ' v)
        -> ∀ {α} (v : Var (Γ ◂ β) α)
        -> (wren ρ ◃ᵣ 𝕫) v ≡ (wren ρ' ◃ᵣ 𝕫) v
    ren-auxᵉ eq 𝕫 = refl
    ren-auxᵉ eq (𝕤 v) rewrite eq v = refl

renᵉ : {ρ ρ' : Renaming Γ Δ}
    -> (eq : ∀ {α} (v : Var Γ α) -> ρ v ≡ ρ' v)
    -> ∀ {α} (t : Term Γ α) -> ren ρ t ≡ ren ρ' t
renᵉ eq (var v) rewrite eq v = refl
renᵉ eq (^ t) rewrite renᵉ (ren-auxᵉ eq) t = refl
renᵉ eq (t ∙ s) rewrite renᵉ eq t | renᵉ eq s = refl

private
    sub-auxᵉ : {σ σ' : Substitution Γ Δ}
        -> (eq : ∀ {α} (v : Var Γ α) -> σ v ≡ σ' v)
        -> ∀ {α} (v : Var (Γ ◂ β) α)
        -> (wsub σ ◃ₛ var 𝕫) v ≡ (wsub σ' ◃ₛ var 𝕫) v
    sub-auxᵉ eq 𝕫 = refl
    sub-auxᵉ eq (𝕤 v) rewrite eq v = refl

subᵉ : {σ σ' : Substitution Γ Δ}
    -> (eq : ∀ {α} (v : Var Γ α) -> σ v ≡ σ' v)
    -> ∀ {α} (t : Term Γ α) -> sub σ t ≡ sub σ' t
subᵉ eq (var v) = eq v
subᵉ eq (^ t) rewrite subᵉ (sub-auxᵉ eq) t = refl
subᵉ eq (t ∙ s) rewrite subᵉ eq t | subᵉ eq s = refl

private
    ren-id-auxᵉ : {ρ : Renaming Γ Γ} (eq : ∀ {α} (v : Var Γ α) -> ρ v ≡ v)
        -> ∀ {β α} (v : Var (Γ ◂ β) α) -> (wren ρ ◃ᵣ 𝕫) v ≡ v
    ren-id-auxᵉ eq 𝕫 = refl
    ren-id-auxᵉ eq (𝕤 v) rewrite eq v = refl

    ren-idᵉ : {ρ : Renaming Γ Γ} (eq : ∀ {α} (v : Var Γ α) -> ρ v ≡ v) (t : Term Γ α)
        -> ren ρ t ≡ t
    ren-idᵉ eq (var v) rewrite eq v = refl
    ren-idᵉ eq (^ t)
        rewrite ren-idᵉ (ren-id-auxᵉ eq) t = refl
    ren-idᵉ eq (t ∙ s) rewrite ren-idᵉ eq t | ren-idᵉ eq s = refl

ren-id : (t : Term Γ α) -> ren id t ≡ t
ren-id t = primEraseEquality (ren-idᵉ (λ _ -> refl) t)

private
    sub-var-auxᵉ : {σ : Substitution Γ Γ} (eq : ∀ {α} (v : Var Γ α) -> σ v ≡ var v)
        -> ∀ {β α} (v : Var (Γ ◂ β) α) -> (wsub σ ◃ₛ var 𝕫) v ≡ var v
    sub-var-auxᵉ eq 𝕫 = refl
    sub-var-auxᵉ eq (𝕤 v) rewrite eq v = refl

    sub-varᵉ : {σ : Substitution Γ Γ} (eq : ∀ {α} (v : Var Γ α) -> σ v ≡ var v) (t : Term Γ α)
        -> sub σ t ≡ t
    sub-varᵉ eq (var v) rewrite eq v = refl
    sub-varᵉ eq (^ t)
        rewrite sub-varᵉ (sub-var-auxᵉ eq) t = refl
    sub-varᵉ eq (t ∙ s) rewrite sub-varᵉ eq t | sub-varᵉ eq s = refl

sub-var : (t : Term Γ α) -> sub var t ≡ t
sub-var t = primEraseEquality (sub-varᵉ (λ _ -> refl) t)

private
    wren-ren-auxᵉ : (σ : Renaming Δ Ξ) (τ : Renaming Γ Δ) (σ∘τ : Renaming Γ Ξ)
        -> (∀ {α} (v : Var Γ α) -> σ (τ v) ≡ σ∘τ v)
        -> ∀ {β α} (v : Var (Γ ◂ β) α)
        -> (wren σ ◃ᵣ 𝕫) ((wren τ ◃ᵣ 𝕫) v) ≡ (wren σ∘τ ◃ᵣ 𝕫) v
    wren-ren-auxᵉ σ τ σ∘τ eq 𝕫 = refl
    wren-ren-auxᵉ σ τ σ∘τ eq (𝕤 v) rewrite eq v = refl

    ren-renᵉ : (σ : Renaming Δ Ξ) (τ : Renaming Γ Δ) (σ∘τ : Renaming Γ Ξ)
        -> (∀ {α} (v : Var Γ α) -> σ (τ v) ≡ σ∘τ v)
        -> (t : Term Γ α) -> ren σ (ren τ t) ≡ ren σ∘τ t
    ren-renᵉ σ τ σ∘τ eq (var v) rewrite eq v = refl
    ren-renᵉ σ τ σ∘τ eq (^ t)
        rewrite ren-renᵉ (wren σ ◃ᵣ 𝕫) (wren τ ◃ᵣ 𝕫) _
            (wren-ren-auxᵉ σ τ σ∘τ eq) t = refl
    ren-renᵉ σ τ σ∘τ eq (t ∙ s)
        rewrite ren-renᵉ σ τ σ∘τ eq t | ren-renᵉ σ τ σ∘τ eq s = refl

ren-ren : (σ : Renaming Δ Ξ) (τ : Renaming Γ Δ) (t : Term Γ α)
    -> ren σ (ren τ t) ≡ ren (σ ∘ τ) t
ren-ren σ τ t = primEraseEquality (ren-renᵉ σ τ (σ ∘ τ) (λ _ -> refl) t)

private
    wren-𝕤-aux : ∀ (ρ : Renaming Γ Δ) {α β} (s : Term Γ α)
        -> ren (wren ρ ◃ᵣ 𝕫) (ren 𝕤_ s) ≡ ren (𝕤_ {β = β}) (ren ρ s)
    wren-𝕤-aux ρ {β = β} s
        rewrite ren-ren (wren ρ ◃ᵣ 𝕫) (𝕤_ {β = β}) s
        | ren-ren (𝕤_ {β = β}) ρ s = refl

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

ren-𝕫:= : (ρ : Renaming Γ Δ) (s : Term Γ α) (v : Var (Γ ◂ α) β)
    -> (𝕫:= ren ρ s) ((wren ρ ◃ᵣ 𝕫) v) ≡ ren ρ ((𝕫:= s) v)
ren-𝕫:= ρ s 𝕫 = refl
ren-𝕫:= ρ s (𝕤 v) = refl

private
    sub-sub-auxᵉ : ∀ (τ : Substitution Δ Ξ) (σ : Substitution Γ Δ)
        (subτ∘σ : Substitution Γ Ξ)
        (eq : ∀ {α} (v : Var Γ α) -> sub τ (σ v) ≡ subτ∘σ v)
        {α β} (v : Var (Γ ◂ α) β)
        -> sub (wsub τ ◃ₛ var 𝕫) ((wsub σ ◃ₛ var 𝕫) v) ≡
            (wsub subτ∘σ ◃ₛ var 𝕫) v
    sub-sub-auxᵉ τ σ subτ∘σ eq 𝕫 = refl
    sub-sub-auxᵉ τ σ subτ∘σ eq {α} {β} (𝕤 v)
        rewrite symm (eq v) 
        | sub-ren (wsub τ ◃ₛ var (𝕫 {α = α})) 𝕤_ (σ v)
        | ren-sub (𝕤_ {β = α}) τ (σ v) = refl

    sub-subᵉ : (τ : Substitution Δ Ξ) (σ : Substitution Γ Δ)
        -> (subτ∘σ : Substitution Γ Ξ)
        -> (eq : ∀ {α} (v : Var Γ α) -> sub τ (σ v) ≡ subτ∘σ v)
        -> (t : Term Γ α)
        -> sub τ (sub σ t) ≡ sub subτ∘σ t
    sub-subᵉ τ σ subτ∘σ eq (var v) = eq v
    sub-subᵉ τ σ subτ∘σ eq (^ t)
        rewrite sub-subᵉ
            (wsub τ ◃ₛ var 𝕫)
            (wsub σ ◃ₛ var 𝕫)
            (wsub subτ∘σ ◃ₛ var 𝕫)
            (sub-sub-auxᵉ τ σ subτ∘σ eq) t
            = refl
    sub-subᵉ τ σ subτ∘σ eq (t ∙ s)
        rewrite sub-subᵉ τ σ subτ∘σ eq t
        | sub-subᵉ τ σ subτ∘σ eq s = refl

sub-sub : (τ : Substitution Δ Ξ) (σ : Substitution Γ Δ) (t : Term Γ α)
    -> sub τ (sub σ t) ≡ sub (sub τ ∘ σ) t
sub-sub τ σ t = primEraseEquality (sub-subᵉ τ σ (sub τ ∘ σ) (λ _ -> refl) t)
