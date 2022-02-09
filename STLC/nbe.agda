{-# OPTIONS --prop --postfix-projections --safe #-}
module STLC.nbe where
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤)

open import STLC.Equivalence
open import STLC.STLC
open import STLC.Substitution

open WN using (nf; NF; Conv)

private variable
    α β γ : Type
    Γ Δ : Context

Red : Term Γ α -> Set
Red {α = ℕ} t = WN t
Red {Γ = Γ} {α = α ⇒ β} t = ∀ {Δ} (ρ : Renaming Γ Δ) ->
    ∀ {s} -> Red s -> Red (ren ρ t ∙ s)

-- Special status is given to renaming, because it has the good property
-- that renaming turns normal forms into normal forms.
Neutral-ren : (ρ : Renaming Γ Δ) -> Neutral t -> Neutral (ren ρ t)
Normal-ren : (ρ : Renaming Γ Δ) -> Normal t -> Normal (ren ρ t)
Neutral-ren ρ (var v) = var (ρ v)
Neutral-ren ρ (ν ∙ ν') = Neutral-ren ρ ν ∙ Normal-ren ρ ν'
Normal-ren ρ (ntr ν) = ntr (Neutral-ren ρ ν)
Normal-ren ρ (^ ν) = ^ Normal-ren (wren ρ ◃ᵣ 𝕫) ν

-- Renaming also preserves reduction.
~>-ren : (ρ : Renaming Γ Δ) -> s ~> t -> ren ρ s ~> ren ρ t
~>-ren ρ (red (β! {t = t} {s = s}))
    rewrite ren-sub ρ (𝕫:= s) t = red r!
        where
            eq : sub (𝕫:= ren ρ s) (ren (wren ρ ◃ᵣ 𝕫) t) ≡
                sub (ren ρ ∘ (𝕫:= s)) t
            eq rewrite sub-ren (𝕫:= ren ρ s) (wren ρ ◃ᵣ 𝕫) t
                = subᵉ (ren-𝕫:= ρ s) t

            r! : (^ ren (wren ρ ◃ᵣ 𝕫) t) ∙ ren ρ s ~>!
                sub (ren ρ ∘ (𝕫:= s)) t
            r! rewrite symm eq = β!

~>-ren {s = s} ρ (red (η! {α = α}))
    rewrite wren-𝕤 ρ {β = α} s = red η!
~>-ren ρ (^ r) = ^ ~>-ren (wren ρ ◃ᵣ 𝕫) r
~>-ren ρ (r ~∙ _) = ~>-ren ρ r ~∙ _
~>-ren ρ (_ ∙~ r) = _ ∙~ ~>-ren ρ r
-- Note that there are many complicated coherence lemmas for renaming
-- and substitution. For the purpose of proving normalization only, they
-- can be eschewed by replacing the Renaming in Red by a more restricted
-- form --- order preserving renaming, or Thinning.

-- In contrast to our "functional" style definition of Renaming and Substitution,
-- Thinning is best defined inductively:
--     data Thinning : Context -> Context -> Set where
--         done : Thinning ∅ ∅
--         take : Thinning Γ Δ -> Thinning (Γ ◂ α) (Δ ◂ α)
--         drop : Thinning Γ Δ -> Thinning (Γ ◂ α)  Δ
-- Exercise: Use Thinning to rewrite this file.
-- Bonus Exercise: You can make it even cleaner with a maximally
--    restricted type. Can you see how?

WN-ren : (ρ : Renaming Γ Δ) -> WN t -> WN (ren ρ t)
WN-ren ρ (wn ν R) = wn (Normal-ren ρ ν) (map (~>-ren ρ) R)

Red-≈ : {s t : Term Γ α} -> s ≈ t -> Red s -> Red t
Red-≈ {α = ℕ} R (wn ν R') = wn ν (R ⁻¹ ⁀ R')
Red-≈ {α = α ⇒ β} R F ρ G = Red-≈ (map (_~∙ _ ⊚ ~>-ren ρ) R) (F ρ G)

reify : {t : Term Γ α} -> Red t -> WN t
reflect : {t : Term Γ α} -> Neutral t -> Red t

reify {α = ℕ} F = F
reify {α = α ⇒ β} F with reify $ F 𝕤_ $ reflect (var 𝕫)
... | wn ν R = wn (^ ν) (single (red η!) ⁀ map ^_ R)

reflect {α = ℕ} ν = normal (ntr ν)
reflect {α = α ⇒ α₁} ν ρ F with reify F
... | wn ν' R' = Red-≈ (map (_ ∙~_) (R' ⁻¹)) $
    reflect $ Neutral-ren ρ ν ∙ ν'

Red-ren : (ρ : Renaming Γ Δ) {t : Term Γ α} -> Red t -> Red (ren ρ t)
Red-ren {α = ℕ} ρ F = WN-ren ρ F
Red-ren {α = α ⇒ β} ρ {t = t} F ρ' {s = s} G
    rewrite ren-ren ρ' ρ t = F (ρ' ∘ ρ) G

SubstRed : Substitution Γ Δ -> Set
SubstRed σ = ∀ {α} (v : Var _ α) -> Red (σ v)

⟦_⟧ : ∀ (t : Term Γ α) {Δ} {σ : Substitution Γ Δ}
    -> SubstRed σ -> Red (sub σ t)
⟦ var v ⟧ σ = σ v
⟦ t ∙ s ⟧ {σ = σ₀} σ
    rewrite symm $ ren-id (sub σ₀ t) = (⟦ t ⟧ σ) id (⟦ s ⟧ σ)
⟦ ^ t ⟧ {σ = σ₀} σ ρ {s = s} F = Red-≈ (red β! ⟵ refl) ans
    where
        eq' : ∀ {α} (v : Var _ α)
            -> sub (𝕫:= s)
                (ren (wren ρ ◃ᵣ 𝕫) $
                    (wsub σ₀ ◃ₛ var 𝕫) v)
            ≡ (ren ρ ∘ σ₀ ◃ₛ s) v
        eq' 𝕫 = refl
        eq' (𝕤 v)
            rewrite sub-ren (𝕫:= s) (wren ρ ◃ᵣ 𝕫) (wsub σ₀ v)
            | sub-ren (𝕫:= s ∘ (wren ρ ◃ᵣ 𝕫)) 𝕤_ (σ₀ v)
            | symm (sub-ren var ρ (σ₀ v))
            = sub-var _

        eq : (sub (𝕫:= s) $ ren (wren ρ ◃ᵣ 𝕫) $ sub (wsub σ₀ ◃ₛ var 𝕫) t)
            ≡ sub (ren ρ ∘ σ₀ ◃ₛ s) t
        eq rewrite ren-sub (wren ρ ◃ᵣ 𝕫) (wsub σ₀ ◃ₛ var 𝕫) t
            | sub-sub (𝕫:= s) (ren (wren ρ ◃ᵣ 𝕫) ∘ (wsub σ₀ ◃ₛ var 𝕫)) t
            = subᵉ eq' t

        expr : Red (sub (ren ρ ∘ σ₀ ◃ₛ s) t)
        expr = ⟦ t ⟧ λ
            { 𝕫     -> F
            ; (𝕤 v) -> Red-ren ρ (σ v) }

        ans : Red (sub (var ◃ₛ s) $ ren (wren ρ ◃ᵣ 𝕫) $ sub (wsub σ₀ ◃ₛ var 𝕫) t)
        ans rewrite eq = expr

Red-id : SubstRed {Γ = Γ} var
Red-id v = reflect (var v)

normalize : Term Γ α -> Term Γ α
normalize t = reify (⟦ t ⟧ Red-id) .nf

open benchmark

nbe-eta = normalize bench-eta
nbe-beta = normalize bench-beta  -- ^ ^ var 𝕫
nbe-both = normalize bench-both  -- ^ ^ ^ var (𝕤 𝕤 𝕫) ∙ var (𝕤 𝕫) ∙ var 𝕫
-- Normalize them to see the result!
