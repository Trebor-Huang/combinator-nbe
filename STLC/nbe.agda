{-# OPTIONS --prop --postfix-projections --safe #-}
module STLC.NbE where
open import Agda.Builtin.Nat
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤)

open import STLC.Equivalence
open import STLC.STLC
open import STLC.Substitution

open import Relation.Binary.PropositionalEquality
open ≡-Reasoning
open import Tactic.Cong

open WN using (nf; NF; Conv)

private variable
    α β γ : Type
    Γ Δ : Context

-- Similar to our combinators, we define a reducible predicate.
-- Unlike combinators which has no contexts, we introduce an
-- additional Renaming argument in the function space.
-- This is because when reifying, when we encounter a λ, we need
-- to snuck in a fresh variable. The Renaming gives us the elbow-
-- room to do this. (Exercise: Try defining Red without the
-- Renaming, and describe the difficulties you meet.)
-- This is in the spirit of Kripke-models, where we have many "worlds"
-- with an accessibility relation (w ≫ w'). A proposition is interpreted
-- at a specific world (w ⊢ p). The intuitionistic implication
-- (w ⊢ p → q) is interpreted as
--     ∀ w' -> w ≫ w' -> w' ⊢ p → q
-- This makes the model much more suitable for proving metatheorems.
Red : Term Γ α -> Set
Red {α = ℕ} t = WN t
Red {α = α ⇒ β} t = ∀ {Δ} (ρ : Renaming _ Δ) ->
    ∀ {s} -> Red s -> Red (ren ρ t ∙ s)

-- Special status is given to renaming, because it has the good property
-- that renaming turns normal forms into normal forms.
Neutral-ren : (ρ : Renaming Γ Δ) -> Neutral t -> Neutral (ren ρ t)
Normal-ren : (ρ : Renaming Γ Δ) -> Normal t -> Normal (ren ρ t)
Neutral-ren ρ (var v) = var (ρ v)
Neutral-ren ρ (ν ∙ ν') = Neutral-ren ρ ν ∙ Normal-ren ρ ν'
Neutral-ren ρ (Rec ν₁ ν₂ ν₃)
    = Rec (Normal-ren ρ ν₁) (Normal-ren ρ ν₂) (Neutral-ren ρ ν₃)
Normal-ren ρ (ntr ν) = ntr (Neutral-ren ρ ν)
Normal-ren ρ (^ ν) = ^ Normal-ren (wren ρ ◃ᵣ 𝕫) ν
Normal-ren ρ O = O
Normal-ren ρ (S ν) = S (Normal-ren ρ ν)

-- Renaming also preserves reduction.
~>-ren : (ρ : Renaming Γ Δ) -> s ~> t -> ren ρ s ~> ren ρ t
~>-ren ρ (red (β! {t = t} {s = s})) = R
    where
        eq : _
        eq =
            begin
                ren ρ (sub (𝕫:= s) t)
            ≡⟨ ren-sub _ _ t ⟩
                sub (ren ρ ∘ (𝕫:= s)) t
            ≡˘⟨ subᵉ (ren-𝕫:= ρ s) t ⟩
                sub ((var ◃ₛ ren ρ s) ∘ (wren ρ ◃ᵣ 𝕫)) t
            ≡˘⟨ sub-ren _ _ t ⟩
                sub (𝕫:= ren ρ s) (ren (wren ρ ◃ᵣ 𝕫) t)
            ∎

        R : ren ρ ((^ t) ∙ s) ~> ren ρ (sub (𝕫:= s) t)
        R rewrite eq = red β!

~>-ren {s = s} ρ (red (η! {α = α})) = R
    where
        eq : _
        eq =
            begin
                ren (wren ρ ◃ᵣ 𝕫) (ren 𝕤_ s)
            ≡⟨ ren-ren _ _ s ⟩
                ren (𝕤_ ∘ ρ) s
            ≡˘⟨ ren-ren _ _ s ⟩
                ren (𝕤_ {β = α}) (ren ρ s)
            ∎

        R : ren ρ s ~> ^ ren (wren ρ ◃ᵣ 𝕫) (ren 𝕤_ s) ∙ var 𝕫
        R rewrite eq = red η!

-- These two are much easier because no binding is involved.
~>-ren ρ (red ιₒ!) = red ιₒ!
~>-ren ρ (red ιₛ!) = red ιₛ!

-- These are just congruence closures.
~>-ren ρ (^ r) = ^ ~>-ren (wren ρ ◃ᵣ 𝕫) r
~>-ren ρ (r ~∙ _) = ~>-ren ρ r ~∙ _
~>-ren ρ (_ ∙~ r) = _ ∙~ ~>-ren ρ r

WN-ren : (ρ : Renaming Γ Δ) -> WN t -> WN (ren ρ t)
WN-ren ρ (wn ν R) = wn (Normal-ren ρ ν) (map (~>-ren ρ) R)

Red-ren : (ρ : Renaming Γ Δ) {t : Term Γ α} -> Red t -> Red (ren ρ t)
Red-ren {α = ℕ} ρ F = WN-ren ρ F
Red-ren {α = α ⇒ β} ρ {t = t} F ρ' {s = s} G
    rewrite ren-ren ρ' ρ t = F (ρ' ∘ ρ) G

-- Similar to the combinator case, Reducibility is preserved
-- by reductions.
Red-≈ : {s t : Term Γ α} -> s ≈ t -> Red s -> Red t
Red-≈ {α = ℕ} R (wn ν R') = wn ν (R ⁻¹ ⁀ R')
Red-≈ {α = α ⇒ β} R F ρ G = Red-≈ (map (_~∙ _ ⊚ ~>-ren ρ) R) (F ρ G)

-- Now we have set up everything needed. Let's look at the big picture.

-- We assigned "meaning" to our terms with Red.

--   ⟦_⟧======>  Red  <-----reflect
--   ||           |            |
--   ||         reify          |
--   ||           |            |
--   ||           ↓            |
--  Term   ⊇   Normal‡   ⊇   Neutral   ⊇   Var

-- ‡ Actually we use WN instead of Normal, to keep track of
-- the normalization path. So you may regard this as an extra middle layer.

-- We first define a reify function to extract the normal form
-- from the Red semantics. But during this stage, when dealing with
-- terms of type (α ⇒ β), we have (Red t) which takes any reducible
-- (Red s) to (Red (t ∙ s)) modulo a renaming. So we should apply
-- (Red (var 𝕫)) to get (Red (t ∙ var 𝕫)), and then we can happily
-- abstract the normal form with a λ. However, the term t is in context
-- Γ, while we need to lift it to (Γ ◂ α) so that (var 𝕫) is a valid
-- term. This is how the "elbow-room" we previously left helps.

-- Also, although it may seem trivial to just apply (var 𝕫), it is not
-- immediate that we have (Red (var 𝕫)) because (var 𝕫) is not
-- necessarily normal! We might have to η-expand it. This gives rise
-- to another function called "reflect", which is weaker because
-- it only needs to deal with Neutral terms.
-- (You might be tempted to say that you only need to deal with Var,
-- which is even simpler. But unfortunately after an η-expansion,
-- you will have to deal with function applications.)

reify : {t : Term Γ α} -> Red t -> WN t
reflect : {t : Term Γ α} -> Neutral t -> Red t

reify {α = ℕ} F = F
reify {α = α ⇒ β} F with reify $ F 𝕤_ $ reflect (var 𝕫)
... | wn ν R = wn (^ ν) (single (red η!) ⁀ map ^_ R)
-- If you get rid of the theorem proving part, it simply
-- turns (wn ν _) into (wn (^ ν) _). Here (wn ν _) comes
-- from applying (var 𝕫) to F, with the lifting 𝕤_.

reflect {α = ℕ} ν = normal (ntr ν)
reflect {α = α ⇒ β} ν ρ F with reify F
... | wn ν' R' = Red-≈ (map (_ ∙~_) (R' ⁻¹)) $
    reflect $ Neutral-ren ρ ν ∙ ν'

-- To make the induction go through, we have to additionally carry
-- a substitution around. This substitution acts as the "environment"
-- during the reduction. In other words, when we are reducing an
-- application (λ x . t) s, we add (x <- s) to the environment, and go
-- inside t to continue reducing.

-- For this purpose, we need a Red predicate on substitutions.
SubstRed : Substitution Γ Δ -> Set
SubstRed σ = ∀ {α} (v : Var _ α) -> Red (σ v)

-- To start a reduction, we supply the identity environment.
Red-id : SubstRed {Γ = Γ} var
Red-id v = reflect (var v)

-- Now the final induction.
⟦_⟧ : ∀ (t : Term Γ α) {Δ} {σ : Substitution Γ Δ}
    -> SubstRed σ -> Red (sub σ t)
⟦ t ∙ s ⟧ σ = subst (λ ⋆ -> Red (⋆ ∙ _)) (ren-id _) $
    (⟦ t ⟧ σ) id (⟦ s ⟧ σ)
⟦ var v ⟧ σ = σ v
⟦ O ⟧ σ = normal O
⟦ S ⟧ σ ρ (wn ν R) = wn (S ν) (map (_ ∙~_) R)
⟦ Rec ⟧ σ ρ₁ {s₁} F₁ ρ₂ {s₂} F₂ ρ₃ {s₃} w₃@(wn ν R)
    with reify F₁ | reify {t = s₂} F₂
    -- Agda inserts implicit arguments too early, so I have to mark this.
... | w₁@(wn ν₁ R₁) | w₂@(wn ν₂ R₂) = ⟦Rec⟧ ν R
    where
        ⟦Rec⟧ : {s s' : Term _ ℕ} (ν : Normal s') (R : s ≈ s')
            -> Red (Rec ∙ ren ρ₃ (ren ρ₂ s₁) ∙ ren ρ₃ s₂ ∙ s)
        ⟦Rec⟧ (ntr ν) R = Red-≈  -- We first reduce the corresponding components.
            -- Then we piece the reductions together.
            ( map (_~∙ _ ⊚ _~∙ _ ⊚ _ ∙~_ ⊚ ~>-ren ρ₃ ⊚ ~>-ren ρ₂) (R₁ ⁻¹)
            ⁀ map (_~∙ _ ⊚ _ ∙~_ ⊚ ~>-ren ρ₃) (R₂ ⁻¹)
            ⁀ map (_ ∙~_) (R ⁻¹)) $ reflect $  -- And use reflect on the final neutral form.
            Rec (Normal-ren ρ₃ (Normal-ren ρ₂ ν₁)) (Normal-ren ρ₃ ν₂) ν
        ⟦Rec⟧ {s' = (S ∙ s₀)} (S ν) R = Red-≈ (red ιₛ! ⟵ map (_ ∙~_) (R ⁻¹)) ⟦Rec⟧S
            where
                eq : (Term _ _ ∋ ren ρ₃ s₂ ∙ s₀) ≡ ren id (ren ρ₃ s₂) ∙ ren id s₀
                eq rewrite ren-id s₀ | ren-id (ren ρ₃ s₂) = refl

                ⟦Rec⟧S : Red (ren ρ₃ s₂ ∙ s₀ ∙
                    (Rec ∙ ren ρ₃ (ren ρ₂ s₁) ∙ ren ρ₃ s₂ ∙ s₀))
                ⟦Rec⟧S rewrite eq = F₂ ρ₃ (wn ν refl) id (⟦Rec⟧ ν refl)

        ⟦Rec⟧ O R = Red-≈ (red ιₒ! ⟵ map (_ ∙~_) (R ⁻¹))
            (Red-ren ρ₃ (Red-ren ρ₂ F₁))

⟦ ^ t ⟧ {σ = σ₀} σ ρ {s = s} F = Red-≈ (red β! ⟵ refl) G
    where
        eqᵉ : (v : Var _ α)
            -> (sub (𝕫:= s) ∘ ren (wren ρ ◃ᵣ 𝕫) ∘ (wsub σ₀ ◃ₛ var 𝕫)) v
                ≡ (ren ρ ∘ σ₀ ◃ₛ s) v
        eqᵉ 𝕫 = refl
        eqᵉ (𝕤 v) =
            begin
                sub (𝕫:= s) (ren (wren ρ ◃ᵣ 𝕫) (wsub σ₀ v))
            ≡⟨ sub-ren _ _ (wsub σ₀ v) ⟩
                sub (𝕫:= s ∘ (wren ρ ◃ᵣ 𝕫)) (wsub σ₀ v)
            ≡⟨ sub-ren _ _ (σ₀ v) ⟩
                sub (var ∘ ρ) (σ₀ v)
            ≡˘⟨ sub-ren _ _ (σ₀ v) ⟩
                sub var (ren ρ (σ₀ v))
            ≡⟨ sub-var _ ⟩
                ren ρ (σ₀ v)
            ∎

        eq : _
        eq =
            begin
                (sub (𝕫:= s) $ ren (wren ρ ◃ᵣ 𝕫) $ sub (wsub σ₀ ◃ₛ var 𝕫) t)
            ≡⟨ cong! (ren-sub _ _ t) ⟩
                sub (𝕫:= s) (sub (ren (wren ρ ◃ᵣ 𝕫) ∘ (wsub σ₀ ◃ₛ var 𝕫)) t)
            ≡⟨ sub-sub _ _ t ⟩
                sub (sub (𝕫:= s) ∘ ren (wren ρ ◃ᵣ 𝕫) ∘ (wsub σ₀ ◃ₛ var 𝕫)) t
            ≡⟨ subᵉ eqᵉ t ⟩
                sub (ren ρ ∘ σ₀ ◃ₛ s) t
            ∎

        G : Red
            (sub (var ◃ₛ s) $
                ren (wren ρ ◃ᵣ 𝕫) $
                    sub (wsub σ₀ ◃ₛ var 𝕫) t)
        G rewrite eq = ⟦ t ⟧ λ
            { 𝕫     -> F
            ; (𝕤 v) -> Red-ren ρ (σ v) }

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
-- restricted type. Can you see how?

-- And the normalization function, which throws the proof away.
normalize : Term Γ α -> Term Γ α
normalize t = reify (⟦ t ⟧ Red-id) .nf

open benchmark
-- Let's put our program to test!

nbe-eta = normalize bench-eta
nbe-beta = normalize bench-beta  -- ^ ^ var 𝕫
nbe-both = normalize bench-both  -- ^ ^ ^ var (𝕤 𝕤 𝕫) ∙ var (𝕤 𝕫) ∙ var 𝕫
nbe-rec = normalize bench-rec  -- (# 720)
-- Normalize them to see the result!

nbe-rec-canon = canon (Normal-ℕ (reify (⟦ bench-rec ⟧ Red-id) .NF))
-- This should evaluate to (720 : Nat)
