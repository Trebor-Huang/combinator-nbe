{-# OPTIONS --prop --postfix-projections --safe #-}
module STLC.Category where
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_)
open import Agda.Builtin.Equality using (_≡_; refl)

open import STLC.Equivalence
open import STLC.STLC
open import STLC.Substitution

private variable
    α β γ : Type
    Γ Γ₁ Γ₂ Δ Δ₁ Δ₂ Ξ : Context
    σ τ σ₁ σ₂ σ₃ : Substitution Γ Δ
    ρ ρ₀ ρ₁ ρ₂ ρ₃ : Renaming Γ Δ

-- The following material packages everything up into nice categorical language.
-- I'm not going through the work of proving trivial lemmas. The key lemmas are
-- already proved in our previous work, and I'll restate them in a better form.
module 𝓣 where
    Obj : Set
    Obj = Context

    Mor : Obj -> Obj -> Set
    Mor Γ Δ = {α : Type} -> Var Δ α -> Term Γ α
    -- Why the reversal? Fundamentally, it's because this suggests
    --   Mor Γ Δ  ∼  Γ ⊢ Δ
    -- i.e. a list of judgements Γ ⊢ x : α. This order makes concepts
    -- like products and sums much more natural.

    idMor : Mor Γ Γ
    idMor = var

    compMor : Mor Γ Δ -> Mor Ξ Γ -> Mor Ξ Δ
    compMor σ τ = sub τ ∘ σ

    -- To prevent Agda inserting implicit arguments.
    -- Also to avoid function extensionality.
    _==_ : Mor Γ Δ -> Mor Γ Δ -> Prop
    σ == τ = ∀ {α} {v : Var _ α} -> σ v ≈ τ v
    infix 3 _==_

    -- The following laws are either trivial or proved in STLC.Substitution.
    idₗ : compMor idMor σ == σ
    idₗ = refl

    idᵣ : compMor σ idMor == σ
    idᵣ {σ = σ} {v = v} rewrite sub-var (σ v) = refl

    assoc : compMor (compMor σ₁ σ₂) σ₃ == compMor σ₁ (compMor σ₂ σ₃)
    assoc {σ₁ = σ₁} {σ₂ = σ₂} {σ₃ = σ₃} {v = v}
        rewrite sub-sub σ₃ σ₂ (σ₁ v) = refl

    -- Our category has products: context concatenation.
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
    -- The laws of products are omitted. But the reader should see that there
    -- is no difficulty proving them.

    𝟏 : Obj
    𝟏 = ∅

    -- Exponential objects are expressed using function spaces. But since we
    -- need to deal with exponential objects between contexts, we need a
    -- telescoping operation:
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

    -- And the usual adjunction properties for exponential objects.
    -- Keep in mind that Hom here denotes internal hom, while Mor is the arrows.
    uncurry : Mor Γ (Hom Ξ Δ) -> Mor (Γ × Ξ) Δ
    uncurry σ 𝕫 = app (σ 𝕫)
    uncurry σ (𝕤 v) = uncurry (σ ∘ 𝕤_) v

    curry : Mor (Γ × Ξ) Δ -> Mor Γ (Hom Ξ Δ)
    curry {Δ = Δ ◂ _} σ 𝕫 = abs (σ 𝕫)
    curry {Δ = Δ ◂ _} σ (𝕤 v) = curry (σ ∘ 𝕤_) v
    -- As usual we omit the laws. Note that the two adjunction laws require
    -- β- and η-conversions, respectively.

-- Apart from substitutions, we also have a category of renamings,
-- which will prove useful later on. Renamings are basically permutations
-- that preserves types, so it is easy refls.
module 𝓦 where
    Obj : Set
    Obj = Context

    Mor : Obj -> Obj -> Set
    Mor Γ Δ = {α : Type} -> Var Δ α -> Var Γ α

    idMor : Mor Γ Γ
    idMor = id

    compMor : Mor Γ Δ -> Mor Ξ Γ -> Mor Ξ Δ
    compMor ρ₁ ρ₂ = ρ₂ ∘ ρ₁

    _==_ : Mor Γ Δ -> Mor Γ Δ -> Set
    ρ₁ == ρ₂ = ∀ {α} {v : Var _ α} -> ρ₁ v ≡ ρ₂ v
    infix 3 _==_

    idₗ : compMor idMor ρ == ρ
    idₗ = refl

    idᵣ : compMor ρ idMor == ρ
    idᵣ = refl

    assoc : compMor (compMor ρ₁ ρ₂) ρ₃ == compMor ρ₁ (compMor ρ₂ ρ₃)
    assoc = refl

-- We define the Shape functor ∫. This determines the shape of the Kripke
-- worlds. It is denoted by ρ in J.Sterling's thesis.
module Shape where
    ∫ : 𝓦.Obj -> 𝓣.Obj
    ∫ = id  -- The map on objects is identity.

    fmap : 𝓦.Mor Γ Δ -> 𝓣.Mor (∫ Γ) (∫ Δ)
    fmap ρ = ren ρ ∘ var

    fmap-id : let _==_ = 𝓣._==_ in
        fmap {Γ} 𝓦.idMor == 𝓣.idMor
    fmap-id = refl

    fmap-comp : let _==_ = 𝓣._==_ in
        fmap (𝓦.compMor ρ₁ ρ₂) == 𝓣.compMor (fmap ρ₁) (fmap ρ₂)
    fmap-comp = refl
open Shape using (∫)

-- Since I'm not gonna prove all the laws, we just need this poor man's presheaf
-- definition :P
Psh : Set -> Set₁
Psh X = X -> Set

PshMor : (X : Set) -> Psh X -> Psh X -> Set
PshMor X 𝔞 𝔟 = ∀ {A} -> 𝔞 A -> 𝔟 A

-- Ignore this if you don't already know simplicial sets. It only explains
-- the origin of the name "Nerve".

-- In simplicial homotopy, the Nerve functor maps a category to a simplicial
-- set having the same "shape". An object to a vertex, a morphism to an edge,
-- a commutative triangle to a trangle face, etc. So, mapping a category 𝒞 to
-- a simplicial set (i.e. a function f : Δᵒᵖ -> Set), the nerve functor is
-- (N : Cat -> Psh(Δ)). We have that N(A)ₙ, the n-face component, is the hom-set
-- Mor(Δₙ , 𝒞), where Δₙ is a category with (n+1) objects A₀->A₁->...->Aₙ.

-- This can be generalized to any (N : 𝒞 -> Psh(Δ)), as long as we have an
-- "internal Δₙ" in 𝒞, i.e. we need a functor (ρ : ℕ -> 𝒞), and we define
-- N(A)ₙ = Mor(ρ(n), A). This ρ is called the "shape". Of course, we need not
-- be confined to ℕ. So with any "shape" functor (ρ : 𝒲 -> 𝒞), we can form
-- N(A)(i) = Mor(ρ(i), A). This makes N a functor from 𝒞 to Psh(𝒲).

-- The Nerve functor, which we denote as Pts, computes a presheaf of Kripke
-- structures. It's fine if you don't see how. Since we've defined Red in our
-- previous work, which was said to possess a Kripke structure, we will later
-- relate Pts to Red.
module Nerve where
    Pts : 𝓣.Obj -> Psh 𝓦.Obj
    Pts Γ = \ Δ -> 𝓣.Mor (∫ Δ) Γ

    -- Pts Γ is indeed a presheaf for each Γ:
    psh-fmap : 𝓦.Mor Δ₁ Δ₂ -> (Pts Γ Δ₂ -> Pts Γ Δ₁)
    psh-fmap ρ σ = ren ρ ∘ σ

    -- And Pts is indded a functor from 𝓣 to Psh(𝓦):
    fmap : 𝓣.Mor Γ₁ Γ₂ -> PshMor 𝓦.Obj (Pts Γ₁) (Pts Γ₂)
    fmap σ₁ σ₂ = sub σ₂ ∘ σ₁
    -- Laws omitted
open Nerve using (Pts)
-- The types may be a little bit confusing, but this is basically because I'm
-- too lazy to set up all the category structures. If we rewrite this with a
-- proper category theory library, Agda will force us to prove all the laws,
-- which probably makes it clearer.

module Glue where
    -- The type of computability structures:
    record Tait (Γ : 𝓣.Obj) : Set₁ where
        field
            -- Tait structures on Γ are defined as:
            --   Total : Psh 𝓦.Obj
            --   proj : ∀ {Δ} -> Total Δ -> Pts Γ Δ
            -- Presheaf morphism laws of proj omitted.
            -- We can do that, but note that whenever we have a structure
            -- consisting of a (T : Set) and (proj : T -> X), we can always
            -- rewrite it as (fiber : X -> Set) and let T be (Σ X fiber).
            -- This suggests we can do the same to presheafs.
            fiber : ∀ {Δ} -> Pts Γ Δ -> Set
        private
            Total : Psh 𝓦.Obj
            Total Δ = Σ (Pts Γ Δ) fiber
            -- The definition with Total is more suited to the category language
            -- using slice categories, while we can use the fiber definition
            -- which is more convenient in type theory.
        -- We need to remember that we need the functor law for proj, i.e.
        -- for any (ρ : 𝓦.Mor Δ₁ Δ₂), we need to prove that Total gives a fmap
        -- to (fmap ρ : Total Δ₂ -> Total Δ₁), and we need to natural transform
        -- that with proj to Pts Γ. Unpacking this to the fiber language, we
        -- arrive at:
        field
            fiber-fmap : (ρ : 𝓦.Mor Δ₁ Δ₂) (pt : Pts Γ Δ₂)
                -> (fiber pt -> fiber (Nerve.psh-fmap ρ pt))
        -- Laws are also omitted.
        -- If you unfold this, you can see that this amounts to giving
        --   (fiber pt -> fiber (ren ρ ∘ pt)).
        -- This is just our Red-ren : Red t -> Red (ren ρ t)
        -- but with Red generalized to operate on contexts.

    -- The objects of the glued category 𝓖 is just (Σ 𝓣.Obj Tait).
    -- This creates a natural projection proj₁ : 𝓖.Obj -> 𝓣.Obj.
    open Tait

    -- The fundamental theorem we want to prove is that there is
    -- a section of proj₁, i.e. a map sect : (Γ : 𝓣.Obj) -> Tait Γ.

    -- We import our Red definition, and generalize it to contexts.
    open import STLC.NbE
    Reds : (Γ Δ : Context) -> Pts Γ Δ -> Set
    Reds Γ Δ σ = ∀ {α} -> (v : Var Γ α) -> Red (σ v)

    sect : (Γ : 𝓣.Obj) -> Tait Γ
    sect _ .fiber = Reds _ _
    -- Yay, we're done! ... wait, is it that simple? Of course not.
    -- We need to prove that the whole thing satisfies laws.

    sect _ .fiber-fmap ρ₀ pt Rs = Reds-ren Rs
        where
            Reds-ren : Reds Γ Δ₂ σ -> Reds Γ Δ₁ (ren ρ ∘ σ)
            Reds-ren Rs v = Red-ren _ (Rs v)
    -- Since we've already done all the hard work, this just generalizes to
    -- a list of terms (a.k.a. a substitution) instead of just a term.

    -- And finally, we need the *ultimate* proof: sect must be natural, which
    -- we omitted in the Tait record.

    -- Natural in what category? Recall that sect is a right inverse to
    -- proj, which is a morphism from (Total : Psh(𝓦)) to (Pts Γ : Psh(𝓦)),
    -- and morphisms from presheafs to presheafs are natural transformations.
    -- Translating to the fibered language, we have
    sect-natural : (σ : 𝓣.Mor Γ₁ Γ₂) (pt : Pts Γ₁ Δ)
        -> Reds Γ₁ Δ pt -> Reds Γ₂ Δ (𝓣.compMor σ pt)
    -- How do we prove that, welllll...
    -- Look back at the definition of Reds. Don't you think "Red generalized
    -- to substitutions" sounds familiar? This is because it is exactly our
    -- SubstRed!
    _ : Reds Γ Δ σ ≡ SubstRed σ
    _ = refl

    sect-natural σ pt Rs v = ⟦ σ v ⟧ Rs
    -- Violà! We successfully packaged every result we proved up into a better,
    -- more categorical language!

    -- For "purely categorical" versions, read Chapter 4 of Sterling's thesis.
