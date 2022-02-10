{-# OPTIONS --prop --postfix-projections --safe #-}
module STLC.STLC where
open import STLC.Equivalence
open import combinator using (Type; ℕ; _⇒_) public

-- We define contexts as lists of types.
data Context : Set where
    ∅ : Context
    _◂_ : Context -> Type -> Context
infixl 6 _◂_

private variable
    α β γ : Type
    Γ Δ : Context

-- A variable is a de Bruijn index into the context.
data Var : Context -> Type -> Set where
    𝕫  :            Var (Γ ◂ α) α
    𝕤_ : Var Γ α -> Var (Γ ◂ β) α
infixr 100 𝕤_

data Term : Context -> Type -> Set where
    var : Var Γ α -> Term Γ α
    ^_ : Term (Γ ◂ α) β -> Term Γ (α ⇒ β)
    _∙_ : Term Γ (α ⇒ β) -> Term Γ α -> Term Γ β

infixr 15 ^_
infixl 16 _∙_

-- Some familiar combinators
𝕀 : Term Γ (α ⇒ α)
𝕀 = ^ var 𝕫

𝕂 : Term Γ (α ⇒ β ⇒ α)
𝕂 = ^ ^ var (𝕤 𝕫)

𝕊 : Term Γ ((α ⇒ β ⇒ γ) ⇒ (α ⇒ β) ⇒ (α ⇒ γ))
𝕊 = ^ ^ ^ (var (𝕤 𝕤 𝕫) ∙ var 𝕫) ∙ (var (𝕤 𝕫) ∙ var 𝕫)

-- A benchmark for normalization, will be used later.
module benchmark where
    -- A very high-order type:
    High = ((ℕ ⇒ ℕ) ⇒ ℕ ⇒ ℕ) ⇒ (ℕ ⇒ ℕ) ⇒ ℕ

    -- This type is used to test eta-expansions.
    bench-eta : Term (∅ ◂ High) High
    bench-eta = var 𝕫

    -- Now for beta-reductions:
    Middle = ℕ ⇒ ℕ ⇒ ℕ
    twice : Term ∅ ((Middle ⇒ Middle) ⇒ (Middle ⇒ Middle))
    twice = ^ ^ var (𝕤 𝕫) ∙ (var (𝕤 𝕫) ∙ var 𝕫)

    flip : Term ∅ (Middle ⇒ Middle)
    flip = ^ ^ ^ var (𝕤 𝕤 𝕫) ∙ var 𝕫 ∙ var (𝕤 𝕫)

    true : Term ∅ Middle
    true = 𝕂

    false : Term ∅ Middle
    false = 𝕂 ∙ 𝕀

    bench-beta : Term ∅ Middle
    bench-beta = twice ∙ flip ∙ false

    bench-both : Term ∅ (Middle ⇒ Middle)
    bench-both = twice ∙ flip

-- We also demonstrate how to translate to SK-combinators.
module SK-translation where
    -- To make induction go through, we also need variables.
    data SK (Γ : Context) : Type -> Set where
        var : Var Γ α -> SK Γ α
        𝔎 : SK Γ (α ⇒ β ⇒ α)
        𝔖 : SK Γ ((α ⇒ β ⇒ γ) ⇒ (α ⇒ β) ⇒ (α ⇒ γ))
        _∙_ : SK Γ (α ⇒ β) -> SK Γ α -> SK Γ β
    -- This corresponds to Hilbert style deduction systems,
    -- except that we have hypotheses (variables).

    -- The deduction theorem of Hilbert-style propositional calculus,
    -- which proves that hypotheses are unnecessary.
    deduction : SK (Γ ◂ α) β -> SK Γ (α ⇒ β)
    deduction (var 𝕫) = 𝔖 ∙ 𝔎 ∙ (𝔎 {β = ℕ})
    deduction (var (𝕤 v)) = 𝔎 ∙ var v
    deduction 𝔎 = 𝔎 ∙ 𝔎
    deduction 𝔖 = 𝔎 ∙ 𝔖
    deduction (c ∙ c') = 𝔖 ∙ deduction c ∙ deduction c'

    -- The translation.
    translate : Term Γ α -> SK Γ α
    translate (var v) = var v
    translate (^ t) = deduction (translate t)
    translate (t ∙ s) = translate t ∙ translate s

    -- Now we can compile closed terms to the combinators defined
    -- previously:
    coerce : SK ∅ α -> combinator.Term α
    coerce 𝔎 = combinator.𝕂
    coerce 𝔖 = combinator.𝕊
    coerce (c ∙ c') = coerce c combinator.∙ coerce c'

    compile : Term ∅ α -> combinator.Term α
    compile = coerce ∘ translate

variable
    s t u v : Term Γ α

-- Next, we define basic term manipulations.
-- These are standard constructions for well-typed de Bruijn terms.
Renaming Substitution Function : Context -> Context -> Set
Renaming Γ Δ = ∀ {α} -> Var Γ α -> Var Δ α
Substitution Γ Δ = ∀ {α} -> Var Γ α -> Term Δ α
Function Γ Δ = ∀ {α} -> Term Γ α -> Term Δ α

infixl 6 _◃ᵣ_
_◃ᵣ_ : Renaming Γ Δ -> Var Δ α -> Renaming (Γ ◂ α) Δ
(σ ◃ᵣ v) 𝕫 = v
(σ ◃ᵣ _) (𝕤 v) = σ v

wren : Renaming Γ Δ -> Renaming Γ (Δ ◂ α)
wren ρ = 𝕤_ ∘ ρ

ren : Renaming Γ Δ -> Function Γ Δ
ren ρ (var v) = var (ρ v)
ren ρ (^ t) = ^ ren (wren ρ ◃ᵣ 𝕫) t
ren ρ (t ∙ s) = ren ρ t ∙ ren ρ s

wsub : Substitution Γ Δ -> Substitution Γ (Δ ◂ α)
wsub σ = ren 𝕤_ ∘ σ

infixl 6 _◃ₛ_
_◃ₛ_ : Substitution Γ Δ -> Term Δ α -> Substitution (Γ ◂ α) Δ
(σ ◃ₛ t) 𝕫 = t
(σ ◃ₛ t) (𝕤 v) = σ v

sub : Substitution Γ Δ -> Function Γ Δ
sub σ (var v) = σ v
sub σ (^ t) = ^ sub (wsub σ ◃ₛ var 𝕫) t
sub σ (t ∙ s) = sub σ t ∙ sub σ s

infix 10 𝕫:=_
𝕫:=_ : Term Γ α -> Substitution (Γ ◂ α) Γ
𝕫:= t = var ◃ₛ t

-- Next, we define Normal terms.
-- Naturally, a normal term is of the form
--   ^ ^ ^ ... (var v) ∙ ν₁ ∙ ν₂ ∙ ν₃ ...
-- where v is a variable, and νₙ are all normal forms.
-- This breaks the definition up into two stages.
data Neutral : Term Γ α -> Set
data Normal : Term Γ α -> Set

data Neutral where  -- Neutral terms are the inner part, without λs.
    var : (v : Var Γ α) -> Neutral (var v)
    _∙_ : Neutral s -> Normal t -> Neutral (s ∙ t)

data Normal where  -- Normal terms cap the λs up.
    ntr : {s : Term Γ ℕ} -> Neutral s -> Normal s
    -- Note the explicit type ascription (Term Γ ℕ).
    -- This means that a variable of type (ℕ ⇒ ℕ) is not normal!
    -- we need to eta-expand it into (λ x. f x).
    ^_ : Normal s -> Normal (^ s)

-- Next, we define reduction.
infix 3 _~>!_ _~>_ _≈_
data _~>!_ : Term Γ α -> Term Γ α -> Prop where
    β! : {t : Term (Γ ◂ α) β} {s : Term Γ α}
        -> (^ t) ∙ s ~>! sub (𝕫:= s) t
    η! : {t : Term Γ (α ⇒ β)}
        -> t ~>! ^ ren 𝕤_ t ∙ var 𝕫
-- We define these in Prop, because we won't use them for computation.

-- Congruence closure:
data _~>_ : Term Γ α -> Term Γ α -> Prop where
    red : s ~>! t -> s ~> t
    ^_ : s ~> t -> ^ s ~> ^ t
    _~∙_ : s ~> t -> ∀ u -> s ∙ u ~> t ∙ u
    _∙~_ : (u : Term Γ (α ⇒ β)) -> s ~> t -> u ∙ s ~> u ∙ t
infixl 16 _~∙_ _∙~_

-- Equivalence closure:
_≈_ : Term Γ α -> Term Γ α -> Prop
_≈_ = Equivalence _~>_
{-# DISPLAY Equivalence _~>_ = _≈_ #-}

-- Read as a proposition: t is weakly normalizing.
-- Read as a datatype: a normal form of t, carrying relevant proofs.
record WN (t : Term Γ α) : Set where
    constructor wn
    field
        {nf} : Term Γ α
        NF : Normal nf
        Conv : t ≈ nf
open WN
pattern normal ν = wn ν refl

-- Strongly normalizing terms.
data SN : Term Γ α -> Set where
    sn : (∀ t -> s ~> t -> SN t) -> SN s
