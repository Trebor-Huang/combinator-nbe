{-# OPTIONS --prop --postfix-projections --safe #-}
module STLC.stlc where
open import STLC.Equivalence
open import combinator using (Type; ℕ; _⇒_) public

data Context : Set where
    ∅ : Context
    _◂_ : Context -> Type -> Context
infixl 6 _◂_

private variable
    α β γ : Type
    Γ Δ : Context

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

data SKI (Γ : Context) : Type -> Set where
    var : Var Γ α -> SKI Γ α
    𝔎 : SKI Γ (α ⇒ β ⇒ α)
    𝔖 : SKI Γ ((α ⇒ β ⇒ γ) ⇒ (α ⇒ β) ⇒ (α ⇒ γ))
    _∙_ : SKI Γ (α ⇒ β) -> SKI Γ α -> SKI Γ β

𝕀 : Term Γ (α ⇒ α)
𝕀 = ^ var 𝕫

𝕂 : Term Γ (α ⇒ β ⇒ α)
𝕂 = ^ ^ var (𝕤 𝕫)

𝕊 : Term Γ ((α ⇒ β ⇒ γ) ⇒ (α ⇒ β) ⇒ (α ⇒ γ))
𝕊 = ^ ^ ^ (var (𝕤 𝕤 𝕫) ∙ var 𝕫) ∙ (var (𝕤 𝕫) ∙ var 𝕫)

reader : SKI (Γ ◂ α) β -> SKI Γ (α ⇒ β)
reader (var 𝕫) = 𝔖 ∙ 𝔎 ∙ (𝔎 {β = ℕ})
reader (var (𝕤 v)) = 𝔎 ∙ var v
reader 𝔎 = 𝔎 ∙ 𝔎
reader 𝔖 = 𝔎 ∙ 𝔖
reader (k ∙ k₁) = 𝔖 ∙ reader k ∙ reader k₁

translate : Term Γ α -> SKI Γ α
translate (var v) = var v
translate (^ t) = reader (translate t)
translate (t ∙ s) = translate t ∙ translate s

variable
    s t u v : Term Γ α

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
{-# INLINE wren #-}

ren : Renaming Γ Δ -> Function Γ Δ
ren ρ (var v) = var (ρ v)
ren ρ (^ t) = ^ ren (wren ρ ◃ᵣ 𝕫) t
ren ρ (t ∙ s) = ren ρ t ∙ ren ρ s

wsub : Substitution Γ Δ -> Substitution Γ (Δ ◂ α)
wsub σ = ren 𝕤_ ∘ σ
{-# INLINE wsub #-}

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

data Neutral : Term Γ α -> Set
data Normal : Term Γ α -> Set

data Neutral where
    var : (v : Var Γ α) -> Neutral (var v)
    _∙_ : Neutral s -> Normal t -> Neutral (s ∙ t)

data Normal where
    ntr : ∀ {s : Term Γ ℕ} -> Neutral s -> Normal s  -- Full η!
    ^_ : Normal s -> Normal (^ s)

infix 3 _~>!_ _~>_ _≈_
data _~>!_ : Term Γ α -> Term Γ α -> Prop where
    β! : {t : Term (Γ ◂ α) β} {s : Term Γ α}
        -> (^ t) ∙ s ~>! sub (𝕫:= s) t
    η! : {t : Term Γ (α ⇒ β)}
        -> t ~>! ^ ren 𝕤_ t ∙ var 𝕫

data _~>_ : Term Γ α -> Term Γ α -> Prop where
    red : s ~>! t -> s ~> t
    ^_ : s ~> t -> ^ s ~> ^ t
    _~∙_ : s ~> t -> ∀ u -> s ∙ u ~> t ∙ u
    _∙~_ : (u : Term Γ (α ⇒ β)) -> s ~> t -> u ∙ s ~> u ∙ t
infixl 16 _~∙_ _∙~_

_≈_ : Term Γ α -> Term Γ α -> Prop
_≈_ = Equivalence _~>_
{-# DISPLAY Equivalence _~>_ = _≈_ #-}

record WN (t : Term Γ α) : Set where
    constructor wn
    field
        {nf} : Term Γ α
        NF : Normal nf
        Conv : t ≈ nf
open WN
pattern normal ν = wn ν refl
