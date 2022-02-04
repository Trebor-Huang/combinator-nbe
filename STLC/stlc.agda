{-# OPTIONS --prop --postfix-projections #-}
module stlc where
open import Agda.Builtin.Equality using (_≡_; refl)

open import Equivalence

data Type : Set where
    ℕ : Type
    _⇒_ : Type -> Type -> Type
infixr 10 _⇒_

data Context : Set where
    ∅ : Context
    _◂_ : Context -> Type -> Context
infixl 6 _◂_

variable
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

𝕀 : Term Γ (α ⇒ α)
𝕀 = ^ var 𝕫

𝕂 : Term Γ (α ⇒ β ⇒ α)
𝕂 = ^ ^ var (𝕤 𝕫)

𝕊 : Term Γ ((α ⇒ β ⇒ γ) ⇒ (α ⇒ β) ⇒ (α ⇒ γ))
𝕊 = ^ ^ ^ (var (𝕤 𝕤 𝕫) ∙ var 𝕫) ∙ (var (𝕤 𝕫) ∙ var 𝕫)

variable
    s t u v : Term Γ α

Renaming Substitution Function : Context -> Context -> Set
Renaming Γ Δ = ∀ {α} -> Var Γ α -> Var Δ α
Substitution Γ Δ = ∀ {α} -> Var Γ α -> Term Δ α
Function Γ Δ = ∀ {α} -> Term Γ α -> Term Δ α

wren : Renaming Γ Δ -> Renaming (Γ ◂ α) (Δ ◂ α)
wren ρ 𝕫 = 𝕫
wren ρ (𝕤 v) = 𝕤 ρ v

ren : Renaming Γ Δ -> Function Γ Δ
ren ρ (var v) = var (ρ v)
ren ρ (^ t) = ^ ren (wren ρ) t
ren ρ (t ∙ s) = ren ρ t ∙ ren ρ s

wsub : Substitution Γ Δ -> Substitution (Γ ◂ α) (Δ ◂ α)
wsub σ 𝕫 = var 𝕫
wsub σ (𝕤 v) = ren 𝕤_ (σ v)

sub : Substitution Γ Δ -> Function Γ Δ
sub σ (var v) = σ v
sub σ (^ t) = ^ sub (wsub σ) t
sub σ (t ∙ s) = sub σ t ∙ sub σ s

infix 10 𝕫:=_
𝕫:=_ : Term Γ α -> Substitution (Γ ◂ α) Γ
(𝕫:= t) 𝕫 = t
(𝕫:= t) (𝕤 v) = var v

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
    β! : (^ t) ∙ s ~>! sub (𝕫:= s) t
    η! : t ~>! ^ ren 𝕤_ t ∙ var 𝕫

data _~>_ : Term Γ α -> Term Γ α -> Prop where
    red : s ~>! t -> s ~> t
    ^_ : s ~> t -> ^ s ~> ^ t
    _~∙_ : s ~> t -> ∀ u -> s ∙ u ~> t ∙ u
    _∙~_ : (u : Term Γ (α ⇒ β)) -> s ~> t -> u ∙ s ~> u ∙ t
infixl 16 _~∙_ _∙~_

_≈_ : Term Γ α -> Term Γ α -> Prop
_≈_ = Equivalence _~>_
{-# DISPLAY Equivalence _~>_ = _≈_ #-}

_ : 𝕊 {Γ = Γ} {α = α} ∙ 𝕂 ∙ 𝕂 {β = β} ≈ 𝕊 ∙ 𝕂 ∙ 𝕀
_ = red β! ~∙ _     ⟶
    red β!          ⟶
    ^ red β! ~∙ _   ⟶
    ^ red β!        ⟶

    ^ red β!        ⟵
    ^ red β! ~∙ _   ⟵
    red β!          ⟵
    red β! ~∙ _     ⟵
    refl

record WN (t : Term Γ α) : Set where
    constructor wn
    field
        {nf} : Term Γ α
        NF : Normal nf
        Conv : t ≈ nf
open WN
pattern normal ν = wn ν refl
