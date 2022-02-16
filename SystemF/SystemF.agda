{-# OPTIONS --prop --postfix-projections --safe #-}
module SystemF.SystemF where
open import Agda.Builtin.Equality
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Fin.Base using (Fin; zero; suc)

TypeContext = ℕ
TypeVar = Fin

variable
    Ω Ω' : TypeContext

data Context : TypeContext -> Set
data Type : TypeContext -> Set

variable
    Γ Δ : Context Ω
    α β : Type Ω

infixl 5 _◂_ _⋆
data Context where
    ∅ : Context Ω
    _◂_ : (Γ : Context Ω) -> Type Ω -> Context Ω
    _⋆ : Context Ω -> Context (suc Ω)

infixr 6 Π_
infixr 7 _⇒_
data Type where
    var : TypeVar Ω -> Type Ω
    Π_ : Type (suc Ω) -> Type Ω
    _⇒_ : Type Ω -> Type Ω -> Type Ω

Rent Subt Funt : TypeContext -> TypeContext -> Set
Rent Ω' Ω = TypeVar Ω -> TypeVar Ω'
Subt Ω' Ω = TypeVar Ω -> Type Ω'
Funt Ω' Ω = Type Ω    -> Type Ω'

wrent : Rent Ω' Ω -> Rent (suc Ω') (suc Ω)
wrent ρ zero = zero
wrent ρ (suc i) = suc (ρ i)

rent : Rent Ω' Ω -> Funt Ω' Ω
rent ρ (var i) = var (ρ i)
rent ρ (Π α) = Π rent (wrent ρ) α
rent ρ (α ⇒ β) = rent ρ α ⇒ rent ρ β

wsubt : Subt Ω' Ω -> Subt (suc Ω') (suc Ω)
wsubt σ zero = var zero
wsubt σ (suc i) = rent suc (σ i)

subt : Subt Ω' Ω -> Funt Ω' Ω
subt σ (var i) = σ i
subt σ (Π α) = Π subt (wsubt σ) α
subt σ (α ⇒ β) = subt σ α ⇒ subt σ β

extt : Type Ω -> Subt Ω (suc Ω)
extt α zero = α
extt α (suc i) = var i

data Var : (Γ : Context Ω) -> Type Ω -> Set where
    𝕫 : Var (Γ ◂ α) α
    𝕤_ : Var Γ α -> Var (Γ ◂ β) α
    𝕊_ : Var Γ α -> Var (Γ ⋆) (rent suc α)

infixr 15 Λ_ ^_
infixl 20 _!_ _∙_
data Term : (Γ : Context Ω) -> Type Ω -> Set where
    var : Var Γ α -> Term Γ α
    Λ_ : Term (Γ ⋆) α -> Term Γ (Π α)
    ^_ : Term (Γ ◂ α) β -> Term Γ (α ⇒ β)
    _!_ : Term {Ω = Ω} Γ (Π α)
        -> (β : Type Ω)
        -> Term Γ (subt (extt β) α)
    _∙_ : Term Γ (α ⇒ β) -> Term Γ α -> Term Γ β

𝔎 : Term Γ (Π Π var (suc zero) ⇒ var zero ⇒ var (suc zero))
𝔎 = Λ Λ ^ ^ var (𝕤 𝕫)
