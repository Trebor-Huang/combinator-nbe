{-# OPTIONS --prop #-}
module nbe where
open import Agda.Builtin.Nat using (Nat; suc; zero)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Function.Base using (_$_)

infixl 10 _≫_
_≫_ : {P Q R : Prop}  -- _∘_ doesn't work on Props
    -> (P -> Q) -> (R -> P) -> (R -> Q)
(f ≫ g) z = f (g z)
{-# INLINE _≫_ #-}

open import combinator

Red : ∀ α -> Term α -> Set  -- Glue!
Red ℕ A = WN A
Red (α ⇒ β) A = WN A × ∀ {B} -> Red α B -> Red β (A ∙ B)

reify : Red α A -> WN A
reify {α = ℕ} Aʷ = Aʷ
reify {α = α ⇒ β} (Aʷ , _) = Aʷ

RedCl : (A ⟶ B) -> Red α B -> Red α A
RedCl {α = ℕ} R (wn ν R') = wn ν (R ⁀ R')
RedCl {α = α ⇒ β} R (wn ν R' , F) = wn ν (R ⁀ R') ,
    λ ⟦C⟧ -> RedCl (map appₗ R) (F ⟦C⟧)

⟦𝕂⟧ : Red α A -> Red β B -> Red α (𝕂 ∙ A ∙ B)
⟦𝕂⟧ ⟦A⟧ ⟦B⟧ = RedCl (single (red 𝕂)) ⟦A⟧

⟦𝕂₁⟧ : Red α A -> Red (β ⇒ α) (𝕂 ∙ A)
⟦𝕂₁⟧ ⟦A⟧ with reify ⟦A⟧
... | wn ν R = wn (𝕂₁ ν) (map appᵣ R) , ⟦𝕂⟧ ⟦A⟧

⟦𝕂₀⟧ : Red (α ⇒ β ⇒ α) 𝕂
⟦𝕂₀⟧ = wn 𝕂₀ refl , ⟦𝕂₁⟧

⟦𝕊⟧ : Red (α ⇒ β ⇒ γ) A
    -> Red (α ⇒ β) B
    -> Red α C
    -> Red γ (𝕊 ∙ A ∙ B ∙ C)
⟦𝕊⟧ ⟦A⟧ ⟦B⟧ ⟦C⟧ = RedCl (single (red 𝕊)) $
    (⟦A⟧ .proj₂ ⟦C⟧) .proj₂ (⟦B⟧ .proj₂ ⟦C⟧)

⟦𝕊₂⟧ : Red (α ⇒ β ⇒ γ) A -> Red (α ⇒ β) B -> Red (α ⇒ γ) (𝕊 ∙ A ∙ B)
⟦𝕊₂⟧ ⟦A⟧@(wn ν₁ R₁ , F₁) ⟦B⟧@(wn ν₂ R₂ , F₂)
    = wn (𝕊₂ ν₁ ν₂) (map appᵣ R₂ ⁀ map (appₗ ≫ appᵣ) R₁) , ⟦𝕊⟧ ⟦A⟧ ⟦B⟧

⟦𝕊₁⟧ : Red (α ⇒ β ⇒ γ) A -> Red ((α ⇒ β) ⇒ (α ⇒ γ)) (𝕊 ∙ A)
⟦𝕊₁⟧ ⟦A⟧@(wn ν R , F) = wn (𝕊₁ ν) (map appᵣ R) , ⟦𝕊₂⟧ ⟦A⟧

⟦𝕊₀⟧ : Red ((α ⇒ β ⇒ γ) ⇒ (α ⇒ β) ⇒ (α ⇒ γ)) 𝕊
⟦𝕊₀⟧ = wn 𝕊₀ refl , ⟦𝕊₁⟧

⟦ℝ_⟧ : ∀ n -> Red α B -> Red (α ⇒ α) C -> Red α (ℝ ∙ (# n) ∙ B ∙ C)
⟦ℝ zero ⟧ ⟦B⟧ ⟦C⟧ = RedCl (single (red ℝ0)) ⟦B⟧
⟦ℝ suc n ⟧ ⟦B⟧ ⟦C⟧ = RedCl (single (red ℝS)) $
    ⟦C⟧ .proj₂ (⟦ℝ n ⟧ ⟦B⟧ ⟦C⟧)

⟦ℝ⟧ : Red ℕ A -> Red α B -> Red (α ⇒ α) C -> Red α (ℝ ∙ A ∙ B ∙ C)
⟦ℝ⟧ (wn (ℕ n) R) ⟦B⟧ ⟦C⟧ =
    RedCl (map (appₗ ≫ appₗ ≫ appᵣ) R) (⟦ℝ n ⟧ ⟦B⟧ ⟦C⟧)

⟦ℝ₂⟧ : Red ℕ A -> Red α B -> Red ((α ⇒ α) ⇒ α) (ℝ ∙ A ∙ B)
⟦ℝ₂⟧ ⟦A⟧@(wn ν₁ R₁) ⟦B⟧ with reify ⟦B⟧
... | wn ν₂ R₂ = wn (ℝ₂ ν₁ ν₂) (map appᵣ R₂ ⁀ map (appₗ ≫ appᵣ) R₁) , ⟦ℝ⟧ ⟦A⟧ ⟦B⟧

⟦ℝ₁⟧ : Red ℕ A -> Red (α ⇒ (α ⇒ α) ⇒ α) (ℝ ∙ A)
⟦ℝ₁⟧ ⟦A⟧@(wn ν R) = wn (ℝ₁ ν) (map appᵣ R) , ⟦ℝ₂⟧ ⟦A⟧

⟦ℝ₀⟧ : Red (ℕ ⇒ α ⇒ (α ⇒ α) ⇒ α) ℝ
⟦ℝ₀⟧ = wn ℝ₀ refl , ⟦ℝ₁⟧

⟦S⟧ : Red ℕ A -> Red ℕ (S ∙ A)
⟦S⟧ (wn (ℕ n) R) = wn (ℕ (suc n)) (map appᵣ R)

⟦_⟧ : ∀ A -> Red α A
⟦ A ∙ B ⟧ = ⟦ A ⟧ .proj₂ ⟦ B ⟧
⟦ 𝕂 ⟧ = ⟦𝕂₀⟧
⟦ 𝕊 ⟧ = ⟦𝕊₀⟧
⟦ ℝ ⟧ = ⟦ℝ₀⟧
⟦ O ⟧ = wn (ℕ zero) refl
⟦ S ⟧ = wn S₀ refl , ⟦S⟧

normalize : Term α -> Term α
normalize A with reify ⟦ A ⟧
... | wn {B = B} _ _ = B

_ : normalize (Mult ∙ # 100 ∙ # 100) ≡ # 10000
_ = refl
