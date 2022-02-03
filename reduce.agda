{-# OPTIONS --prop #-}
module reduce where
open import Agda.Builtin.Nat using (Nat; suc; zero)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Sum using (_⊎_)

open import combinator

{-# TERMINATING #-}
reduce : (A : Term α) -> WN A
reduce O = wn (ℕ zero) refl
reduce S = wn S₀ refl
reduce (S ∙ A) with reduce A
... | wn (ℕ n) R = wn (ℕ (suc n)) (map appᵣ R)
reduce 𝕂 = wn 𝕂₀ refl
reduce (𝕂 ∙ A) with reduce A
... | wn ν R = wn (𝕂₁ ν) (map appᵣ R)
reduce (𝕂 ∙ A ∙ B) with reduce A
... | wn ν R = wn ν (step (red 𝕂) R)
reduce 𝕊 = wn 𝕊₀ refl
reduce (𝕊 ∙ A) with reduce A
... | wn ν R = wn (𝕊₁ ν) (map appᵣ R)
reduce (𝕊 ∙ A ∙ B) with reduce A | reduce B
... | wn ν₁ R₁ | wn ν₂ R₂ = wn (𝕊₂ ν₁ ν₂)
    (map appₗ (map appᵣ R₁) ⁀ map appᵣ R₂)
reduce (𝕊 ∙ A ∙ B ∙ C) with reduce (A ∙ C ∙ (B ∙ C))
... | wn ν R = wn ν (step (red 𝕊) R)
reduce ℝ = wn ℝ₀ refl
reduce (ℝ ∙ A) with reduce A
... | wn ν R = wn (ℝ₁ ν) (map appᵣ R)
reduce (ℝ ∙ A ∙ B) with reduce A | reduce B
... | wn ν₁ R₁ | wn ν₂ R₂ = wn (ℝ₂ ν₁ ν₂)
    (map appₗ (map appᵣ R₁) ⁀ map appᵣ R₂)
reduce (ℝ ∙ O ∙ A ∙ B) with reduce A
... | wn ν R = wn ν (step (red ℝ0) R)
reduce (ℝ ∙ (S ∙ A) ∙ B ∙ C) with reduce (C ∙ (ℝ ∙ A ∙ B ∙ C))
... | wn ν R = wn ν (step (red ℝS) R)
reduce (A ∙ B) with reduce A
... | wn {B = A'} ν' R' with reduce (A' ∙ B)
... | wn ν R = wn ν (map appₗ R' ⁀ R)

normalize : Term α -> Term α
normalize A with reduce A
... | wn {B = B} _ _ = B

_ : normalize (Mult ∙ # 100 ∙ # 100) ≡ # 10000
_ = refl
