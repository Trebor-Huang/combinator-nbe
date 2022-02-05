{-# OPTIONS --prop #-}
module nbe where
open import Agda.Builtin.Nat using (Nat; suc; zero)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤)

open import combinator

private variable
    α β γ : Type
    n : Nat
    M N A B C : Term α

-- We now take a differerent approach.
-- Instead of blindly following the reduction rules, let's
-- really find out what the combinator 𝑚𝑒𝑎𝑛𝑠.

-- Since these are not part of the final program, I
-- separate them into a private module.
private module Meaning where
    -- What does the types mean?
    -- ℕ means the natural numbers Nat, no doubt. And
    -- (α ⇒ β) should mean the function space.
    -- So we might do the following:
    Meaning : Type -> Set
    Meaning ℕ = Nat
    Meaning (α ⇒ β) = Meaning α -> Meaning β
    -- Then, we want to 𝑖𝑛𝑡𝑒𝑟𝑝𝑟𝑒𝑡 the combinators to their Meaning.
    interpret : Term α -> Meaning α
    interpret O = zero
    interpret S = suc
    interpret ℝ = rec
        where
            rec : ∀ {A : Set} -> Nat -> A -> (Nat -> A -> A) -> A
            rec zero a f = a
            rec (suc n) a f = f n (rec n a f)
    interpret 𝕂 = λ z _ -> z
    interpret 𝕊 = λ x y z -> x z (y z)
    interpret (M ∙ N) = interpret M (interpret N)
    -- All work fine, and the most important thing is that if two things are
    -- considered equal, then their interpretations are equal:
    _ : interpret (𝕂 ∙ 𝕂 ∙ 𝕀 {ℕ}) ≡ λ (x : Nat) (y : Nat) -> x
    _ = refl
    _ : interpret (𝕂 ∙ 𝕂 ∙ 𝕊 {ℕ}{ℕ}{ℕ}) ≡ λ (x : Nat) (y : Nat) -> x
    _ = refl
    -- (There are some eta-equality related problems that we will not discuss here.)
    -- To make use of the interpretations, we need a way to convert
    -- the interpreted terms into normal forms. In other words:
    --     reify : Meaning α -> Term α
    -- But we can't do that. This is because in the function spaces,
    -- there are more functions than we can express in the combinator
    -- language! And if we worked in Set theory instead of Agda, there
    -- would be even more of those ghost functions. (Exercise: try to
    -- implement the function reify, and describe the difficulty you
    -- encounter.)

-- What can we do to amend the situation? Actually we just need a
-- very natural change. Note that in our previous implementation
-- in reduce.agda, we only cared about the normal forms, i.e. the syntax.
-- And in the development above, we only cared about the meanings,
-- i.e. the semantics. This suggests the following change...

-- For ℕ the meaning stays the same, but for
-- function spaces, we require 𝑏𝑜𝑡ℎ a normal form 𝑎𝑛𝑑 a function.
-- In Agda code:
--     Meaning : Type -> Set
--     Meaning ℕ = Nat
--     Meaning (α ⇒ β) = NormalForm (α ⇒ β) × (Meaning α -> Meaning β)
-- where NormalForm (which is not yet defined) is the type of normal
-- forms. This is sufficient for programming purposes, and is close to
-- the real-world implementations. But since we are using Agda, we
-- shouldn't confine ourselves to programming. We should simultaneously
-- produce a 𝑝𝑟𝑜𝑜𝑓 that the normal form can indeed be obtained from
-- reducing the original term. This means that we also need to keep track
-- of the original term. (After program extraction, the proofs are
-- erased, so there's no additional cost in the program.)

-- This produces the definition of (Red α A), which stands for
-- "A is reducible of type α". Our new definition for the Meaning of α
-- is exactly the reducible terms.
-- The word "reducible" comes from Tait. We also adopt the convention
-- to use ⟦ M ⟧ to denote the interpretation of M
Red : ∀ α -> Term α -> Set  -- Glue!
Red α A = WN A × helper α A
    where
        helper : ∀ α -> Term α -> Set
        helper ℕ A = ⊤
        helper (α ⇒ β) A = ∀ {B} -> Red α B -> Red β (A ∙ B)

-- We can easily extract the normal form now.
reify : Red α A -> WN A
reify = proj₁

-- A very interesting lemma: if A reduces to B, and B is reducible,
-- then A is also reducible.
RedCl : (A ⟶ B) -> Red α B -> Red α A
RedCl {α = ℕ} R (wn ν R' , _) = wn ν (R ⁀ R') , _
RedCl {α = α ⇒ β} R (wn ν R' , F) = wn ν (R ⁀ R') ,
    λ ⟦C⟧ -> RedCl (map appₗ R) (F ⟦C⟧)

-- The easy ones first.
⟦#_⟧ : ∀ n -> Red ℕ (# n)
⟦# n ⟧ = wn (ℕ n) refl , _  -- Agda can easily work out all these.

⟦S⟧ : Red ℕ A -> Red ℕ (S ∙ A)
⟦S⟧ (wn (ℕ n) R , _) = wn (ℕ (suc n)) (map appᵣ R) , _

-- The interpretation of 𝕂 is also simple, we invoke the lemma.
-- Since (𝕂 ∙ A ∙ B) just reduces to A, so according to RedCl
-- we just need to prove that A is reducible; which is the assumption.
⟦𝕂⟧ : Red α A -> Red β B -> Red α (𝕂 ∙ A ∙ B)
⟦𝕂⟧ ⟦A⟧ ⟦B⟧ = RedCl (single (red 𝕂)) ⟦A⟧

-- Now for partially applied 𝕂, we just need to make use of the previous case.
⟦𝕂₁⟧ : Red α A -> Red (β ⇒ α) (𝕂 ∙ A)
⟦𝕂₁⟧ ⟦A⟧ with reify ⟦A⟧
... | wn ν R = wn (𝕂₁ ν) (map appᵣ R) , ⟦𝕂⟧ ⟦A⟧

-- Similarly for unapplied 𝕂.
⟦𝕂₀⟧ : Red (α ⇒ β ⇒ α) 𝕂
⟦𝕂₀⟧ = wn 𝕂₀ refl , ⟦𝕂₁⟧

⟦𝕊⟧ : Red (α ⇒ β ⇒ γ) A
    -> Red (α ⇒ β) B
    -> Red α C
    -> Red γ (𝕊 ∙ A ∙ B ∙ C)
⟦𝕊⟧ ⟦A⟧ ⟦B⟧ ⟦C⟧ = RedCl (single (red 𝕊)) $
    (⟦A⟧ .proj₂ ⟦C⟧) .proj₂ (⟦B⟧ .proj₂ ⟦C⟧)
-- See how everything passes though without the need for the TERMINATING pragma?
-- The interpretation of ⟦A⟧ includes a function that maps
-- every C to the interpretation of (A ∙ C), and we just need
-- to use .proj₂ to fetch it.

⟦𝕊₂⟧ : Red (α ⇒ β ⇒ γ) A -> Red (α ⇒ β) B -> Red (α ⇒ γ) (𝕊 ∙ A ∙ B)
⟦𝕊₂⟧ ⟦A⟧@(wn ν₁ R₁ , F₁) ⟦B⟧@(wn ν₂ R₂ , F₂)
    = wn (𝕊₂ ν₁ ν₂) (map appᵣ R₂ ⁀ map (appₗ ∘ appᵣ) R₁) , ⟦𝕊⟧ ⟦A⟧ ⟦B⟧

⟦𝕊₁⟧ : Red (α ⇒ β ⇒ γ) A -> Red ((α ⇒ β) ⇒ (α ⇒ γ)) (𝕊 ∙ A)
⟦𝕊₁⟧ ⟦A⟧@(wn ν R , F) = wn (𝕊₁ ν) (map appᵣ R) , ⟦𝕊₂⟧ ⟦A⟧

⟦𝕊₀⟧ : Red ((α ⇒ β ⇒ γ) ⇒ (α ⇒ β) ⇒ (α ⇒ γ)) 𝕊
⟦𝕊₀⟧ = wn 𝕊₀ refl , ⟦𝕊₁⟧

-- Now for the recursion operator. We first deal with the case
-- where the natural number argument is alreadly calculated.
⟦ℝ_⟧ : ∀ n -> Red α B -> Red (ℕ ⇒ α ⇒ α) C -> Red α (ℝ ∙ (# n) ∙ B ∙ C)
⟦ℝ zero ⟧ ⟦B⟧ ⟦C⟧ = RedCl (single (red ℝ0)) ⟦B⟧
⟦ℝ suc n ⟧ ⟦B⟧ ⟦C⟧ = RedCl (single (red ℝS)) $
    ⟦C⟧ .proj₂ ⟦# n ⟧ .proj₂ (⟦ℝ n ⟧ ⟦B⟧ ⟦C⟧)

-- The case where A may be neutral.
⟦ℝ⟧ : Red ℕ A -> Red α B -> Red (ℕ ⇒ α ⇒ α) C -> Red α (ℝ ∙ A ∙ B ∙ C)
⟦ℝ⟧ (wn (ℕ n) R , _) ⟦B⟧ ⟦C⟧ =
    RedCl (map (appₗ ∘ appₗ ∘ appᵣ) R) (⟦ℝ n ⟧ ⟦B⟧ ⟦C⟧)


⟦ℝ₂⟧ : Red ℕ A -> Red α B -> Red ((ℕ ⇒ α ⇒ α) ⇒ α) (ℝ ∙ A ∙ B)
⟦ℝ₂⟧ ⟦A⟧@(wn ν₁ R₁ , _) ⟦B⟧ with reify ⟦B⟧
... | wn ν₂ R₂ = wn (ℝ₂ ν₁ ν₂) (map appᵣ R₂ ⁀ map (appₗ ∘ appᵣ) R₁) , ⟦ℝ⟧ ⟦A⟧ ⟦B⟧

⟦ℝ₁⟧ : Red ℕ A -> Red (α ⇒ (ℕ ⇒ α ⇒ α) ⇒ α) (ℝ ∙ A)
⟦ℝ₁⟧ ⟦A⟧@(wn ν R , _) = wn (ℝ₁ ν) (map appᵣ R) , ⟦ℝ₂⟧ ⟦A⟧

⟦ℝ₀⟧ : Red (ℕ ⇒ α ⇒ (ℕ ⇒ α ⇒ α) ⇒ α) ℝ
⟦ℝ₀⟧ = wn ℝ₀ refl , ⟦ℝ₁⟧

-- Finally, we collect everything together.
-- Read as a theorem: Every term is reducible;
-- Read as a program: A program that calculates the meaning of the terms.
⟦_⟧ : ∀ A -> Red α A
⟦ A ∙ B ⟧ = ⟦ A ⟧ .proj₂ ⟦ B ⟧
⟦ 𝕂 ⟧ = ⟦𝕂₀⟧
⟦ 𝕊 ⟧ = ⟦𝕊₀⟧
⟦ ℝ ⟧ = ⟦ℝ₀⟧
⟦ O ⟧ = ⟦# 0 ⟧
⟦ S ⟧ = wn S₀ refl , ⟦S⟧

-- We can also get a normalizing function that throws away the proof.
normalize : Term α -> Term α
normalize A with reify ⟦ A ⟧
... | wn {B = B} _ _ = B

_ : normalize (Fact ∙ # 6) ≡ # 720
_ = refl

-- Recall that we defined Red in terms of WN. Actually, replacing WN with
-- SN, the proof also works, except for some tweaks. This then proves the
-- strong normalization theorem. It is left as an exercise for the reader.
