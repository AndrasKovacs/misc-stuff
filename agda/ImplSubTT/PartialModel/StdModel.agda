{-# OPTIONS --without-K #-}

module StdModel where

open import Lib
open import Syntax
open import Embedding
open import Substitution
open import Conversion
open import Typing
open import Sanity

open import Data.Maybe
open import Category.Monad
open module MaybeMonad {α} = RawMonad {α} Data.Maybe.monad

import Level as L

Ty≡? : ∀ {n} (A A' : Ty n) → (A ≡ A') ⊎ (A ≡ A' → ⊥)
Ty≡? = {!!}

-- first try to do it without Maybe
module M (Uᴹ : Set)(Elᴹ : Uᴹ → Set) where


  Conᴹ : ∀ {n} → Con n → Set
  Tyᴹ  : ∀ {n} Γ → Ty n → Conᴹ {n} Γ → Set
  ∈ᴹ   : ∀ {n} Γ A → Fin n → (γ : Conᴹ {n} Γ) → Tyᴹ Γ A γ
  OPEᴹ : ∀ {n m} (Γ : Con n)(Δ : Con m) → OPE n m → Conᴹ Γ → Conᴹ Δ
  Subᴹ : ∀ {n m} (Γ : Con n)(Δ : Con m) → Sub n m → Conᴹ Γ → Conᴹ Δ
  Tmᴹ  : ∀ {n} Γ A → Tm n → (γ : Conᴹ {n} Γ) → Tyᴹ Γ A γ
  {-# TERMINATING #-}
  Tyₑᴹ : ∀ {n m Γ Δ}(σ : OPE n m) A γ  → Tyᴹ Γ (Tyₑ σ A) γ ≡ Tyᴹ Δ A (OPEᴹ Γ Δ σ γ)
  Tmₑᴹ :
    ∀ {n m Γ}{Δ : Con m}{A}(σ : OPE n m) t γ
    → Tmᴹ Γ (Tyₑ σ A) (Tmₑ σ t) γ ≡ coe (Tyₑᴹ σ A γ ⁻¹) (Tmᴹ Δ A t (OPEᴹ Γ Δ σ γ))

  Conᴹ ∙       = ⊤
  Conᴹ (Γ ▷ A) = Σ (Conᴹ Γ) (Tyᴹ Γ A)

  Tyᴹ Γ U       γ = Uᴹ
  Tyᴹ Γ (El t)  γ = Elᴹ (Tmᴹ Γ U t γ)
  Tyᴹ Γ (Π A B) γ = (α : Tyᴹ Γ A γ) → Tyᴹ (Γ ▷ A) B (γ , α)

  OPEᴹ Γ       ∙        ∙        γ = tt
  OPEᴹ (Γ ▷ A) Δ        (drop σ) (γ , t) = OPEᴹ Γ Δ σ γ
  OPEᴹ (Γ ▷ A) (Δ ▷ A') (keep σ) (γ , t) =
    either
     (λ p → OPEᴹ Γ Δ σ γ , coe ((λ x → Tyᴹ Γ x γ) & p ◾ Tyₑᴹ σ A' γ) t)
     undef (Ty≡? A (Tyₑ σ A'))
    where postulate undef : _

  Subᴹ Γ ∙       ∙       γ = tt
  Subᴹ Γ (Δ ▷ A) (σ , t) γ = Subᴹ Γ Δ σ γ , coe {!!} (Tmᴹ Γ (Tyₛ σ A) t γ)  -- Tyₛᴹ

  ∈ᴹ (Γ ▷ A) A' zero (γ , t) =
    either
       (λ p → coe
         -- wtf Agda
         (({!OPEᴹ (Γ ▷ A) Γ (drop idₑ) (γ , t)!} ◾ Tyₑᴹ {Γ = Γ ▷ A}{Γ} wk A (γ , t) ⁻¹) ◾ (λ x → Tyᴹ (Γ ▷ A) x (γ , t)) & p ⁻¹)
         t)
       undef
       (Ty≡? A' (Tyₑ wk A))
    where postulate undef : _
  ∈ᴹ (Γ ▷ A) A' (suc x) (γ , t) = {!!}

  Tmᴹ Γ A (var x) γ = ∈ᴹ Γ A x γ
  Tmᴹ Γ U       (lam t)   γ = undef where postulate undef : _
  Tmᴹ Γ (El _)  (lam t)   γ = undef where postulate undef : _
  Tmᴹ Γ (Π A B) (lam t)   γ = λ α → Tmᴹ (Γ ▷ A) B t (γ , α)
  Tmᴹ Γ A (app A' B' t u) γ =
    either
      (λ p → coe ({!!} ◾ (λ x → Tyᴹ Γ x γ) & p ⁻¹) (Tmᴹ Γ (Π A' B') t γ (Tmᴹ Γ A' u γ)))
      undef
      (Ty≡? A (Tyₛ (idₛ , u) B'))
    where postulate undef : _

  Tyₑᴹ σ U       γ = refl
  Tyₑᴹ {Γ = Γ} {Δ} σ (El t) γ = Elᴹ & Tmₑᴹ {Γ = Γ}{Δ}{U} σ t γ
  Tyₑᴹ {Γ = Γ} {Δ} σ (Π A B) γ = {!!}

  -- with Ty≡? (Tyₑ σ A) (Tyₑ σ A)
  --     ... | inl p = Π-≡ (Tyₑᴹ σ A γ) (λ α → {!Tyₑᴹ {Γ = Γ ▷ Tyₑ σ A}{Δ ▷ A}(keep σ) B (γ , α)!})
  --     ... | inr p = {!!}
  -- Π-≡ (Tyₑᴹ σ A γ) (λ α → {!Tyₑᴹ {Γ = Γ ▷ Tyₑ σ A}{Δ ▷ A}(keep σ) B (γ , α)!})

  Tmₑᴹ σ (var x)       γ = {!!}
  Tmₑᴹ σ (lam t)       γ = {!!}
  Tmₑᴹ σ (app A B t u) γ = {!!}

-- -- sanity: I don't quite know?
-- data Sub⊢ {n}(Γ : Con n) : ∀ {m} → Con m → Sub n m → Set where
--   ∙    : Γ ⊢ → Sub⊢ Γ ∙ ∙
--   cons : ∀ {m Δ A t σ} → Γ ⊢ t ∈ Tyₛ σ A → Sub⊢ Γ {m} Δ σ → Sub⊢ Γ (Δ ▷ A) (σ , t)

-- -- sanity: if (Δ ⊢) and (OPE⊢ Γ Δ σ), then (Γ ⊢)
-- data OPE⊢ : ∀ {n m} → Con n → Con m → OPE n m → Set where
--   ∙    : OPE⊢ ∙ ∙ ∙
--   drop : ∀ {n m Γ Δ A σ} → Γ ⊢ A → OPE⊢ {n}{m} Γ Δ σ → OPE⊢ (Γ ▷ A) Δ (drop σ)
--   keep : ∀ {n m Γ Δ A σ} → OPE⊢ {n}{m} Γ Δ σ → OPE⊢ (Γ ▷ Tyₑ σ A) (Δ ▷ A) (keep σ)
