{-# OPTIONS --without-K #-}

open import Lib

-- Ordered LC

data Ty : Set where
  ι : Ty
  _⊸_ : Ty → Ty → Ty
infixr 4 _⊸_

data Con : Set where
  ∙   : Con
  _▷_ : Con → Ty → Con
infixl 5 _▷_

_++_ : Con → Con → Con
Γ ++ ∙       = Γ
Γ ++ (Δ ▷ A) = (Γ ++ Δ) ▷ A
infixr 5 _++_

∙++ : ∀ Γ → ∙ ++ Γ ≡ Γ
∙++ ∙       = refl
∙++ (Γ ▷ A) = (_▷ A) & ∙++ Γ

++assoc : ∀ Γ Δ Σ → (Γ ++ Δ) ++ Σ ≡ Γ ++ Δ ++ Σ
++assoc Γ Δ ∙       = refl
++assoc Γ Δ (Σ ▷ A) = (_▷ A) & ++assoc Γ Δ Σ

data Tm : Con → Ty → Set where
  var   : ∀ {A} → Tm (∙ ▷ A) A
  lam   : ∀ {Γ A B} → Tm (Γ ▷ A) B → Tm Γ (A ⊸ B)
  app   : ∀ {Γ Δ A B} → Tm Γ (A ⊸ B) → Tm Δ A → Tm (Γ ++ Δ) B

data _∈_ A : Con → Set where
  vz : ∀ {Γ} → A ∈ (Γ ▷ A)
  vs : ∀ {Γ B} → A ∈ Γ → A ∈ (Γ ▷ B)

data Sub : Con → Con → Set where
  ∙   : Sub ∙ ∙
  _▷_ : ∀ {Γ Δ Σ A} → Sub Γ Δ → Tm Σ A → Sub (Γ ++ Σ) (Δ ▷ A)

π₂ : ∀ {Γ A} → Sub Γ (∙ ▷ A) → Tm Γ A
π₂ {A = A} (_▷_ {Σ = Σ} ∙ t) = coe ((λ x → Tm x A) & (∙++ Σ ⁻¹)) t

splitₛ :
  ∀ {Γ Δ} Σ → Sub Γ (Δ ++ Σ)
  → ∃₂ λ Γ₀ Γ₁ → (Γ ≡ (Γ₀ ++ Γ₁)) × Sub Γ₀ Δ × Sub Γ₁ Σ
splitₛ {Γ} {Δ} ∙        σ      = Γ , ∙ , refl , σ , ∙
splitₛ (Σ ▷ A) (_▷_ {Γ} {Σ = Ξ} σ t) with splitₛ Σ σ
... | Γ₀ , Γ₁ , refl , σ₀ , σ₁ = Γ₀ , (Γ₁ ++ Ξ) , ++assoc Γ₀ Γ₁ Ξ , σ₀ , (σ₁ ▷ t)

Tmₛ : ∀ {Γ Δ A} → Sub Γ Δ → Tm Δ A → Tm Γ A
Tmₛ σ var       = π₂ σ
Tmₛ σ (lam t)   = lam (Tmₛ (σ ▷ var) t)
Tmₛ σ (app {Δ = Δ} t u) with splitₛ Δ σ
... | _ , _ , refl , σ₀ , σ₁ = app (Tmₛ σ₀ t) (Tmₛ σ₁ u)

idₛ : ∀ {Γ} → Sub Γ Γ
idₛ {∙}     = ∙
idₛ {Γ ▷ A} = idₛ {Γ} ▷ var

infixr 5 _∘ₛ_
_∘ₛ_ : ∀ {Γ Δ Σ} → Sub Δ Σ → Sub Γ Δ → Sub Γ Σ
∙       ∘ₛ δ = δ
_∘ₛ_ (_▷_ {Σ = Ξ} σ t) δ with splitₛ Ξ δ
... | _ , _ , refl , δ₀ , δ₁ = (σ ∘ₛ δ₀) ▷ Tmₛ δ₁ t

--------------------------------------------------------------------------------
