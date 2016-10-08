{-# OPTIONS --no-eta --without-K #-}

module STLC.Norm.Methods1 where

open import STLC.lib
open import STLC.Derived
open import STLC.Syntax
open import STLC.Nf
open import STLC.Renaming

infixl 5 _,ᴹ_
infixl 4 _⇒ᴹ_
infixl 5 _,ₛᴹ_
infix  6 _∘ᴹ_
infixl 8 _[_]ᴹ

_∸>_ : ∀ {α β γ}{I : Set α} → (I → Set β) → (I → Set γ) → Set _
A ∸> B = ∀ {i} → A i → B i

Tyᴹ : Ty → Set₁
Tyᴹ A = ∀ {Γ} → Tm Γ A → Set

Conᴹ : Con → Set₁
Conᴹ Δ = ∀ {Γ} → Tms Γ Δ → Set

Tmsᴹ : ∀ {Γ} → Conᴹ Γ → ∀{Δ} → Conᴹ Δ → Tms Γ Δ → Set
Tmsᴹ {θ} θᴹ {Δ} Δᴹ σ = ∀ Γ (δ : Tms Γ θ) → θᴹ δ → Δᴹ (σ ∘ δ)

Tmᴹ : ∀ {Γ} → Conᴹ Γ → ∀{A} → Tyᴹ A → Tm Γ A → Set
Tmᴹ {θ} θᴹ {A} Aᴹ t = ∀ Γ (σ : Tms Γ θ) → θᴹ σ → Aᴹ (t [ σ ])

ιᴹ : Tyᴹ ι
ιᴹ {Γ} t = Σ (Nf Γ ι) λ n → ⌜ n ⌝ ≡ t

_⇒ᴹ_ : ∀ {A} → Tyᴹ A → ∀ {B} → Tyᴹ B → Tyᴹ (A ⇒ B)
_⇒ᴹ_ {A} Aᴹ {B} Bᴹ {Γ} t = ∀ Δ (r : Γ ⊆ Δ) → (a : Tm Δ A) → Aᴹ a → Bᴹ (app t [ sub r ,ₛ a ])

∙ᴹ : Conᴹ ∙
∙ᴹ _ = ⊤

_,ᴹ_ : ∀ {Γ} → Conᴹ Γ → ∀ {A} → Tyᴹ A → Conᴹ (Γ , A)
_,ᴹ_ Δᴹ Aᴹ σ = Δᴹ (π₁ σ) × Aᴹ (π₂ σ)

idᴹ : ∀ {Γ}{Γᴹ : Conᴹ Γ} → Tmsᴹ Γᴹ Γᴹ (id {Γ})
idᴹ {Γ}{Γᴹ} Δ σ = coe (ap Γᴹ (idl ⁻¹))

_∘ᴹ_ :
  ∀ {Γ}{Γᴹ : Conᴹ Γ}{Δ}{Δᴹ : Conᴹ Δ}{Σ}{Σᴹ : Conᴹ Σ}
  → {σ : Tms Δ Σ} → Tmsᴹ Δᴹ Σᴹ σ → {ν : Tms Γ Δ} → Tmsᴹ Γᴹ Δᴹ ν → Tmsᴹ Γᴹ Σᴹ (σ ∘ ν)
_∘ᴹ_ {Σᴹ = Σᴹ} {σ} σᴹ {ν} νᴹ _ δ δᴹ = coe (ap Σᴹ (ass ⁻¹)) (σᴹ _ (ν ∘ δ) (νᴹ _ δ δᴹ))

εᴹ : ∀{Γ}{Γᴹ : Conᴹ Γ} → Tmsᴹ Γᴹ ∙ᴹ ε
εᴹ _ _ _ = tt

,ₛᴹ-coe :
  ∀ {Γ Δ}(Δᴹ : Conᴹ Δ){δ : Tms Γ Δ}
    {A}(Aᴹ : Tyᴹ A){t : Tm Γ A}{Σ}{σ : Tms Σ Γ}
  → (Δᴹ (δ ∘ σ) × Aᴹ (t [ σ ])) ≡ (Δᴹ (π₁ ((δ ,ₛ t) ∘ σ)) × Aᴹ (π₂ ((δ ,ₛ t) ∘ σ)))
,ₛᴹ-coe Δᴹ Aᴹ = ap2 _×_  (ap Δᴹ ((ap π₁ ,∘ ◾ ,β₁) ⁻¹)) (ap Aᴹ ((ap π₂ ,∘ ◾ ,β₂) ⁻¹))

_,ₛᴹ_ :
  ∀{Γ}{Γᴹ : Conᴹ Γ}{Δ}{Δᴹ : Conᴹ Δ}{δ : Tms Γ Δ} → Tmsᴹ Γᴹ Δᴹ δ
  → ∀{A}{Aᴹ : Tyᴹ A}{t : Tm Γ A} → Tmᴹ Γᴹ Aᴹ t → Tmsᴹ Γᴹ (Δᴹ ,ᴹ Aᴹ) (δ ,ₛ t)
_,ₛᴹ_ {Δᴹ = Δᴹ} δᴹ {Aᴹ = Aᴹ} {t} tᴹ Σ σ σᴹ = coe (,ₛᴹ-coe Δᴹ Aᴹ) (δᴹ _ σ σᴹ , tᴹ _ σ σᴹ)

_[_]ᴹ  :
  ∀ {Γ}{Γᴹ : Conᴹ Γ}{Δ}{Δᴹ : Conᴹ Δ}{A}{Aᴹ : Tyᴹ A}{t : Tm Δ A}
  → Tmᴹ Δᴹ Aᴹ t → {δ : Tms Γ Δ} → Tmsᴹ Γᴹ Δᴹ δ → Tmᴹ Γᴹ Aᴹ (t [ δ ])
_[_]ᴹ {Aᴹ = Aᴹ} tᴹ {δ} δᴹ _ σ σᴹ = coe (ap Aᴹ ([][] ⁻¹)) (tᴹ _ (δ ∘ σ) (δᴹ _ σ σᴹ))

π₁ᴹ :
  ∀{Γ}{Γᴹ : Conᴹ Γ}{Δ}{Δᴹ : Conᴹ Δ}{A}{Aᴹ : Tyᴹ A}{δ : Tms Γ (Δ , A)}
  → Tmsᴹ Γᴹ (Δᴹ ,ᴹ Aᴹ) δ → Tmsᴹ Γᴹ Δᴹ (π₁ δ)
π₁ᴹ {Δᴹ = Δᴹ}{δ = δ} δᴹ Σ σ σᴹ = coe (ap Δᴹ (π₁∘ ⁻¹)) (proj₁ (δᴹ _ σ σᴹ))

π₂ᴹ :
  ∀ {Γ}{Γᴹ : Conᴹ Γ}{Δ}{Δᴹ : Conᴹ Δ}{A}{Aᴹ : Tyᴹ A}{δ : Tms Γ (Δ , A)}
  → Tmsᴹ Γᴹ (Δᴹ ,ᴹ Aᴹ) δ → Tmᴹ Γᴹ Aᴹ (π₂ δ)
π₂ᴹ {Aᴹ = Aᴹ}{δ = δ} δᴹ _ σ σᴹ = coe (ap Aᴹ (π₂[] ⁻¹)) (proj₂ (δᴹ _ σ σᴹ))


