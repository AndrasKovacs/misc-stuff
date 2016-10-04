{-# OPTIONS --no-eta --without-K --rewriting #-}

module STLC.Cubical.LogPred.Model where

open import Level
open import STLC.Cubical.Lib
open import STLC.Cubical.Syntax
open import STLC.Cubical.Derived
open import STLC.Cubical.Elim
open import STLC.Cubical.Nf

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
_⇒ᴹ_ {A} Aᴹ {B} Bᴹ {Γ} t = (u : Tm Γ A) → Aᴹ u → Bᴹ (app t [ id ,ₛ u ])

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

_,ₛᴹ_ :
  ∀{Γ}{Γᴹ : Conᴹ Γ}{Δ}{Δᴹ : Conᴹ Δ}{δ : Tms Γ Δ} → Tmsᴹ Γᴹ Δᴹ δ
  → ∀{A}{Aᴹ : Tyᴹ A}{t : Tm Γ A} → Tmᴹ Γᴹ Aᴹ t → Tmsᴹ Γᴹ (Δᴹ ,ᴹ Aᴹ) (δ ,ₛ t)
_,ₛᴹ_ {Δᴹ = Δᴹ} δᴹ {Aᴹ = Aᴹ} {t} tᴹ Σ σ σᴹ =
    coe (ap Δᴹ ((ap π₁ ,∘ ◾ ,β₁) ⁻¹)) (δᴹ _ σ σᴹ)
  , coe (ap Aᴹ ((ap π₂ ,∘ ◾ ,β₂) ⁻¹)) (tᴹ _ σ σᴹ)

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




-- M : (∀ {Γ} → Tm Γ ι → Set) → Model {suc zero}{zero}
-- M ιᴹ = record
--       { Tyᴹ    = λ A → ∀ {Γ} → Tm Γ A → Set
--       ; Conᴹ   = λ Δ → ∀ {Γ} → Tms Γ Δ → Set
--       ; Tmsᴹ   = λ {θ} θᴹ {Δ} Δᴹ σ → ∀ Γ (δ : Tms Γ θ) → θᴹ δ → Δᴹ (σ ∘ δ)
--       ; Tmᴹ    = λ {θ} θᴹ {A} Aᴹ t → ∀ Γ (σ : Tms Γ θ) → θᴹ σ → Aᴹ (t [ σ ])
--       ; ιᴹ     = ιᴹ 
--       ; _⇒ᴹ_   = λ {A} Aᴹ {B} Bᴹ {Γ} t → (a : Tm Γ A) → Aᴹ a → Bᴹ (app t [ id ,ₛ a ])
--       ; ∙ᴹ     = λ _ → ⊤
--       ; _,ᴹ_   = λ Δᴹ Aᴹ σ → Δᴹ (π₁ σ) × Aᴹ (π₂ σ) 
--       ; idᴹ    = λ {Γ}{Γᴹ} Δ σ σᴹ → coe (ap Γᴹ (idl ⁻¹)) σᴹ
--       ; _∘ᴹ_   = λ {_}{_}{_}{_}{_}{Σᴹ} {σ} σᴹ {ν} νᴹ _ δ δᴹ → coe (ap Σᴹ (ass ⁻¹)) (σᴹ _ (ν ∘ δ) (νᴹ _ δ δᴹ))
--       ; εᴹ     = {!!}
--       ; _,ₛᴹ_  = {!!}
--       ; π₁ᴹ    = {!!}
--       ; _[_]ᴹ  = {!!}
--       ; π₂ᴹ    = {!!}
--       ; idlᴹ   = {!!}
--       ; idrᴹ   = {!!}
--       ; assᴹ   = {!!}
--       ; ,∘ᴹ    = {!!}
--       ; ,β₁ᴹ   = {!!}
--       ; ,ηᴹ    = {!!}
--       ; ∙ηᴹ    = {!!}
--       ; ,β₂ᴹ   = {!!}
--       ; lamᴹ   = {!!}
--       ; appᴹ   = {!!}
--       ; lam[]ᴹ = {!!}
--       ; ⇒βᴹ    = {!!}
--       ; ⇒ηᴹ    = {!!}
--       }
