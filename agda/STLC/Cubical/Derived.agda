{-# OPTIONS --rewriting #-}

module STLC.Cubical.Derived where

open import STLC.Cubical.Lib
open import STLC.Cubical.Syntax

abstract
  [id] : ∀{Γ A}{t : Tm Γ A} → t [ id ] ≡ t
  [id] {t = t} =
    t [ id ]                 ≡⟨ ,β₂ ⁻¹ ⟩
    π₂ (id ∘ id ,ₛ t [ id ]) ≡⟨ ap π₂ (,∘ ⁻¹) ⟩
    π₂ ((id ,ₛ t) ∘ id)      ≡⟨ ap π₂ idr ⟩
    π₂ (id ,ₛ t)             ≡⟨ ,β₂ ⟩
    t ∎

  [][] : ∀ {Γ Δ Σ A}{t : Tm Σ A}{σ : Tms Γ Δ}{δ : Tms Δ Σ}
          → t [ δ ] [ σ ] ≡ t [ δ ∘ σ ]
  [][] {t = t}{σ}{δ} =
    t [ δ ] [ σ ]                      ≡⟨ ,β₂ ⁻¹ ⟩
    π₂ ((id ∘ δ) ∘ σ ,ₛ t [ δ ] [ σ ]) ≡⟨ ap π₂ (,∘ ⁻¹) ⟩
    π₂ ((id ∘ δ ,ₛ t [ δ ]) ∘ σ)       ≡⟨ ap (λ x → π₂ (x ∘ σ)) (,∘ ⁻¹) ⟩
    π₂ (((id ,ₛ t) ∘ δ) ∘ σ)           ≡⟨ ap π₂ ass ⟩
    π₂ ((id ,ₛ t) ∘ (δ ∘ σ))           ≡⟨ ap π₂ ,∘ ⟩
    π₂ (id ∘ (δ ∘ σ) ,ₛ t [ δ ∘ σ ])   ≡⟨ ,β₂ ⟩
    t [ δ ∘ σ ] ∎

  π₁∘ :
    ∀ {Γ Δ Σ A}{σ : Tms Γ (Δ , A)}{δ : Tms Σ Γ}
    → π₁ σ ∘ δ ≡ π₁ (σ ∘ δ)
  π₁∘ {σ = σ}{δ} = ,β₁ ⁻¹ ◾ ap π₁ (,∘ ⁻¹) ◾ ap (λ σ → π₁ (σ ∘ δ)) ,η

  π₂[] :
    ∀ {Γ Δ Σ A}{σ : Tms Γ (Δ , A)}{δ : Tms Σ Γ}
    → π₂ σ [ δ ] ≡ π₂ (σ ∘ δ)
  π₂[] {σ = σ}{δ} = ,β₂ ⁻¹ ◾ ap π₂ (,∘ ⁻¹) ◾ ap (λ σ → π₂ (σ ∘ δ)) ,η

  π₁id∘ :
    ∀ {Γ Δ A}{σ : Tms Γ (Δ , A)}
    → π₁ id ∘ σ ≡ π₁ σ
  π₁id∘ = π₁∘ ◾ ap π₁ idl

  π₂idβ :
    ∀ {Γ Δ A}{σ : Tms Γ Δ}{t : Tm Γ A}
    → π₂ id [ σ ,ₛ t ] ≡ t
  π₂idβ = π₂[] ◾ ap π₂ idl ◾ ,β₂

  app[] :
    ∀ {Γ Δ A B}{σ : Tms Γ Δ}{t : Tm Δ (A ⇒ B)}
    → app (t [ σ ]) ≡ (app t) [ σ ^ A ]
  app[] {σ = σ} = ap (λ x → app (x [ σ ])) (⇒η ⁻¹) ◾ ap app lam[] ◾ ⇒β

  ,ₛ≡ :
    ∀ {Γ Δ}{σ σ' : Tms Γ Δ}(p : σ ≡ σ'){A : Ty}{t t' : Tm Γ A}(q : t ≡ t')
    → σ ,ₛ t ≡ σ' ,ₛ t'
  ,ₛ≡ p q = ⟨ i ⟩ (p $ i) ,ₛ (q $ i) 

  ,ₛ-lam :
    ∀ {Γ Δ A B}{t : Tm (Γ , A) B}{σ : Tms Δ Γ}{a : Tm Δ A}
    → t [ σ ,ₛ a ] ≡ app (lam t [ σ ]) [ id ,ₛ a ]
  ,ₛ-lam {t = t}{σ}{a} = (
      ap (λ x → app x [ id ,ₛ a ]) lam[]
    ◾ ap (_[ id ,ₛ a ]) ⇒β
    ◾ [][]
    ◾ ap (t [_]) (
      ,∘ ◾ ,ₛ≡ (ass ◾ ap (σ ∘_) (π₁id∘ ◾ ,β₁) ◾ idr) π₂idβ)
    ) ⁻¹

  split-app :
    ∀ {Γ Δ A B}{σ : Tms Δ (Γ , A)}{t : Tm Γ (A ⇒ B)}
    → app (t [ π₁ σ ]) [ id ,ₛ π₂ σ ] ≡ app t [ σ ]
  split-app {σ = σ}{t} =
      ap (_[ id ,ₛ π₂ σ ]) app[]
    ◾ [][]
    ◾ ap (app t [_]) (
        ,∘ ◾ ,ₛ≡ (ass ◾ (ap (π₁ σ ∘_) (π₁id∘ ◾ ,β₁) ◾ idr)) π₂idβ ◾ ,η)


