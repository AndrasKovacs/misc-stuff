{-# OPTIONS --no-eta --without-K --rewriting #-}

module STLC.Cubical.LogPred.Methods3 where

open import Level
open import STLC.Cubical.Lib
open import STLC.Cubical.Syntax
open import STLC.Cubical.Derived
open import STLC.Cubical.Elim
open import STLC.Cubical.Nf

open import STLC.Cubical.LogPred.Methods1

,∘ᴹ :
  ∀ {Γ} {Γᴹ : Conᴹ Γ} {Δ} {Δᴹ : Conᴹ Δ}
    {Σ} {Σᴹ : Conᴹ Σ} {δ : Tms Γ Δ} {δᴹ : Tmsᴹ Γᴹ Δᴹ δ}
    {σ : Tms Σ Γ} {σᴹ : Tmsᴹ Σᴹ Γᴹ σ} {A} {Aᴹ : Tyᴹ A}
    {a} {aᴹ : Tmᴹ Γᴹ Aᴹ a}
    -- (δᴹ ,ₛᴹ aᴹ) ∘ᴹ σᴹ ≡[ ap (Tmsᴹ Σᴹ (Δᴹ ,ᴹ Aᴹ)) ,∘ ]≡ δᴹ ∘ᴹ σᴹ ,ₛᴹ aᴹ [ σᴹ ]ᴹ
    → _∘ᴹ_ {Σᴹ = Δᴹ ,ᴹ Aᴹ} (_,ₛᴹ_ {Δᴹ = Δᴹ} δᴹ {Aᴹ = Aᴹ} aᴹ) σᴹ
        ≡[ ap (Tmsᴹ Σᴹ (Δᴹ ,ᴹ Aᴹ)) ,∘ ]≡
      _,ₛᴹ_ {Δᴹ = Δᴹ} (_∘ᴹ_ {Σᴹ = Δᴹ} δᴹ σᴹ) {Aᴹ = Aᴹ} (_[_]ᴹ {Aᴹ = Aᴹ} aᴹ σᴹ)

,∘ᴹ {Γ}{Γᴹ}{Δ}{Δᴹ}{Σ}{Σᴹ}{δ}{δᴹ}{σ}{σᴹ}{A}{Aᴹ}{a}{aᴹ} = {!!}


,β₁ᴹ :
  ∀ {Γ} {Γᴹ : Conᴹ Γ} {Δ} {Δᴹ : Conᴹ Δ} {A}{Aᴹ : Tyᴹ A}
    {δ : Tms Γ Δ} {δᴹ : Tmsᴹ Γᴹ Δᴹ δ} {a : Tm Γ A}{aᴹ : Tmᴹ Γᴹ Aᴹ a}
    -- π₁ᴹ (δᴹ ,ₛᴹ aᴹ) ≡[ ap (Tmsᴹ Γᴹ Δᴹ) ,β₁ ]≡ δᴹ
    → π₁ᴹ {Δᴹ = Δᴹ}{Aᴹ = Aᴹ} (_,ₛᴹ_ {Δᴹ = Δᴹ} δᴹ {Aᴹ = Aᴹ} aᴹ) ≡[ ap (Tmsᴹ Γᴹ Δᴹ) ,β₁ ]≡ δᴹ

,β₁ᴹ {Γ}{Γᴹ}{Δ}{Δᴹ}{A}{Aᴹ}{δ}{δᴹ}{a}{aᴹ} = {!!}

  -- ,ₛ-lam :
  --   ∀ {Γ Δ A B}{t : Tm (Γ , A) B}{σ : Tms Δ Γ}{a : Tm Δ A}
  --   → t [ σ ,ₛ a ] ≡ app (lam t [ σ ]) [ id ,ₛ a ]
  -- ,ₛ-lam {t = t}{σ}{a} = (
  --     ap (λ x → app x [ id ,ₛ a ]) lam[]
  --   ◾ ap (_[ id ,ₛ a ]) ⇒β
  --   ◾ [][]
  --   ◾ ap (t [_]) (
  --     ,∘ ◾ ,ₛ≡ (ass ◾ ap (σ ∘_) (π₁id∘ ◾ ,β₁) ◾ idr) π₂idβ)
  --   ) ⁻¹

  -- split-app :
  --   ∀ {Γ Δ A B}{σ : Tms Δ (Γ , A)}{t : Tm Γ (A ⇒ B)}
  --   → app (t [ π₁ σ ]) [ id ,ₛ π₂ σ ] ≡ app t [ σ ]
  -- split-app {σ = σ}{t} =
  --     ap (_[ id ,ₛ π₂ σ ]) app[]
  --   ◾ [][]
  --   ◾ ap (app t [_]) (
  --       ,∘ ◾ ,ₛ≡ (ass ◾ (ap (π₁ σ ∘_) (π₁id∘ ◾ ,β₁) ◾ idr)) π₂idβ ◾ ,η)


,β₂ᴹ :
  ∀ {Γ} {Γᴹ : Conᴹ Γ} {Δ} {Δᴹ : Conᴹ Δ} {A}{Aᴹ : Tyᴹ A}
    {δ : Tms Γ Δ} {δᴹ : Tmsᴹ Γᴹ Δᴹ δ} {a}{aᴹ : Tmᴹ Γᴹ Aᴹ a}
  -- π₂ᴹ (δᴹ ,ₛᴹ aᴹ) ≡[ ap (Tmᴹ Γᴹ Aᴹ) ,β₂ ]≡ aᴹ
  → π₂ᴹ {Δᴹ = Δᴹ}{Aᴹ = Aᴹ}(_,ₛᴹ_ {Δᴹ = Δᴹ} δᴹ {Aᴹ = Aᴹ} aᴹ) ≡[ ap (Tmᴹ Γᴹ Aᴹ) ,β₂ ]≡ aᴹ
,β₂ᴹ {Γ}{Γᴹ}{Δ}{Δᴹ}{A}{Aᴹ}{δ}{δᴹ}{a}{aᴹ} = {!!}


lamᴹ :
  ∀ {Γ} {Γᴹ : Conᴹ Γ} {A} {Aᴹ : Tyᴹ A} {B} {Bᴹ : Tyᴹ B} {t : Tm (Γ , A) B}
  → Tmᴹ (Γᴹ ,ᴹ Aᴹ) Bᴹ t → Tmᴹ Γᴹ (Aᴹ ⇒ᴹ Bᴹ) (lam t)
lamᴹ {Γ}{Γᴹ}{A}{Aᴹ}{B}{Bᴹ} {t} tᴹ Δ σ σᴹ a aᴹ =
  coe (ap Bᴹ ,ₛ-lam) (tᴹ _ (σ ,ₛ a) (coe (ap Γᴹ (,β₁ ⁻¹)) σᴹ , coe (ap Aᴹ (,β₂ ⁻¹)) aᴹ))

appᴹ :
  ∀ {Γ} {Γᴹ : Conᴹ Γ} {A} {Aᴹ : Tyᴹ A} {B}{Bᴹ : Tyᴹ B}
    {t : Tm Γ (A ⇒ B)}
  → Tmᴹ Γᴹ (Aᴹ ⇒ᴹ Bᴹ) t → Tmᴹ (Γᴹ ,ᴹ Aᴹ) Bᴹ (app t)
appᴹ {Γ}{Γᴹ}{A}{Aᴹ}{B}{Bᴹ}{t} tᴹ Δ σ (π₁σᴹ , π₂σᴹ) =
  coe (ap Bᴹ split-app) (tᴹ _ (π₁ σ) π₁σᴹ (π₂ σ) π₂σᴹ)


lam[]ᴹ :
  ∀ {Γ} {Γᴹ : Conᴹ Γ} {Δ} {Δᴹ : Conᴹ Δ} {δ : Tms Γ Δ}
    {δᴹ : Tmsᴹ Γᴹ Δᴹ δ} {A} {Aᴹ : Tyᴹ A} {B} {Bᴹ : Tyᴹ B}
    {t : Tm (Δ , A) B} {tᴹ : Tmᴹ (Δᴹ ,ᴹ Aᴹ) Bᴹ t}

  --           lamᴹ tᴹ [ δᴹ ]ᴹ
  --    ≡[ ap (Tmᴹ Γᴹ (Aᴹ ⇒ᴹ Bᴹ)) lam[] ]≡
  -- lamᴹ (tᴹ [ δᴹ ∘ᴹ π₁ᴹ idᴹ ,ₛᴹ π₂ᴹ idᴹ ]ᴹ)

  →  _[_]ᴹ {Aᴹ = Aᴹ ⇒ᴹ Bᴹ} (lamᴹ {Γᴹ = Δᴹ}{Bᴹ = Bᴹ} tᴹ) δᴹ
          ≡[ ap (Tmᴹ Γᴹ (Aᴹ ⇒ᴹ Bᴹ)) lam[] ]≡
     lamᴹ {Bᴹ = Bᴹ} (_[_]ᴹ {Aᴹ = Bᴹ} tᴹ
       (_,ₛᴹ_ {Δᴹ = Δᴹ} (_∘ᴹ_ {Σᴹ = Δᴹ} δᴹ (π₁ᴹ{Δᴹ = Γᴹ}{Aᴹ = Aᴹ} idᴹ))
         {Aᴹ = Aᴹ} (π₂ᴹ {Δᴹ = Γᴹ}{Aᴹ = Aᴹ} idᴹ)))

lam[]ᴹ {Γ}{Γᴹ}{Δ}{Δᴹ}{δ}{δᴹ}{A}{Aᴹ}{B}{Bᴹ}{t}{tᴹ} = {!!}
