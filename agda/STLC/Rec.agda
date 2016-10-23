{-# OPTIONS --without-K --no-eta --rewriting #-}

module Rec where

open import Level
open import Lib
open import Syntax

record Model {i j} : Set (suc (i ⊔ j)) where
  field
    Tyᴹ    : Set i
    Conᴹ   : Set i
    Tmsᴹ   : Conᴹ → Conᴹ → Set j
    Tmᴹ    : Conᴹ → Tyᴹ → Set j
    ιᴹ     : Tyᴹ
    _⇒ᴹ_   : Tyᴹ → Tyᴹ → Tyᴹ
    ∙ᴹ     : Conᴹ
    _,ᴹ_   : Conᴹ → Tyᴹ → Conᴹ
    idᴹ    : ∀{Γᴹ} → Tmsᴹ Γᴹ Γᴹ
    _∘ᴹ_   : ∀{Γᴹ Δᴹ Σᴹ} → Tmsᴹ Δᴹ Σᴹ → Tmsᴹ Γᴹ Δᴹ → Tmsᴹ Γᴹ Σᴹ
    εᴹ     : ∀{Γᴹ} → Tmsᴹ Γᴹ ∙ᴹ
    _,ₛᴹ_  : ∀{Γᴹ Δᴹ}(δᴹ : Tmsᴹ Γᴹ Δᴹ){Aᴹ : Tyᴹ} → Tmᴹ Γᴹ Aᴹ → Tmsᴹ Γᴹ (Δᴹ ,ᴹ Aᴹ)
    π₁ᴹ    : ∀{Γᴹ Δᴹ}{Aᴹ : Tyᴹ} → Tmsᴹ Γᴹ (Δᴹ ,ᴹ Aᴹ) → Tmsᴹ Γᴹ Δᴹ
    _[_]ᴹ  : ∀{Γᴹ Δᴹ}{Aᴹ : Tyᴹ} → Tmᴹ Δᴹ Aᴹ → Tmsᴹ Γᴹ Δᴹ → Tmᴹ Γᴹ Aᴹ
    π₂ᴹ    : ∀{Γᴹ Δᴹ}{Aᴹ : Tyᴹ} → Tmsᴹ Γᴹ (Δᴹ ,ᴹ Aᴹ) → Tmᴹ Γᴹ Aᴹ
    idlᴹ   : ∀{Γᴹ Δᴹ}{δᴹ : Tmsᴹ Γᴹ Δᴹ} → idᴹ ∘ᴹ δᴹ ≡ δᴹ
    idrᴹ   : ∀{Γᴹ Δᴹ}{δᴹ : Tmsᴹ Γᴹ Δᴹ} → δᴹ ∘ᴹ idᴹ ≡ δᴹ
    assᴹ   : ∀{Δᴹ Γᴹ Σᴹ Ωᴹ}{σᴹ : Tmsᴹ Σᴹ Ωᴹ}{δᴹ : Tmsᴹ Γᴹ Σᴹ}{νᴹ : Tmsᴹ Δᴹ Γᴹ}
             → (σᴹ ∘ᴹ δᴹ) ∘ᴹ νᴹ ≡ σᴹ ∘ᴹ (δᴹ ∘ᴹ νᴹ)
    ,∘ᴹ    : ∀{Γᴹ Δᴹ Σᴹ}{δᴹ : Tmsᴹ Γᴹ Δᴹ}{σᴹ : Tmsᴹ Σᴹ Γᴹ}{Aᴹ : Tyᴹ}{aᴹ : Tmᴹ Γᴹ Aᴹ}
             → (δᴹ ,ₛᴹ aᴹ) ∘ᴹ σᴹ ≡ (δᴹ ∘ᴹ σᴹ) ,ₛᴹ aᴹ [ σᴹ ]ᴹ
    ,β₁ᴹ   : ∀{Γᴹ Δᴹ}{Aᴹ : Tyᴹ}{δᴹ : Tmsᴹ Γᴹ Δᴹ}{aᴹ : Tmᴹ Γᴹ Aᴹ}
             → π₁ᴹ (δᴹ ,ₛᴹ aᴹ) ≡ δᴹ
    ,ηᴹ    : ∀{Γᴹ Δᴹ}{Aᴹ : Tyᴹ}{δᴹ : Tmsᴹ Γᴹ (Δᴹ ,ᴹ Aᴹ)}
             → π₁ᴹ δᴹ ,ₛᴹ π₂ᴹ δᴹ ≡ δᴹ
    ∙ηᴹ    : ∀{Γᴹ}{σᴹ : Tmsᴹ Γᴹ ∙ᴹ}
             → σᴹ ≡ εᴹ
    ,β₂ᴹ   : ∀{Γᴹ Δᴹ}{Aᴹ : Tyᴹ}{δᴹ : Tmsᴹ Γᴹ Δᴹ}{aᴹ : Tmᴹ Γᴹ Aᴹ}
             → π₂ᴹ (δᴹ ,ₛᴹ aᴹ) ≡ aᴹ
    lamᴹ   : ∀{Γᴹ Aᴹ Bᴹ} → Tmᴹ (Γᴹ ,ᴹ Aᴹ) Bᴹ → Tmᴹ Γᴹ (Aᴹ ⇒ᴹ Bᴹ)
    appᴹ   : ∀{Γᴹ Aᴹ Bᴹ} → Tmᴹ Γᴹ (Aᴹ ⇒ᴹ Bᴹ) → Tmᴹ (Γᴹ ,ᴹ Aᴹ) Bᴹ

  _^ᴹ_ : {Γᴹ Δᴹ : Conᴹ}(σᴹ : Tmsᴹ Γᴹ Δᴹ)(Aᴹ : Tyᴹ) → Tmsᴹ (Γᴹ ,ᴹ Aᴹ) (Δᴹ ,ᴹ Aᴹ)
  _^ᴹ_ = λ σᴹ Aᴹ → (σᴹ ∘ᴹ π₁ᴹ idᴹ) ,ₛᴹ (π₂ᴹ idᴹ)

  field
    lam[]ᴹ : ∀{Γᴹ Δᴹ}{δᴹ : Tmsᴹ Γᴹ Δᴹ}{Aᴹ Bᴹ : Tyᴹ}{tᴹ : Tmᴹ (Δᴹ ,ᴹ Aᴹ) Bᴹ}
             → (lamᴹ tᴹ) [ δᴹ ]ᴹ ≡ lamᴹ (tᴹ [ δᴹ ^ᴹ Aᴹ ]ᴹ)
    ⇒βᴹ    : ∀{Γᴹ Aᴹ Bᴹ}{tᴹ : Tmᴹ (Γᴹ ,ᴹ Aᴹ) Bᴹ}
             → appᴹ (lamᴹ tᴹ) ≡ tᴹ
    ⇒ηᴹ    : ∀{Γᴹ Aᴹ Bᴹ}{tᴹ : Tmᴹ Γᴹ (Aᴹ ⇒ᴹ Bᴹ)}
             → lamᴹ (appᴹ tᴹ) ≡ tᴹ

  infixl 5 _,ᴹ_
  infixl 4 _⇒ᴹ_
  infixl 5 _,ₛᴹ_
  infix  6 _∘ᴹ_
  infixl 8 _[_]ᴹ

module _ {i}{j}(M : Model {i}{j}) where

  open Model M

  RecTy : Ty → Tyᴹ
  RecTy ι = ιᴹ
  RecTy (A ⇒ B) = RecTy A ⇒ᴹ RecTy B

  RecCon : Con → Conᴹ
  RecCon ∙ = ∙ᴹ
  RecCon (Γ , A) = RecCon Γ ,ᴹ RecTy A

  postulate
    RecTms : ∀{Γ Δ} → Tms Γ Δ → Tmsᴹ (RecCon Γ) (RecCon Δ)
    RecTm  : ∀{Γ A} → Tm Γ A → Tmᴹ (RecCon Γ) (RecTy A)

  postulate
    idβ  : ∀{Γ} → RecTms {Γ} id ≡ idᴹ
    ∘β   : ∀{Γ Δ Σ}{δ : Tms Δ Σ}{σ : Tms Γ Δ} → RecTms (δ ∘ σ) ≡ RecTms δ ∘ᴹ RecTms σ
    εβ   : ∀{Γ} → RecTms {Γ} ε ≡ εᴹ
    ,ₛβ  : ∀{Γ Δ}{δ : Tms Γ Δ}{A : Ty}{t : Tm Γ A} → RecTms (δ ,ₛ t) ≡ RecTms δ ,ₛᴹ RecTm t
    π₁β  : ∀{Γ Δ}{A : Ty}{σ : Tms Γ (Δ , A)} → RecTms (π₁ σ) ≡ π₁ᴹ (RecTms σ)

    []β  : ∀{Γ Δ}{A : Ty}{t : Tm Δ A}{σ : Tms Γ Δ} → RecTm (t [ σ ]) ≡ RecTm t [ RecTms σ ]ᴹ
    π₂β  : ∀{Γ Δ}{A : Ty}{σ : Tms Γ (Δ , A)} → RecTm (π₂ σ) ≡ π₂ᴹ (RecTms σ)

  {-# REWRITE idβ  #-}
  {-# REWRITE ∘β   #-}
  {-# REWRITE εβ   #-}
  {-# REWRITE ,ₛβ  #-}
  {-# REWRITE π₁β  #-}
  {-# REWRITE []β  #-}
  {-# REWRITE π₂β  #-}

  postulate
    idlβ  : ∀{Γ Δ}{δ : Tms Γ Δ} → RecTms & (idl {δ = δ}) ≡ idlᴹ
    idrβ  : ∀{Γ Δ}{δ : Tms Γ Δ} → RecTms & (idr {δ = δ}) ≡ idrᴹ
    assβ  : ∀{Δ Γ Σ Ω}{σ : Tms Σ Ω}{δ : Tms Γ Σ}{ν : Tms Δ Γ}
            → RecTms & (ass {σ = σ}{δ}{ν}) ≡ assᴹ
    ,∘β   : ∀{Γ Δ Σ}{δ : Tms Γ Δ}{σ : Tms Σ Γ}{A : Ty}{a : Tm Γ A}
            → RecTms & (,∘ {δ = δ}{σ}{a = a}) ≡ ,∘ᴹ
    ,β₁β  : ∀{Γ Δ}{A : Ty}{δ : Tms Γ Δ}{a : Tm Γ A}
            → RecTms & (,β₁ {δ = δ}{a}) ≡ ,β₁ᴹ
    ,ηβ   : ∀{Γ Δ}{A : Ty}{δ : Tms Γ (Δ , A)}
            → RecTms & (,η {δ = δ}) ≡ ,ηᴹ
    ∙ηβ   : ∀{Γ}{σ : Tms Γ ∙}
            → RecTms & (∙η {σ = σ}) ≡ ∙ηᴹ
    ,β₂β  : ∀{Γ Δ}{A : Ty}{δ : Tms Γ Δ}{a : Tm Γ A}
            → RecTm & (,β₂ {δ = δ}{a}) ≡ ,β₂ᴹ

  postulate
    lamβ : ∀{Γ A B}{t : Tm (Γ , A) B} → RecTm (lam t) ≡ lamᴹ (RecTm t)
    appβ : ∀{Γ A B}{t : Tm Γ (A ⇒ B)} → RecTm (app t) ≡ appᴹ (RecTm t)

  {-# REWRITE lamβ #-}
  {-# REWRITE appβ #-}

  postulate
    lam[]β : ∀{Γ Δ}{δ : Tms Γ Δ}{A B : Ty}{t : Tm (Δ , A) B}
             → RecTm & (lam[] {δ = δ}{t = t}) ≡ lam[]ᴹ
    ⇒ββ    : ∀{Γ A B}{t : Tm (Γ , A) B}
             → RecTm & (⇒β {t = t}) ≡ ⇒βᴹ
    ⇒ηβ    : ∀{Γ A B}{t : Tm Γ (A ⇒ B)}
             → RecTm & (⇒η {t = t}) ≡ ⇒ηᴹ

