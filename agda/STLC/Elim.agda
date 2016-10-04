{-# OPTIONS --without-K --no-eta --rewriting #-}

module STLC.Elim where

open import Level
open import STLC.lib
open import STLC.Syntax

record Model {i j} : Set (suc (i ⊔ j)) where
  field
    Tyᴹ    : Ty → Set i
    Conᴹ   : Con → Set i
    Tmsᴹ   : ∀ {Γ} → Conᴹ Γ → ∀{Δ} → Conᴹ Δ → Tms Γ Δ → Set j
    Tmᴹ    : ∀ {Γ} → Conᴹ Γ → ∀{A} → Tyᴹ A → Tm Γ A → Set j

    ιᴹ     : Tyᴹ ι
    _⇒ᴹ_   : ∀ {A} → Tyᴹ A → ∀ {B} → Tyᴹ B → Tyᴹ (A ⇒ B)

    ∙ᴹ     : Conᴹ ∙
    _,ᴹ_   : ∀ {Γ} → Conᴹ Γ → ∀ {A} → Tyᴹ A → Conᴹ (Γ , A)

    idᴹ    : ∀ {Γ Γᴹ} → Tmsᴹ Γᴹ Γᴹ (id {Γ})

    _∘ᴹ_   : ∀ {Γ Γᴹ Δ Δᴹ Σ Σᴹ}
             → {σ : Tms Δ Σ} → Tmsᴹ Δᴹ Σᴹ σ → {ν : Tms Γ Δ} → Tmsᴹ Γᴹ Δᴹ ν → Tmsᴹ Γᴹ Σᴹ (σ ∘ ν)

    εᴹ     : ∀{Γ}{Γᴹ : Conᴹ Γ} → Tmsᴹ Γᴹ ∙ᴹ ε

    _,ₛᴹ_  : ∀{Γ Γᴹ Δ Δᴹ}{δ : Tms Γ Δ} → Tmsᴹ Γᴹ Δᴹ δ
             → ∀{A Aᴹ}{t : Tm Γ A} → Tmᴹ Γᴹ Aᴹ t → Tmsᴹ Γᴹ (Δᴹ ,ᴹ Aᴹ) (δ ,ₛ t)

    π₁ᴹ    : ∀{Γ Γᴹ Δ Δᴹ A Aᴹ}{δ : Tms Γ (Δ , A)} → Tmsᴹ Γᴹ (Δᴹ ,ᴹ Aᴹ) δ → Tmsᴹ Γᴹ Δᴹ (π₁ δ)

    _[_]ᴹ  : ∀ {Γ Γᴹ Δ Δᴹ A Aᴹ}{t : Tm Δ A}
             → Tmᴹ Δᴹ Aᴹ t → {δ : Tms Γ Δ} → Tmsᴹ Γᴹ Δᴹ δ → Tmᴹ Γᴹ Aᴹ (t [ δ ])

    π₂ᴹ    : ∀{Γ Γᴹ Δ Δᴹ A Aᴹ}{δ : Tms Γ (Δ , A)} → Tmsᴹ Γᴹ (Δᴹ ,ᴹ Aᴹ) δ → Tmᴹ Γᴹ Aᴹ (π₂ δ)

    idlᴹ   : ∀{Γ Γᴹ Δ Δᴹ}{δ : Tms Γ Δ}{δᴹ : Tmsᴹ Γᴹ Δᴹ δ} → idᴹ ∘ᴹ δᴹ ≡[ ap (Tmsᴹ Γᴹ Δᴹ) idl ]≡ δᴹ
    idrᴹ   : ∀{Γ Γᴹ Δ Δᴹ}{δ : Tms Γ Δ}{δᴹ : Tmsᴹ Γᴹ Δᴹ δ} → δᴹ ∘ᴹ idᴹ ≡[ ap (Tmsᴹ Γᴹ Δᴹ) idr ]≡ δᴹ

    assᴹ   : ∀ {Δ Δᴹ Γ Γᴹ Σ Σᴹ Ω Ωᴹ}{σ : Tms Σ Ω}{σᴹ : Tmsᴹ Σᴹ Ωᴹ σ}
               {δ : Tms Γ Σ}{δᴹ : Tmsᴹ Γᴹ Σᴹ δ}{ν : Tms Δ Γ}{νᴹ : Tmsᴹ Δᴹ Γᴹ ν}
             → (σᴹ ∘ᴹ δᴹ) ∘ᴹ νᴹ ≡[ ap (Tmsᴹ Δᴹ Ωᴹ) ass ]≡ (σᴹ ∘ᴹ (δᴹ ∘ᴹ νᴹ))

    ,∘ᴹ    : ∀ {Γ Γᴹ Δ Δᴹ Σ Σᴹ}{δ : Tms Γ Δ}{δᴹ : Tmsᴹ Γᴹ Δᴹ δ}{σ : Tms Σ Γ}{σᴹ : Tmsᴹ Σᴹ Γᴹ σ}
               {A}{Aᴹ : Tyᴹ A}{a}{aᴹ : Tmᴹ Γᴹ Aᴹ a}
             → (δᴹ ,ₛᴹ aᴹ) ∘ᴹ σᴹ ≡[ ap (Tmsᴹ Σᴹ (Δᴹ ,ᴹ Aᴹ)) ,∘ ]≡ (δᴹ ∘ᴹ σᴹ) ,ₛᴹ aᴹ [ σᴹ ]ᴹ

    ,β₁ᴹ   : ∀ {Γ Γᴹ Δ Δᴹ A Aᴹ}{δ : Tms Γ Δ}{δᴹ : Tmsᴹ Γᴹ Δᴹ δ}{a : Tm Γ A}{aᴹ : Tmᴹ Γᴹ Aᴹ a}
             → π₁ᴹ (δᴹ ,ₛᴹ aᴹ) ≡[ ap (Tmsᴹ Γᴹ Δᴹ) ,β₁ ]≡ δᴹ

    ,ηᴹ    : ∀ {Γ Γᴹ Δ Δᴹ A Aᴹ}{δ : Tms Γ (Δ , A)}{δᴹ : Tmsᴹ Γᴹ (Δᴹ ,ᴹ Aᴹ) δ}
             → π₁ᴹ δᴹ ,ₛᴹ π₂ᴹ δᴹ ≡[ ap (Tmsᴹ Γᴹ (Δᴹ ,ᴹ Aᴹ)) ,η ]≡ δᴹ

    ∙ηᴹ    : ∀ {Γ Γᴹ}{σ : Tms Γ ∙}{σᴹ : Tmsᴹ Γᴹ ∙ᴹ σ} → σᴹ ≡[ ap (Tmsᴹ Γᴹ ∙ᴹ) ∙η ]≡ εᴹ

    ,β₂ᴹ   : ∀{Γ Γᴹ Δ Δᴹ A Aᴹ}{δ : Tms Γ Δ}{δᴹ : Tmsᴹ Γᴹ Δᴹ δ}{a : Tm Γ A}{aᴹ : Tmᴹ Γᴹ Aᴹ a}
           → π₂ᴹ (δᴹ ,ₛᴹ aᴹ) ≡[ ap (Tmᴹ Γᴹ Aᴹ) ,β₂ ]≡ aᴹ

    lamᴹ   : ∀{Γ Γᴹ A Aᴹ B Bᴹ}{t : Tm (Γ , A) B} → Tmᴹ (Γᴹ ,ᴹ Aᴹ) Bᴹ t → Tmᴹ Γᴹ (Aᴹ ⇒ᴹ Bᴹ) (lam t)

    appᴹ   : ∀{Γ Γᴹ A Aᴹ B Bᴹ}{t : Tm Γ (A ⇒ B)} → Tmᴹ Γᴹ (Aᴹ ⇒ᴹ Bᴹ) t → Tmᴹ (Γᴹ ,ᴹ Aᴹ) Bᴹ (app t)

  _^ᴹ_ : ∀ {Γ Γᴹ Δ Δᴹ}{σ : Tms Γ Δ}(σᴹ : Tmsᴹ Γᴹ Δᴹ σ){A}(Aᴹ : Tyᴹ A) → Tmsᴹ (Γᴹ ,ᴹ Aᴹ) (Δᴹ ,ᴹ Aᴹ) (σ ^ A)
  _^ᴹ_ σᴹ Aᴹ = (σᴹ ∘ᴹ π₁ᴹ idᴹ) ,ₛᴹ π₂ᴹ idᴹ

  field
    lam[]ᴹ : ∀{Γ Γᴹ Δ Δᴹ}{δ : Tms Γ Δ}{δᴹ : Tmsᴹ Γᴹ Δᴹ δ}{A Aᴹ B Bᴹ}
               {t : Tm (Δ , A) B}{tᴹ : Tmᴹ (Δᴹ ,ᴹ Aᴹ) Bᴹ t}
             → (lamᴹ tᴹ) [ δᴹ ]ᴹ ≡[ ap (Tmᴹ Γᴹ (Aᴹ ⇒ᴹ Bᴹ)) lam[] ]≡ lamᴹ (tᴹ [ δᴹ ^ᴹ Aᴹ ]ᴹ)
    ⇒βᴹ    : ∀{Γ Γᴹ A Aᴹ B Bᴹ}{t : Tm (Γ , A) B}{tᴹ : Tmᴹ (Γᴹ ,ᴹ Aᴹ) Bᴹ t}
             → appᴹ (lamᴹ tᴹ) ≡[ ap (Tmᴹ (Γᴹ ,ᴹ Aᴹ) Bᴹ) ⇒β ]≡ tᴹ
    ⇒ηᴹ    : ∀{Γ Γᴹ A Aᴹ B Bᴹ}{t : Tm Γ (A ⇒ B)}{tᴹ : Tmᴹ Γᴹ (Aᴹ ⇒ᴹ Bᴹ) t}
             → lamᴹ (appᴹ tᴹ) ≡[ ap (Tmᴹ Γᴹ (Aᴹ ⇒ᴹ Bᴹ)) ⇒η ]≡ tᴹ

  infixl 5 _,ᴹ_
  infixl 4 _⇒ᴹ_
  infixl 5 _,ₛᴹ_
  infix  6 _∘ᴹ_
  infixl 8 _[_]ᴹ


module _ {i}{j}(M : Model {i}{j}) where
  open Model M

  ElimTy : (A : Ty) → Tyᴹ A
  ElimTy ι       = ιᴹ
  ElimTy (A ⇒ B) = ElimTy A ⇒ᴹ ElimTy B

  ElimCon : (Γ : Con) → Conᴹ Γ
  ElimCon ∙       = ∙ᴹ
  ElimCon (Γ , A) = ElimCon Γ ,ᴹ ElimTy A

  postulate
    ElimTms : ∀{Γ Δ}(σ : Tms Γ Δ) → Tmsᴹ (ElimCon Γ) (ElimCon Δ) σ
    ElimTm  : ∀{Γ A}(t : Tm Γ A) → Tmᴹ (ElimCon Γ) (ElimTy A) t

  postulate
    idβ  : ∀{Γ} → ElimTms {Γ} id ≡ idᴹ
    ∘β   : ∀{Γ Δ Σ}{δ : Tms Δ Σ}{σ : Tms Γ Δ} → ElimTms (δ ∘ σ) ≡ ElimTms δ ∘ᴹ ElimTms σ
    εβ   : ∀{Γ} → ElimTms {Γ} ε ≡ εᴹ
    ,sβ  : ∀{Γ Δ}{δ : Tms Γ Δ}{A : Ty}{t : Tm Γ A} → ElimTms (δ ,ₛ t) ≡ ElimTms δ ,ₛᴹ ElimTm t
    π₁β  : ∀{Γ Δ}{A : Ty}{σ : Tms Γ (Δ , A)} → ElimTms (π₁ σ) ≡ π₁ᴹ (ElimTms σ)
    []tβ : ∀{Γ Δ}{A : Ty}{t : Tm Δ A}{σ : Tms Γ Δ} → ElimTm (t [ σ ]) ≡ ElimTm t [ ElimTms σ ]ᴹ
    π₂β  : ∀{Γ Δ}{A : Ty}{σ : Tms Γ (Δ , A)} → ElimTm (π₂ σ) ≡ π₂ᴹ (ElimTms σ)

  {-# REWRITE idβ  #-}
  {-# REWRITE ∘β   #-}
  {-# REWRITE εβ   #-}
  {-# REWRITE ,sβ  #-}
  {-# REWRITE π₁β  #-}
  {-# REWRITE []tβ #-}
  {-# REWRITE π₂β  #-}

  postulate
    idlβ  : ∀{Γ Δ}{δ : Tms Γ Δ} → apd ElimTms (idl {δ = δ}) ≡ idlᴹ
    idrβ  : ∀{Γ Δ}{δ : Tms Γ Δ} → apd ElimTms (idr {δ = δ}) ≡ idrᴹ
    assβ  : ∀{Δ Γ Σ Ω}{σ : Tms Σ Ω}{δ : Tms Γ Σ}{ν : Tms Δ Γ}
            → apd ElimTms (ass {σ = σ}{δ}{ν}) ≡ assᴹ
    ,∘β   : ∀{Γ Δ Σ}{δ : Tms Γ Δ}{σ : Tms Σ Γ}{A : Ty}{a : Tm Γ A}
            → apd ElimTms (,∘ {δ = δ}{σ}{a = a}) ≡ ,∘ᴹ
    ,β₁β  : ∀{Γ Δ}{A : Ty}{δ : Tms Γ Δ}{a : Tm Γ A}
            → apd ElimTms (,β₁ {δ = δ}{a}) ≡ ,β₁ᴹ
    ,ηβ   : ∀{Γ Δ}{A : Ty}{δ : Tms Γ (Δ , A)}
            → apd ElimTms (,η {δ = δ}) ≡ ,ηᴹ
    •ηβ   : ∀{Γ}{σ : Tms Γ ∙}
            → apd ElimTms (∙η {σ = σ}) ≡ ∙ηᴹ
    ,β₂β  : ∀{Γ Δ}{A : Ty}{δ : Tms Γ Δ}{a : Tm Γ A}
            → apd ElimTm (,β₂ {δ = δ}{a}) ≡ ,β₂ᴹ

  postulate
    lamβ : ∀{Γ A B}{t : Tm (Γ , A) B} → ElimTm (lam t) ≡ lamᴹ (ElimTm t)
    appβ : ∀{Γ A B}{t : Tm Γ (A ⇒ B)} → ElimTm (app t) ≡ appᴹ (ElimTm t)

  {-# REWRITE lamβ #-}
  {-# REWRITE appβ #-}

  postulate
    lam[]β : ∀{Γ Δ}{δ : Tms Γ Δ}{A B : Ty}{t : Tm (Δ , A) B}
             → apd ElimTm (lam[] {δ = δ}{t = t}) ≡ lam[]ᴹ
    ⇒ββ    : ∀{Γ A B}{t : Tm (Γ , A) B}
             → apd ElimTm (⇒β {t = t}) ≡ ⇒βᴹ
    ⇒ηβ    : ∀{Γ A B}{t : Tm Γ (A ⇒ B)}
             → apd ElimTm (⇒η {t = t}) ≡ ⇒ηᴹ

