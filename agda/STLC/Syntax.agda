{-# OPTIONS --without-K --no-eta #-}

module Syntax where

open import Lib using (_≡_; refl)

-- declaration of the syntax

infixl 5 _,_
infixl 4 _⇒_

data Ty : Set where
  ι   : Ty
  _⇒_ : Ty → Ty → Ty

data Con : Set where
  ∙   : Con
  _,_ : Con → Ty → Con

postulate
  Tms : Con → Con → Set
  Tm  : Con → Ty → Set

----------------------------------------------------------------------
-- Core substitution calculus
----------------------------------------------------------------------

postulate
  id    : ∀{Γ} → Tms Γ Γ
  _∘_   : ∀{Γ Δ Σ} → Tms Δ Σ → Tms Γ Δ → Tms Γ Σ
  ε     : ∀{Γ} → Tms Γ ∙
  _,ₛ_  : ∀{Γ Δ}(δ : Tms Γ Δ){A : Ty} → Tm Γ A → Tms Γ (Δ , A)
  π₁    : ∀{Γ Δ}{A : Ty} → Tms Γ (Δ , A) →  Tms Γ Δ

  _[_]  : ∀{Γ Δ}{A : Ty} → Tm Δ A → Tms Γ Δ → Tm Γ A
  π₂    : ∀{Γ Δ}{A : Ty} → Tms Γ (Δ , A) → Tm Γ A

infixl 5 _,ₛ_
infix  6 _∘_
infixl 8 _[_]

postulate
   idl  : ∀{Γ Δ}{δ : Tms Γ Δ} → id ∘ δ ≡ δ
   idr  : ∀{Γ Δ}{δ : Tms Γ Δ} → δ ∘ id ≡ δ
   ass  : ∀{Δ Γ Σ Ω}{σ : Tms Σ Ω}{δ : Tms Γ Σ}{ν : Tms Δ Γ}
          → (σ ∘ δ) ∘ ν ≡ σ ∘ (δ ∘ ν)
   ,∘   : ∀{Γ Δ Σ}{δ : Tms Γ Δ}{σ : Tms Σ Γ}{A : Ty}{a : Tm Γ A}
          → (δ ,ₛ a) ∘ σ ≡ (δ ∘ σ) ,ₛ a [ σ ]
   ,β₁  : ∀{Γ Δ}{A : Ty}{δ : Tms Γ Δ}{a : Tm Γ A}
          → π₁ (δ ,ₛ a) ≡ δ
   ,η   : ∀{Γ Δ}{A : Ty}{δ : Tms Γ (Δ , A)}
          → π₁ δ ,ₛ π₂ δ ≡ δ
   ∙η   : ∀{Γ}{σ : Tms Γ ∙}
          → σ ≡ ε

   ,β₂  : ∀{Γ Δ}{A : Ty}{δ : Tms Γ Δ}{a : Tm Γ A}
        → π₂ (δ ,ₛ a) ≡ a

-- De Bruijn indices

wk : ∀{Γ}{A : Ty} → Tms (Γ , A) Γ
wk = π₁ id

vz : ∀ {Γ}{A : Ty} → Tm (Γ , A) A
vz = π₂ id

vs : ∀ {Γ}{A B : Ty} → Tm Γ A → Tm (Γ , B) A
vs x = x [ wk ]

----------------------------------------------------------------------
-- Function space
----------------------------------------------------------------------

postulate
  lam : ∀{Γ A B} → Tm (Γ , A) B → Tm Γ (A ⇒ B)
  app : ∀{Γ A B} → Tm Γ (A ⇒ B) → Tm (Γ , A) B

_^_ : {Γ Δ : Con}(σ : Tms Γ Δ)(A : Ty) → Tms (Γ , A) (Δ , A)
σ ^ A = σ ∘ wk ,ₛ vz

infixl 5 _^_

postulate
   lam[] : ∀{Γ Δ}{δ : Tms Γ Δ}{A B : Ty}{t : Tm (Δ , A) B}
         → (lam t) [ δ ] ≡ lam (t [ δ ^ A ])
   ⇒β    : ∀{Γ A B}{t : Tm (Γ , A) B}
         → app (lam t) ≡ t
   ⇒η    : ∀{Γ A B}{t : Tm Γ (A ⇒ B)}
         → lam (app t) ≡ t

_$_ : ∀ {Γ A B} → Tm Γ (A ⇒ B) → Tm Γ A → Tm Γ B
t $ x = app t [ id ,ₛ x ]

infixl 7 _$_
