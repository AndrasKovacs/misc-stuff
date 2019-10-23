{-# OPTIONS --without-K --postfix-projections #-}

module Syntax where

open import Lib

infixr 6 _∘'ₑ_
infixr 3 _⇒_
infixr 4 _,_

-- Type syntax
--------------------------------------------------------------------------------

data Con' : Set where
  ∙   : Con'
  _,* : Con' → Con'

data *∈ : Con' → Set where
  vz : ∀ {Γ} → *∈ (Γ ,*)
  vs : ∀ {Γ} → *∈ Γ → *∈ (Γ ,*)

data Ty (Γ : Con') : Set where
  var : *∈ Γ → Ty Γ
  _⇒_ : Ty Γ → Ty Γ → Ty Γ
  ∀'  : Ty (Γ ,*) → Ty Γ

-- Type embedding
--------------------------------------------------------------------------------

data OPE' : Con' → Con' → Set where
  ∙    : OPE' ∙ ∙
  drop : ∀ {Γ Δ} → OPE' Γ Δ → OPE' (Γ ,*) Δ
  keep : ∀ {Γ Δ} → OPE' Γ Δ → OPE' (Γ ,*) (Δ ,*)

id'ₑ : ∀ {Γ} → OPE' Γ Γ
id'ₑ {∙}    = ∙
id'ₑ {Γ ,*} = keep (id'ₑ {Γ})

wk' : ∀ {Γ} → OPE' (Γ ,*) Γ
wk' = drop id'ₑ

*∈ₑ : ∀ {Γ Δ} → OPE' Δ Γ → *∈ Γ → *∈ Δ
*∈ₑ ∙        v      = v
*∈ₑ (drop σ) v      = vs (*∈ₑ σ v)
*∈ₑ (keep σ) vz     = vz
*∈ₑ (keep σ) (vs v) = vs (*∈ₑ σ v)

Tyₑ : ∀ {Γ Δ} → OPE' Δ Γ → Ty Γ → Ty Δ
Tyₑ σ (var v) = var (*∈ₑ σ v)
Tyₑ σ (A ⇒ B) = Tyₑ σ A ⇒ Tyₑ σ B
Tyₑ σ (∀' A)  = ∀' (Tyₑ (keep σ) A)

_∘'ₑ_ : ∀ {Γ Δ Σ} → OPE' Δ Σ → OPE' Γ Δ → OPE' Γ Σ
σ      ∘'ₑ ∙      = σ
σ      ∘'ₑ drop δ = drop (σ ∘'ₑ δ)
drop σ ∘'ₑ keep δ = drop (σ ∘'ₑ δ)
keep σ ∘'ₑ keep δ = keep (σ ∘'ₑ δ)


-- Type substitution
--------------------------------------------------------------------------------

data Sub' (Γ : Con') : Con' → Set where
  ∙   : Sub' Γ ∙
  _,_ : ∀ {Δ} → Sub' Γ Δ → Ty Γ → Sub' Γ (Δ ,*)

_ₛ∘'ₑ_ : ∀ {Γ Δ Σ} → Sub' Δ Σ → OPE' Γ Δ → Sub' Γ Σ
∙       ₛ∘'ₑ δ = ∙
(σ , A) ₛ∘'ₑ δ = (σ ₛ∘'ₑ δ) , Tyₑ δ A

drop'ₛ : ∀ {Γ Δ} → Sub' Γ Δ → Sub' (Γ ,*) Δ
drop'ₛ σ = σ ₛ∘'ₑ wk'

keep'ₛ : ∀ {Γ Δ} → Sub' Γ Δ → Sub' (Γ ,*) (Δ ,*)
keep'ₛ σ = drop'ₛ σ , var vz

*∈ₛ : ∀ {Γ Δ} → Sub' Δ Γ → *∈ Γ → Ty Δ
*∈ₛ (σ , A) vz     = A
*∈ₛ (σ , _) (vs v) = *∈ₛ σ v

Tyₛ : ∀ {Γ Δ} → Sub' Δ Γ → Ty Γ → Ty Δ
Tyₛ σ (var v) = *∈ₛ σ v
Tyₛ σ (A ⇒ B) = Tyₛ σ A ⇒ Tyₛ σ B
Tyₛ σ (∀' A)  = ∀' (Tyₛ (keep'ₛ σ) A)

id'ₛ : ∀ {Γ} → Sub' Γ Γ
id'ₛ {∙}    = ∙
id'ₛ {Γ ,*} = keep'ₛ id'ₛ


-- Terms
--------------------------------------------------------------------------------

data Con : Con' → Set where
  ∙    : Con ∙
  _,_  : ∀ {Γ'} → Con Γ' → Ty Γ' → Con Γ'
  _,*  : ∀ {Γ'} → Con Γ' → Con (Γ' ,*)

infix 3 _∈_
data _∈_ : ∀ {Δ} (A : Ty Δ) → Con Δ → Set where
  vz  : ∀ {Δ}{A : Ty Δ}{Γ}   → A ∈ (Γ , A)
  vs  : ∀ {Δ}{A : Ty Δ}{B Γ} → A ∈ Γ → A ∈ (Γ , B)
  vs* : ∀ {Δ}{A : Ty Δ}{Γ}   → A ∈ Γ → Tyₑ wk' A ∈ (Γ ,*)

data Tm {Δ} (Γ : Con Δ) : Ty Δ → Set where
  var  : ∀ {A} → A ∈ Γ → Tm Γ A
  lam  : ∀ {A B} → Tm (Γ , A) B → Tm Γ (A ⇒ B)
  app  : ∀ {A B} → Tm Γ (A ⇒ B) → Tm Γ A → Tm Γ B
  tlam : ∀ {A} → Tm (Γ ,*) A → Tm Γ (∀' A)
  tapp : ∀ {A} → Tm Γ (∀' A) → (B : Ty Δ) → Tm Γ (Tyₛ (id'ₛ , B) A)
