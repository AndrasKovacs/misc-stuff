{-# OPTIONS --without-K #-}

module Typing where

open import Lib
open import Syntax
open import Embedding
open import Substitution
open import Conversion

data _⊢ : ∀ {n} → Con n → Set
data _⊢_ {n}(Γ : Con n) : Ty n → Set
data _,_∈_ : ∀ {n} → Fin n → Ty n → Con n → Set
data _⊢_∈_ {n}(Γ : Con n) : Tm n → Ty n → Set

infix 3 _⊢
infix 3 _⊢_
infix 3 _⊢_∈_
infix 3 _,_∈_

data _⊢ where
  ∙   : ∙ ⊢
  _▷_ : ∀ {n Γ}{A : Ty n} → Γ ⊢ → Γ ⊢ A → (Γ ▷ A) ⊢

data _⊢_ {n} Γ where
  U  : Γ ⊢ → Γ ⊢ U
  El : ∀ {t} → Γ ⊢ t ∈ U → Γ ⊢ El t
  Π  : ∀ {A B} → Γ ⊢ A → (Γ ▷ A) ⊢ B → Γ ⊢ Π A B

data _,_∈_ where
  zero : ∀ {n A}{Γ : Con n} → Γ ⊢ A → zero , Tyₑ wk A ∈ (Γ ▷ A)
  suc  : ∀ {n x A B}{Γ : Con n} → Γ ⊢ B → x , A ∈ Γ → suc x , Tyₑ wk A ∈ (Γ ▷ B)

data _⊢_∈_ {n} Γ where
  var  : ∀ {x A} → x , A ∈ Γ → Γ ⊢ var x ∈ A
  app  : ∀ {t u A B} → Γ ⊢ t ∈ Π A B → Γ ⊢ u ∈ A → Γ ⊢ app t u ∈ Tyₛ (idₛ , u) B
  lam  : ∀ {t A B} → Γ ⊢ A → Γ ▷ A ⊢ t ∈ B → Γ ⊢ lam t ∈ Π A B
  conv : ∀ {t A B} → Γ ⊢ A → Γ ⊢ B → A ~ₜ B → Γ ⊢ t ∈ A → Γ ⊢ t ∈ B


