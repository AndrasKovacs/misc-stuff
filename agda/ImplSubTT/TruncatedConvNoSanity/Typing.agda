{-# OPTIONS --without-K #-}

module Typing where

open import Lib
open import Syntax
open import Embedding
open import Substitution
open import Conversion
open import PropTrunc

lookup : ∀ {n} → Fin n → Con n → Ty n
lookup zero    (Γ ▷ A) = Tyₑ wk A
lookup (suc x) (Γ ▷ A) = Tyₑ wk (lookup x Γ)

infix 3 _⊢ _⊢_ _⊢_⇑_ _⊢_⇓_

data _⊢ : ∀ {n} → Con n → Set
data _⊢_ {n}(Γ : Con n) : Ty n → Set
data _⊢_⇑_ {n}(Γ : Con n) : Tm n → Ty n → Set

_⊢_⇓_ : ∀ {n}(Γ : Con n) → Tm n → Ty n → Set
Γ ⊢ t ⇓ A = ∃ λ A' → (Γ ⊢ t ⇑ A') × ∣ A ~ₜ A' ∣

data _⊢ where
  ∙   : ∙ ⊢
  _▷_ : ∀ {n}{Γ : Con n}{A} → Γ ⊢ → Γ ⊢ A → (Γ ▷ A) ⊢

data _⊢_ {n} Γ  where
  U  : Γ ⊢ U
  El : ∀ {t} → Γ ⊢ t ⇓ U → Γ ⊢ El t
  Π  : ∀ {A B} → Γ ⊢ A → (Γ ▷ A) ⊢ B → Γ ⊢ Π A B

data _⊢_⇑_ {n} Γ where
  var : ∀ x → Γ ⊢ var x ⇑ lookup x Γ
  lam : ∀ {A B t} → Γ ⊢ A → (Γ ▷ A) ⊢ t ⇑ B → Γ ⊢ lam A t ⇑ Π A B
  app : ∀ {t u A B} → Γ ⊢ t ⇑ Π A B → Γ ⊢ u ⇓ A → Γ ⊢ app t u ⇑ Tyₛ (idₛ , u) B
