{-# OPTIONS --without-K #-}

module STLC.Nf where

open import STLC.lib
open import STLC.Syntax

data _∈_ (A : Ty) : Con → Set where
  vzₙ : ∀ {Γ} → A ∈ (Γ , A)
  vsₙ : ∀ {B Γ} → A ∈ Γ → A ∈ (Γ , B)

infix 3 _∈_

mutual
  data Nf (Γ : Con) : Ty → Set where
    ne   : Ne Γ ι → Nf Γ ι
    lamₙ : ∀ {A B} → Nf (Γ , A) B → Nf Γ (A ⇒ B)

  data Ne (Γ : Con) : Ty → Set where
    var  : ∀ {A} → A ∈ Γ → Ne Γ A
    _$ₙ_ : ∀ {A B} → Ne Γ (A ⇒ B) → Nf Γ A → Ne Γ B

infixl 7 _$ₙ_

⌜_⌝∈ : ∀ {Γ A} → A ∈ Γ → Tm Γ A
⌜ vzₙ   ⌝∈ = vz
⌜ vsₙ v ⌝∈ = vs ⌜ v ⌝∈

mutual
  ⌜_⌝ : ∀ {Γ A} → Nf Γ A → Tm Γ A
  ⌜ ne n   ⌝ = ⌜ n ⌝ne
  ⌜ lamₙ t ⌝ = lam ⌜ t ⌝

  ⌜_⌝ne : ∀ {Γ A} → Ne Γ A → Tm Γ A
  ⌜ var v  ⌝ne = ⌜ v ⌝∈
  ⌜ n $ₙ t ⌝ne = ⌜ n ⌝ne $ ⌜ t ⌝
