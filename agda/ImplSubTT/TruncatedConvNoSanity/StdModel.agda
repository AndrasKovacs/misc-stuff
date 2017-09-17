{-# OPTIONS --without-K #-}

module StdModel (Uᴹ : Set)(Elᴹ : Uᴹ → Set) where

open import Lib
open import Syntax
open import Embedding
open import Substitution
open import Conversion
open import Typing
open import Sanity
open import SyntaxSet
open import UIP

Conᴹ :
  ∀ {n}{Γ : Con n} → Γ ⊢ → Set

Tyᴹ :
  ∀ {n Γ} Γw {A} → Γ ⊢ A → Conᴹ {n}{Γ} Γw → Set

Tm⇑ᴹ :
  ∀ {n Γ} Γw {A} Aw {t}(tw : Γ ⊢ t ⇑ A)(γ : Conᴹ {n}{Γ} Γw) → Tyᴹ Γw {A} Aw γ

Tm⇓ᴹ :
  ∀ {n Γ} Γw {A} Aw {t}(tw : Γ ⊢ t ⇓ A)(γ : Conᴹ {n}{Γ} Γw) → Tyᴹ Γw {A} Aw γ

Conᴹ ∙         = ⊤
Conᴹ (Γw ▷ Aw) = Σ (Conᴹ Γw) (Tyᴹ Γw Aw)

Tyᴹ Γw U         γ = Uᴹ
Tyᴹ Γw (El tw)   γ = Elᴹ {!!}
Tyᴹ Γw (Π Aw Bw) γ = (α : Tyᴹ Γw Aw γ) → Tyᴹ (Γw ▷ Aw) Bw (γ , α)

Tm⇑ᴹ Γw Aw        (var x)    γ = {!!}
Tm⇑ᴹ Γw (Π Aw Bw) (lam _ tw) γ = λ α → Tm⇑ᴹ (Γw ▷ Aw) Bw tw (γ , α)
Tm⇑ᴹ Γw Aw        (app tw x) γ = {!Tm⇑ᴹ Γw ? tw!}

Tm⇓ᴹ Γw Aw tw = {!!}
