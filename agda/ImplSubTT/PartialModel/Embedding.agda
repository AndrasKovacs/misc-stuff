{-# OPTIONS --without-K #-}

module Embedding where

open import Lib
open import Syntax

data OPE : ℕ → ℕ → Set where
  ∙    : OPE zero zero
  drop : ∀ {n m} → OPE n m → OPE (suc n) m
  keep : ∀ {n m} → OPE n m → OPE (suc n) (suc m)

idₑ : ∀ {n} → OPE n n
idₑ {zero}  = ∙
idₑ {suc n} = keep idₑ

wk : ∀ {n} → OPE (suc n) n
wk = drop idₑ

_∘ₑ_ : ∀ {m n k} → OPE m k → OPE n m → OPE n k
σ      ∘ₑ ∙      = σ
σ      ∘ₑ drop δ = drop (σ ∘ₑ δ)
drop σ ∘ₑ keep δ = drop (σ ∘ₑ δ)
keep σ ∘ₑ keep δ = keep (σ ∘ₑ δ)

idlₑ : ∀ {Γ Δ}(σ : OPE Γ Δ) → idₑ ∘ₑ σ ≡ σ
idlₑ ∙        = refl
idlₑ (drop σ) = drop & idlₑ σ
idlₑ (keep σ) = keep & idlₑ σ

idrₑ : ∀ {Γ Δ}(σ : OPE Γ Δ) → σ ∘ₑ idₑ ≡ σ
idrₑ ∙        = refl
idrₑ (drop σ) = drop & idrₑ σ
idrₑ (keep σ) = keep & idrₑ σ

assₑ :
  ∀ {Γ Δ Σ Ξ}(σ : OPE Σ Ξ)(δ : OPE Δ Σ)(ν : OPE Γ Δ)
  → (σ ∘ₑ δ) ∘ₑ ν ≡ σ ∘ₑ (δ ∘ₑ ν)
assₑ σ        δ        ∙        = refl
assₑ σ        δ        (drop ν) = drop & assₑ σ δ ν
assₑ σ        (drop δ) (keep ν) = drop & assₑ σ δ ν
assₑ (drop σ) (keep δ) (keep ν) = drop & assₑ σ δ ν
assₑ (keep σ) (keep δ) (keep ν) = keep & assₑ σ δ ν

∈ₑ : ∀ {Γ Δ} → OPE Γ Δ → Fin Δ → Fin Γ
∈ₑ ∙        x       = x
∈ₑ (drop σ) x       = suc (∈ₑ σ x)
∈ₑ (keep σ) zero    = zero
∈ₑ (keep σ) (suc x) = suc (∈ₑ σ x)

∈-idₑ : ∀ {Γ}(x : Fin Γ) → ∈ₑ idₑ x ≡ x
∈-idₑ zero    = refl
∈-idₑ (suc x) = suc & ∈-idₑ x

∈-∘ₑ : ∀ {Γ Δ Σ}(σ : OPE Δ Σ)(δ : OPE Γ Δ)(v : Fin Σ) → ∈ₑ (σ ∘ₑ δ) v ≡ ∈ₑ δ (∈ₑ σ v)
∈-∘ₑ ∙        ∙        v       = refl
∈-∘ₑ σ        (drop δ) v       = suc & ∈-∘ₑ σ δ v
∈-∘ₑ (drop σ) (keep δ) v       = suc & ∈-∘ₑ σ δ v
∈-∘ₑ (keep σ) (keep δ) zero    = refl
∈-∘ₑ (keep σ) (keep δ) (suc v) = suc & ∈-∘ₑ σ δ v

mutual
  Tmₑ : ∀ {Γ Δ} → OPE Γ Δ → Tm Δ → Tm Γ
  Tmₑ σ (var x)       = var (∈ₑ σ x)
  Tmₑ σ (lam t)       = lam (Tmₑ (keep σ) t)
  Tmₑ σ (app A B t u) = app (Tyₑ σ A) (Tyₑ (keep σ) B) (Tmₑ σ t) (Tmₑ σ u)

  Tyₑ : ∀ {Γ Δ} → OPE Γ Δ → Ty Δ → Ty Γ
  Tyₑ σ U       = U
  Tyₑ σ (El t)  = El (Tmₑ σ t)
  Tyₑ σ (Π A B) = Π (Tyₑ σ A) (Tyₑ (keep σ) B)

mutual
  Tm-idₑ : ∀ {Γ}(t : Tm Γ) → Tmₑ idₑ t ≡ t
  Tm-idₑ (var x)       = var & ∈-idₑ x
  Tm-idₑ (lam t)       = lam & Tm-idₑ t
  Tm-idₑ (app A B f a) = app & Ty-idₑ A ⊗ Ty-idₑ B ⊗ Tm-idₑ f ⊗ Tm-idₑ a

  Ty-idₑ : ∀ {Γ}(A : Ty Γ) → Tyₑ idₑ A ≡ A
  Ty-idₑ U       = refl
  Ty-idₑ (El t)  = El & Tm-idₑ t
  Ty-idₑ (Π A B) = Π & Ty-idₑ A ⊗ Ty-idₑ B

mutual
  Tm-∘ₑ : ∀ {Γ Δ Σ}(σ : OPE Δ Σ)(δ : OPE Γ Δ)(t : Tm Σ) → Tmₑ (σ ∘ₑ δ) t ≡ Tmₑ δ (Tmₑ σ t)
  Tm-∘ₑ σ δ (var x)       = var & ∈-∘ₑ σ δ x
  Tm-∘ₑ σ δ (lam t)       = lam & Tm-∘ₑ (keep σ) (keep δ) t
  Tm-∘ₑ σ δ (app A B f a) = app & Ty-∘ₑ σ δ A ⊗ Ty-∘ₑ (keep σ) (keep δ) B ⊗ Tm-∘ₑ σ δ f ⊗ Tm-∘ₑ σ δ a

  Ty-∘ₑ : ∀ {Γ Δ Σ}(σ : OPE Δ Σ)(δ : OPE Γ Δ)(A : Ty Σ) → Tyₑ (σ ∘ₑ δ) A ≡ Tyₑ δ (Tyₑ σ A)
  Ty-∘ₑ σ δ U       = refl
  Ty-∘ₑ σ δ (El t)  = El & Tm-∘ₑ σ δ t
  Ty-∘ₑ σ δ (Π A B) = Π & Ty-∘ₑ σ δ A ⊗ Ty-∘ₑ (keep σ) (keep δ) B
