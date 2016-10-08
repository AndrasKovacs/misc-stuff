{-# OPTIONS --no-eta --rewriting #-}

module STLC.Norm.CoeLemmas where

open import STLC.lib
open import STLC.Syntax
open import STLC.Norm.Methods1

coe-apply :
 ∀ {α β γ}{A : Set α}{B : Set β}(C : A → B → Set γ)
   {b b' : B}(p : b ≡ b')(f : ∀ a → C a b)(a : A)
 →  coe (ap (λ x → ∀ a → C a x) p) f a ≡ coe (ap (C a) p) (f a)
coe-apply C refl f a = refl

coe-× :
 ∀ {α β}{A A' : Set α}{B B' : Set β}(p : A ≡ A')(q : B ≡ B')
   {a : A}{b : B}
 → (A' × B' ∋ (coe p a , coe q b)) ≡ coe (ap2 _×_ p q) (a , b)
coe-× refl refl = refl

,ₛ≡ :
  ∀ {Γ Δ}{σ σ' : Tms Γ Δ}(p : σ ≡ σ'){A : Ty}{t t' : Tm Γ A}(q : t ≡ t')
  → σ ,ₛ t ≡ σ' ,ₛ t'
,ₛ≡ refl refl = refl

ap-◾ :
  ∀ {α}{A B C : Set α}(p : B ≡ C)(q : A ≡ B){a : A}
  → coe p (coe q a) ≡ coe (q ◾ p) a
ap-◾ refl refl = refl

Tmᴹ-≡-intro :
  ∀ {Γ}{Γᴹ : Conᴹ Γ}{A}{Aᴹ : Tyᴹ A}{t₁}{tᴹ₁ : Tmᴹ Γᴹ Aᴹ t₁}{t₂}{tᴹ₂ : Tmᴹ Γᴹ Aᴹ t₂}
  → (p : t₁ ≡ t₂)
  → ((Δ : Con) → (σ : Tms Δ Γ) → (σᴹ : Γᴹ σ) → tᴹ₁ Δ σ σᴹ ≡[ ap (λ t → Aᴹ (t [ σ ])) p ]≡ tᴹ₂ Δ σ σᴹ)
  → tᴹ₁ ≡[ ap (Tmᴹ Γᴹ Aᴹ) p ]≡ tᴹ₂
Tmᴹ-≡-intro {Γ}{Γᴹ}{A}{Aᴹ}{t₁}{tᴹ₁}{t₂}{tᴹ₂} p f =
  funext λ Δ → funext λ σ → funext λ σᴹ →
    ap (λ x → x σ σᴹ) (coe-apply (λ Δ t → (σ : Tms Δ Γ) → Γᴹ σ → Aᴹ (t [ σ ])) p tᴹ₁ Δ)
  ◾ ap (λ x → x σᴹ) (coe-apply (λ σ t → Γᴹ σ → Aᴹ (t [ σ ])) p (tᴹ₁ Δ) σ)
  ◾ coe-apply (λ σᴹ t → Aᴹ (t [ σ ])) p (tᴹ₁ Δ σ) σᴹ
  ◾ f Δ σ σᴹ

Tmsᴹ-≡-intro :
  ∀ {Γ}{Γᴹ : Conᴹ Γ}{Δ}{Δᴹ : Conᴹ Δ}{σ₁ : Tms Γ Δ}
    {σᴹ₁ : Tmsᴹ Γᴹ Δᴹ σ₁}{σ₂ : Tms Γ Δ}{σᴹ₂ : Tmsᴹ Γᴹ Δᴹ σ₂}
  → (p : σ₁ ≡ σ₂)
  → (∀(Σ : Con)(δ : Tms Σ Γ)(δᴹ : Γᴹ δ) → σᴹ₁ Σ δ δᴹ ≡[ ap (λ σ → Δᴹ (σ ∘ δ)) p ]≡ σᴹ₂ Σ δ δᴹ )
  → σᴹ₁ ≡[ ap (Tmsᴹ Γᴹ Δᴹ) p ]≡ σᴹ₂
Tmsᴹ-≡-intro {Γ}{Γᴹ}{Δ}{Δᴹ}{σ₁}{σᴹ₁}{σ₂}{σᴹ₂} p f =
  funext λ Σ → funext λ δ → funext λ δᴹ →
    ap (λ x → x δ δᴹ) (coe-apply (λ Σ σ → (δ : Tms Σ Γ) → Γᴹ δ → Δᴹ (σ ∘ δ)) p σᴹ₁ Σ)
  ◾ (ap (λ x → x δᴹ) (coe-apply (λ δ σ → Γᴹ δ → Δᴹ (σ ∘ δ)) p (σᴹ₁ Σ) δ)
  ◾ coe-apply (λ δᴹ σ → Δᴹ (σ ∘ δ)) p (σᴹ₁ Σ δ) δᴹ)
  ◾ f Σ δ δᴹ

coe-float :
  ∀ {α β γ}
    {A : Set α}{B : A → Set β}{C D : ∀ {a} → B a → Set γ}
    (f : (a : A)(b : B a)(c : C b) → D b)
    {a : A}{b b' : B a}{c : C b}
    (p : b ≡ b')
  → f a b' (coe (ap C p) c) ≡ coe (ap D p) (f a b c)
coe-float f refl = refl

-- todo: use set truncation for Tm and Tms instead of UIP here
UIP : ∀ {α}{A : Set α}{a a' : A}(p q : a ≡ a') → p ≡ q
UIP refl refl = refl

UIP-coe : ∀ {α}{A B : Set α}(p q : A ≡ B){a : A} → coe p a ≡ coe q a
UIP-coe p q {a} = ap (λ x → coe x a) (UIP p q)

