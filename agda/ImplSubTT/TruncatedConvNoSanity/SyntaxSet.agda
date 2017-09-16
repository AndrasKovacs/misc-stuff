{-# OPTIONS --without-K #-}

module SyntaxSet where

open import Lib
open import Syntax

Prop : ∀ {α}(A : Set α) → Set α
Prop A = (x y : A) → x ≡ y

Fin≡? : ∀ {n}(x y : Fin n) → (x ≡ y) ⊎ (x ≢ y)
Fin≡? zero zero = inj₁ refl
Fin≡? zero (suc y) = inj₂ (λ ())
Fin≡? (suc x) zero = inj₂ (λ ())
Fin≡? (suc x) (suc y) with Fin≡? x y
... | inj₁ refl = inj₁ refl
... | inj₂ p    = inj₂ λ {refl → p refl}

mutual
  Ty≡? : ∀ {n}(x y : Ty n) → (x ≡ y) ⊎ (x ≢ y)
  Ty≡? U U               = inj₁ refl
  Ty≡? U (El x)          = inj₂ (λ ())
  Ty≡? U (Π y y₁)        = inj₂ (λ ())
  Ty≡? (El x) U          = inj₂ (λ ())
  Ty≡? (El t) (El t') with Tm≡? t t'
  ... | inj₁ refl = inj₁ refl
  ... | inj₂ x = inj₂ λ {refl → x refl}
  Ty≡? (El x) (Π y y₁)   = inj₂ (λ ())
  Ty≡? (Π x x₁) U        = inj₂ (λ ())
  Ty≡? (Π x x₁) (El x₂)  = inj₂ (λ ())
  Ty≡? (Π A B) (Π A' B') with Ty≡? A A' | Ty≡? B B'
  ... | inj₁ refl | inj₁ refl = inj₁ refl
  ... | inj₁ x | inj₂ x₁ = inj₂ λ {refl → x₁ refl}
  ... | inj₂ x | bar = inj₂ λ {refl → x refl}

  Tm≡? : ∀ {n}(x y : Tm n) → (x ≡ y) ⊎ (x ≢ y)
  Tm≡? (var x) (var x') with Fin≡? x x'
  ... | inj₁ refl = inj₁ refl
  ... | inj₂ p    = inj₂ λ {refl → p refl}
  Tm≡? (var x) (lam x₁ y)    = inj₂ (λ ())
  Tm≡? (var x) (app y y₁)    = inj₂ (λ ())
  Tm≡? (lam x x₁) (var x₂)   = inj₂ (λ ())
  Tm≡? (lam A t) (lam A' t') with Ty≡? A A' | Tm≡? t t'
  ... | inj₁ refl | inj₁ refl = inj₁ refl
  ... | inj₁ _ | inj₂ p = inj₂ λ {refl → p refl}
  ... | inj₂ p | bar = inj₂ λ {refl → p refl}
  Tm≡? (lam x x₁) (app y y₁) = inj₂ (λ ())
  Tm≡? (app x x₁) (var x₂)   = inj₂ (λ ())
  Tm≡? (app x x₁) (lam x₂ y) = inj₂ (λ ())
  Tm≡? (app t u) (app t' u') with Tm≡? t t' | Tm≡? u u'
  ... | inj₁ refl | inj₁ refl = inj₁ refl
  ... | inj₁ x | inj₂ x₁ = inj₂ λ {refl → x₁ refl}
  ... | inj₂ x | bar = inj₂ λ {refl → x refl}

hedberg :
  ∀ {α}{A : Set α}
  → ((x y : A) → (x ≡ y) ⊎ (x ≢ y))
  → ∀ {x y : A} → Prop (x ≡ y)
hedberg {_}{A} eq? {x}{y} p q =
  f-inv p ⁻¹ ◾ (_◾ f refl ⁻¹) & f-const p q ◾ f-inv q
  where
    f : {x y : A} → x ≡ y → x ≡ y
    f {x}{y} p with eq? x y
    ... | inj₁ eq   = eq
    ... | inj₂ ¬eq  = ⊥-elim (¬eq p)

    f-const : ∀ {x y} p q → f {x}{y} p ≡ f q
    f-const {x}{y} p q  with eq? x y
    ... | inj₁ eq  = refl
    ... | inj₂ ¬eq = ⊥-elim (¬eq q)

    f-inv : ∀ {x y} p → (f {x}{y} p ◾ f refl ⁻¹) ≡ p
    f-inv refl = J (λ p → (p ◾ p ⁻¹) ≡ refl) refl (f refl)
