{-# OPTIONS --without-K #-}

module Abstraction where

open import Lib

import Source.Syntax as S
import Source.LogicalEqv as S
import Source.StdModel as S
open S.Ty
open S.Con
open S.Tm
open S._∈_
open S.OPE
open S.Sub
open S._~_
open S._~ₛ_

import Target.Syntax as T
import Target.LogicalEqv as T
import Target.ClosureBuilding as T
import Target.StdModel as T
open T.Ty
open T.Con
open T.Tm
open T._∈_
open T.OPE
open T.Sub
open T._~_
open T._~ₛ_

open import CConv
open import BackTranslate

-- coercion shuffling
------------------------------------------------------------

coe-π₁ : ∀ {A A' B B'} (p : A ≡ A')(q : B ≡ B')(t : S.Tm ∙ (A * B))
        → π₁ (coe (S.Tm ∙ & (_*_ & p ⊗ q)) t) ≡ coe (S.Tm ∙ & p) (π₁ t)
coe-π₁ refl refl t = refl

coe-π₂ : ∀ {A A' B B'} (p : A ≡ A')(q : B ≡ B')(t : S.Tm ∙ (A * B))
        → π₂ (coe (S.Tm ∙ & (_*_ & p ⊗ q)) t) ≡ coe (S.Tm ∙ & q) (π₂ t)
coe-π₂ refl refl t = refl

*&⁻¹ : ∀ {A A' B B'}(p : A ≡ A')(q : B ≡ B') → (S.Ty._*_  & p ⊗ q ⁻¹) ≡ _*_ & (p ⁻¹) ⊗ (q ⁻¹)
*&⁻¹ refl refl = refl

------------------------------------------------------------

Ty⁻⁺ : ∀ A → Ty⁻ (Ty⁺ A) ≡ A
Ty⁻⁺ 𝔹       = refl
Ty⁻⁺ Top     = refl
Ty⁻⁺ (A * B) = S._*_ & Ty⁻⁺ A ⊗ Ty⁻⁺ B
Ty⁻⁺ (A ⇒ B) = S._⇒_ & Ty⁻⁺ A ⊗ Ty⁻⁺ B

Con⁻⁺ : ∀ Γ → Con⁻ (Con⁺ Γ) ≡ Γ
Con⁻⁺ ∙       = refl
Con⁻⁺ (Γ ▶ A) = _▶_ & Con⁻⁺ Γ ⊗ Ty⁻⁺ A

mutual
  sym≤ : ∀ {A}{t t'} → t ≤ t' → t' ≥ coe (S.Tm ∙ & (Ty⁻⁺ A ⁻¹)) t
  sym≤ {𝔹} (inl (p , q)) = inl (q , p)
  sym≤ {𝔹} (inr (p , q)) = inr (q , p)
  sym≤ {Top}   p = tt
  sym≤ {A * B} {t} {t'} (p , q) =
    (coe ((π₁ t' ≥_) & (coe-π₁ _ _ _ ⁻¹ ◾ (λ x → π₁ (coe (S.Tm ∙ & x) t)) & (*&⁻¹ _ _ ⁻¹) ))
         (sym≤ p))
    , coe ((π₂ t' ≥_) & (coe-π₂ _ _ _ ⁻¹ ◾ (λ x → π₂ (coe (S.Tm ∙ & x) t)) & (*&⁻¹ _ _ ⁻¹)))
          (sym≤ q)
  sym≤ {A ⇒ B} {t} {t'} p {a} {a'} q =
    coe
       ((app⁺ t' a ≥_) &
         J (λ A eq → ∀ t →
                coe (S.Tm ∙ & (Ty⁻⁺ B ⁻¹)) (app t (coe (S.Tm ∙ & eq) a'))
                ≡ app (coe (S.Tm ∙ & (_⇒_ & eq ⊗ Ty⁻⁺ B ⁻¹)) t) a')
           (λ t →
             J (λ _ eq → ∀ t →
                      coe (S.Tm ∙ & (eq ⁻¹)) (app t a')
                      ≡ app (coe (S.Tm ∙ & (refl ⊗ eq ⁻¹)) t) a')
               (λ t → refl)
               (Ty⁻⁺ B) t)
           (Ty⁻⁺ A) t)
       (sym≤ (p (sym≥ q)))

  sym≥ : ∀ {A}{t t'} → t ≥ t' → coe (S.Tm ∙ & Ty⁻⁺  A) t' ≤ t
  sym≥ {𝔹} (inl (p , q)) = inl (q , p)
  sym≥ {𝔹} (inr (p , q)) = inr (q , p)
  sym≥ {Top}   p = tt
  sym≥ {A * B} {t} {t'} (p , q) =
     (coe ((_≤ π₁ t) & (coe-π₁ (Ty⁻⁺ A)(Ty⁻⁺ B) t' ⁻¹)) (sym≥ p))
    , coe ((_≤ π₂ t) & (coe-π₂ (Ty⁻⁺ A)(Ty⁻⁺ B) t' ⁻¹)) (sym≥ q)
  sym≥ {A ⇒ B} {t} {t'} p {a} {a'} q =
    coe
      ((_≤ app⁺ t a') &
        J (λ A eq → ∀ a →
               coe (S.Tm ∙ & Ty⁻⁺ B) (app t' (coe (S.Tm ∙ & (eq ⁻¹)) a))
               ≡ app (coe (S.Tm ∙ & (_⇒_ & eq ⊗ Ty⁻⁺ B)) t') a)
          (λ a → J (λ B eq → ∀ a → coe (S.Tm ∙ & eq) (app t' a)
                              ≡ app (coe (S.Tm ∙ & (refl ⊗ eq)) t') a)
                    (λ a → refl)
                    (Ty⁻⁺ B) a)
          (Ty⁻⁺ A) a)
      (sym≥ (p (sym≤ q)))

Tm⁻' : ∀ {A} → T.Tm ∙ (Ty⁺ A) → S.Tm ∙ A
Tm⁻' t = coe (S.Tm ∙ & Ty⁻⁺ _) (Tm⁻ t)

≤r : ∀ {A}{t : S.Tm ∙ A}{t' t''} → t ≤ t' → t ≤ t'' → t' T.≈ t''
≤r {𝔹} (inl (p , q)) (inl (r , s)) = inl (q , s)
≤r {𝔹} (inl (p , q)) (inr (r , s)) = ⊥-elim (S.consistent (p ~⁻¹ ~◾ r))
≤r {𝔹} (inr (p , q)) (inl (r , s)) = ⊥-elim (S.consistent (r ~⁻¹ ~◾ p))
≤r {𝔹} (inr (p , q)) (inr (r , s)) = inr (q , s)
≤r {Top} p q = tt
≤r {A * B} (p , q) (r , s) = ≤r p r , ≤r q s
≤r {A ⇒ B} {t} {t'} {t''} p q {a} {a'} r =
  ≤r {B} (p {Tm⁻' a}{a} (sym≥ (Tm≥⁻' a))) (q {Tm⁻' a}{a'}(sym≥ (Tm≥⁻' a) ≤◾ r))

abstraction : ∀ {A}{t t' : S.Tm ∙ A} → t S.≈ t' → Tm⁺ t T.≈ Tm⁺ t'
abstraction {A}{t}{t'} p = ≤r (Tm≤⁺' t) (p ◾≤ Tm≤⁺' t')
