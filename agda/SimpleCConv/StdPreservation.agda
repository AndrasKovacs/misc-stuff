{-# OPTIONS --without-K #-}

module StdPreservation where

open import Lib
open import StrictLib

import Source.Syntax as S
import Source.LogicalEqv as S
import Source.StdModel as S
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
open import Data.Bool

-- Preservation of standard semantics
------------------------------------------------------------

Tyᴾ : (A : S.Ty) → S.⟦ A ⟧Ty ≡ T.⟦ Ty⁺ A ⟧Ty
Tyᴾ 𝔹       = refl
Tyᴾ Top     = refl
Tyᴾ (A * B) = _×_ & Tyᴾ A ⊗ Tyᴾ B
Tyᴾ (A ⇒ B) = (λ x y → x → y) & Tyᴾ A ⊗ Tyᴾ B

Conᴾ : ∀ Γ → S.⟦ Γ ⟧Con ≡ T.⟦ Con⁺ Γ ⟧Con
Conᴾ ∙       = refl
Conᴾ (Γ ▶ A) = _×_ & Conᴾ Γ ⊗ Tyᴾ A

∈ᴾ : ∀ {Γ A}(x : A S.∈ Γ)
     → S.⟦ var x ⟧Tm ≃ T.⟦ var (∈⁺ x) ⟧Tm
∈ᴾ {A = A} (vz {Γ}) =
   ap2̃̃ (λ Γ A → ₂ {A = Γ}{λ _ → A}) (Conᴾ Γ) (Tyᴾ A ~)
∈ᴾ {A = A} (vs {B} {Γ} x) =
   ap4̃̃ (λ Γ A B (f : Γ → A) → (λ (γ : Γ × B) → f (₁ γ)))
       (Conᴾ Γ) (Tyᴾ A ~) (Tyᴾ B ~)
       (∈ᴾ x)

Tmᴾ : ∀ {Γ A}(t : S.Tm Γ A) → S.⟦ t ⟧Tm ≃ T.⟦ Tm⁺ t ⟧Tm
Tmᴾ (var x)   = ∈ᴾ x
Tmᴾ {Γ} tt    = ap̃̃ (λ Γ → (λ (γ : Γ) → tt)) (Conᴾ Γ)
Tmᴾ {Γ} true  = ap̃̃ (λ Γ → (λ (γ : Γ) → true)) (Conᴾ Γ)
Tmᴾ {Γ} false = ap̃̃ (λ Γ → (λ (γ : Γ) → false)) (Conᴾ Γ)
Tmᴾ {Γ} {A} (if t u v) =
  ap5̃̃ (λ Γ A (t : Γ → Bool) (u v : Γ → A)
         → (λ γ → if (t γ) then (u γ) else (v γ)))
       (Conᴾ Γ) (Tyᴾ A ~) (Tmᴾ t) (Tmᴾ u) (Tmᴾ v)
Tmᴾ {Γ} (π₁ {A}{B} t) =
  ap4̃̃ (λ Γ A B (t : Γ → A × B) → (λ γ → ₁ (t γ)))
      (Conᴾ Γ) (Tyᴾ A ~) (Tyᴾ B ~) (Tmᴾ t)
Tmᴾ {Γ} (π₂ {A}{B} t) =
  ap4̃̃ (λ Γ A B (t : Γ → A × B) → (λ γ → ₂ (t γ)))
      (Conᴾ Γ) (Tyᴾ A ~) (Tyᴾ B ~) (Tmᴾ t)
Tmᴾ {Γ} (_,_ {A} {B} t u) =
  ap5̃̃ (λ Γ A B (t : Γ → A) (u : Γ → B) → λ γ → (A × B) ∋ (t γ , u γ))
       (Conᴾ Γ) (Tyᴾ A ~) (Tyᴾ B ~) (Tmᴾ t) (Tmᴾ u)
Tmᴾ {Γ} (app {A}{B} t u) =
  ap5̃̃ (λ Γ A B (t : Γ → A → B)(u : Γ → A) → λ γ → t γ (u γ))
      (Conᴾ Γ) (Tyᴾ A ~) (Tyᴾ B ~) (Tmᴾ t) (Tmᴾ u)
Tmᴾ {Γ} (lam {A} {B} t) with T.open' (Con⁺ Γ) | T.⟦∘ₛ⟧ (T.close (Con⁺ Γ)) (T.open' (Con⁺ Γ)) ⁻¹ ◾ T.⟦~ₛ⟧ (T.close-open {Con⁺ Γ})
... | ∙ , openΓ | clopen
  rewrite
      T.⟦Tmₛ⟧ ((T.close (Con⁺ Γ) T.∘ₛ (∙ , π₁ (var (vz {Γ = ∙}))))
               , π₂ (var vz)) (Tm⁺ t)
    | T.⟦∘ₛ⟧ (T.close (Con⁺ Γ)) (∙ , π₁ {B = Ty⁺ A}(var (vz {Γ = ∙})))
    | (λ f → (λ γ α → T.⟦ Tm⁺ t ⟧Tm (f γ , α))) & clopen
    | T.⟦idₛ⟧ {Con⁺ Γ}
    = ap4̃̃ (λ Γ A B (t : (Γ × A) → B) → λ γ α → t (γ , α))
          (Conᴾ Γ) (Tyᴾ A ~) (Tyᴾ B ~) (Tmᴾ t)

Tmᴾ' : ∀ {Γ A}(t : S.Tm Γ A)
  → coe ((λ x y → x → y) & Conᴾ Γ ⊗ Tyᴾ A) S.⟦ t ⟧Tm ≡ T.⟦ Tm⁺ t ⟧Tm
Tmᴾ' {Γ}{A} t = coe-coe ((λ x y → x → y) & Conᴾ Γ ⊗ Tyᴾ A)
                        (ty (Tmᴾ t))
                        (S.⟦ t ⟧Tm)
              ◾ Tmᴾ t .tm
