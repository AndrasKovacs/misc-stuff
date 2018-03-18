
{-# OPTIONS --without-K #-}

module Abstraction where

open import Lib
import Source.Syntax as S
import Source.LogicalEqv as S
import Source.StdModel as S
import Target.Syntax as T
import Target.LogicalEqv as T

open import CConv
open import BackTranslate

Ty⁻⁺ : ∀ A → Ty⁻ (Ty⁺ A) ≡ A
Ty⁻⁺ S.𝔹       = refl
Ty⁻⁺ S.Top     = refl
Ty⁻⁺ (A S.* B) = S._*_ & Ty⁻⁺ A ⊗ Ty⁻⁺ B
Ty⁻⁺ (A S.⇒ B) = S._⇒_ & Ty⁻⁺ A ⊗ Ty⁻⁺ B

Con⁻⁺ : ∀ Γ → Con⁻ (Con⁺ Γ) ≡ Γ
Con⁻⁺ S.∙ = refl
Con⁻⁺ (Γ S.▶ A) = S._▶_ & Con⁻⁺ Γ ⊗ Ty⁻⁺ A

Tm⁻' : ∀ {A} → T.Tm T.∙ (Ty⁺ A) → S.Tm S.∙ A
Tm⁻' {A} t = coe (S.Tm S.∙ & Ty⁻⁺ A) (Tm⁻ t)

-- abstraction : ∀ {A}{t t' : S.Tm S.∙ A} → t S.≈ t' → Tm⁺ t T.≈ Tm⁺ t'
-- abstraction {S.𝔹} (inl (p , q)) = inl ((~⁺ p) , (~⁺ q))
-- abstraction {S.𝔹} (inr (p , q)) = inr ((~⁺ p) , (~⁺ q))
-- abstraction {S.Top} p = tt
-- abstraction {A S.* B} (p , q) = abstraction p , abstraction q
-- abstraction {A S.⇒ B} {t} {t'} p {a} {a'} q =
--        T.≈refl {t = Tm⁺ t} {!!}
--   T.≈◾ (abstraction {B} (p {Tm⁻' a}{Tm⁻' a'} {!!}))
--   T.≈◾ T.≈refl {t = Tm⁺ t'} {!!}




triangle : ∀ {A}{t : S.Tm S.∙ A}{t' t''} → t ≈ t' → t ≈ t'' → t' T.≈ t''
triangle {S.𝔹} (inl (p , q)) (inl (r , s)) = inl (q , s)
triangle {S.𝔹} (inl (p , q)) (inr (r , s)) = ⊥-elim (S.consistent (p S.~⁻¹ S.~◾ r))
triangle {S.𝔹} (inr (p , q)) (inl (r , s)) = ⊥-elim (S.consistent (r S.~⁻¹ S.~◾ p))
triangle {S.𝔹} (inr (p , q)) (inr (r , s)) = inr (q , s)
triangle {S.Top}   p q = tt
triangle {A S.* B} (p , q) (r , s) = triangle p r , triangle q s
triangle {A S.⇒ B} p q {a} {a'} r = triangle {B} (p {!!}) (q {!!})
  -- triangle (p (⁻≈' a)) (q ((⁻≈' a) ≈◾ r))

-- abstraction : ∀ {A}{t t' : S.Tm S.∙ A} → t S.≈ t' → Tm⁺ t T.≈ Tm⁺ t'
-- abstraction {A} {t} {t'} p = triangle {A} (Tm≈⁺' t) (p ◾≈ Tm≈⁺' t')
