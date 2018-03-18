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

Ty⁻⁺ : ∀ A → Ty⁻ (Ty⁺ A) ≡ A
Ty⁻⁺ 𝔹       = refl
Ty⁻⁺ Top     = refl
Ty⁻⁺ (A * B) = S._*_ & Ty⁻⁺ A ⊗ Ty⁻⁺ B
Ty⁻⁺ (A ⇒ B) = S._⇒_ & Ty⁻⁺ A ⊗ Ty⁻⁺ B

Con⁻⁺ : ∀ Γ → Con⁻ (Con⁺ Γ) ≡ Γ
Con⁻⁺ ∙       = refl
Con⁻⁺ (Γ ▶ A) = _▶_ & Con⁻⁺ Γ ⊗ Ty⁻⁺ A

Tm⁻' : ∀ {A} → T.Tm ∙ (Ty⁺ A) → S.Tm ∙ A
Tm⁻' t = coe (S.Tm ∙ & Ty⁻⁺ _) (Tm⁻ t)

-- Tm⁺' : ∀ {A} → S.Tm ∙ (Ty⁻ A) → T.Tm ∙ A
-- Tm⁺' t = coe (S.Tm ∙ & Ty⁻⁺ _) (Tm⁻ t)

-- (a' > Tm⁻ a') → (Tm⁻ a' < Tm⁺ (Tm⁻ a')) →  a' ≈ Tm⁺ (Tm⁻ a')
-- likewise the other direction

mutual
  Tm≈⁺ : ∀ {A}{t t' : S.Tm ∙ A} → t S.≈ t' → Tm⁺ t T.≈ Tm⁺ t'
  Tm≈⁺ {𝔹} (inl (p , q)) = inl (~⁺ p , ~⁺ q)
  Tm≈⁺ {𝔹} (inr (p , q)) = inr (~⁺ p , ~⁺ q)
  Tm≈⁺ {Top}   p = tt
  Tm≈⁺ {A * B} (p , q) = (Tm≈⁺ p) , (Tm≈⁺ q)
  Tm≈⁺ {A ⇒ B} {t} {t'} p {a} {a'} q =
         T.≈refl {t = Tm⁺ t} {!!}
    T.≈◾ Tm≈⁺ {B} {app t (Tm⁻' a)}{app t' (Tm⁻' a')} (p (Tm≈⁻' q))
    T.≈◾ T.≈refl {t = Tm⁺ t'} {!!}

  Tm≈⁻ : ∀ {A}{t t' : T.Tm ∙ A} → t T.≈ t' → Tm⁻ t S.≈ Tm⁻ t'
  Tm≈⁻ {𝔹} (inl (p , q)) = inl (~⁻ p , ~⁻ q)
  Tm≈⁻ {𝔹} (inr (p , q)) = inr (~⁻ p , ~⁻ q)
  Tm≈⁻ {Top} p = tt
  Tm≈⁻ {A * B} (p , q) = (Tm≈⁻ p) , (Tm≈⁻ q)
  Tm≈⁻ {A ⇒⁺ B} {t} {t'} p {a} {a'} q =
    {!Tm≈⁻ {B} {app⁺ t (Tm⁺ a)}{app ? ?}!}
  Tm≈⁻ {A ⇒ B} {t} {t'} p {a} {a'} q = {!!}

  Tm≈⁻' : ∀ {A}{t t' : T.Tm ∙ (Ty⁺ A)} → t T.≈ t' → Tm⁻' t S.≈ Tm⁻' t'
  Tm≈⁻' {A} {t} {t'} p =
    J (λ _ eq → coe (S.Tm ∙ & eq) (Tm⁻ t) S.≈ coe (S.Tm ∙ & eq) (Tm⁻ t')) (Tm≈⁻ p) (Ty⁻⁺ A)

-- Ty⁻ (Ty⁺ A) ≡ A

-- ≤≥l : ∀ {A}{t : S.Tm ∙ A}{t' t''} → t ≤ t' → t' ≥ t'' → t S.≈ coe (S.Tm ∙ & Ty⁻⁺ A) t''
-- ≤≥l {𝔹} (inl (p , q)) (inl (r , s)) = inl (p , s)
-- ≤≥l {𝔹} (inl (p , q)) (inr (r , s)) = ⊥-elim (T.consistent (q ~⁻¹ ~◾ r))
-- ≤≥l {𝔹} (inr (p , q)) (inl (r , s)) = ⊥-elim (T.consistent (r ~⁻¹ ~◾ q))
-- ≤≥l {𝔹} (inr (p , q)) (inr (r , s)) = inr (p , s)
-- ≤≥l {Top}   p q = tt
-- ≤≥l {A * B} {t} {t'} {t''} (p , q) (r , s) =
--   (coe {!!} (≤≥l p r)) , coe {!!} (≤≥l q s)
-- ≤≥l {A ⇒ B} {t} {t'} {t''} p q {a} {a'} r =
--   coe {!!} (≤≥l {B} (p {a}{Tm⁺ a} (Tm≤⁺' a)) (q {Tm⁺ a}{Tm⁻ (Tm⁺ a')}
--            ({!!} ◾≥ Tm≥⁻' (Tm⁺ a'))))

-- -- sym≤ : ∀ {A}{t : S.Tm ∙ A}{t'} → t ≤ t' → t' ≥ coe (S.Tm ∙ & (Ty⁻⁺ A ⁻¹)) t
-- -- sym≤ {𝔹} (inl (p , q)) = inl (q , p)
-- -- sym≤ {𝔹} (inr (p , q)) = inr (q , p)
-- -- sym≤ {Top} p = tt
-- -- sym≤ {A * B} {t} {t'} (p , q) = {!!}
-- -- sym≤ {A ⇒ B} {t} {t'} p {a} {a'} q =
-- --   {!!}

-- sym≥ : ∀ {A}{t : T.Tm ∙ (Ty⁺ A)}{t'} → t ≥ t' → coe (S.Tm ∙ & Ty⁻⁺  A) t' ≤ t
-- sym≥ {𝔹} (inl (p , q)) = inl (q , p)
-- sym≥ {𝔹} (inr (p , q)) = inr (q , p)
-- sym≥ {Top}   p = tt
-- sym≥ {A * B} {t} {t'} (p , q) =
--   (coe ((_≤ π₁ t) & {!!}) (sym≥ p)) , coe ((_≤ π₂ t) & {!!}) (sym≥ q)
-- sym≥ {A ⇒ B} {t} {t'} p {a} {a'} q =
--      {!!}
--   ◾≤ sym≥ {B} {T.Tm.app⁺ t (Tm⁺ a)} {S.Tm.app t' (Tm⁻ a')} (p {!!})
--   ≤◾ T.≈refl {t = t} {!sym≥ (Tm≥⁻' a')!}

-- ≤r : ∀ {A}{t : S.Tm ∙ A}{t' t''} → t ≤ t' → t ≤ t'' → t' T.≈ t''
-- ≤r {𝔹} (inl (p , q)) (inl (r , s)) = inl (q , s)
-- ≤r {𝔹} (inl (p , q)) (inr (r , s)) = ⊥-elim (S.consistent (p ~⁻¹ ~◾ r))
-- ≤r {𝔹} (inr (p , q)) (inl (r , s)) = ⊥-elim (S.consistent (r ~⁻¹ ~◾ p))
-- ≤r {𝔹} (inr (p , q)) (inr (r , s)) = inr (q , s)
-- ≤r {Top} p q = tt
-- ≤r {A * B} (p , q) (r , s) = ≤r p r , ≤r q s
-- ≤r {A ⇒ B} {t} {t'} {t''} p q {a} {a'} r =
--   ≤r {B} (p {Tm⁻' a}{a} (sym≥ (Tm≥⁻' a))) (q (sym≥ (Tm≥⁻' a) ≤◾ r))

-- abstraction : ∀ {A}{t t' : S.Tm ∙ A} → t S.≈ t' → Tm⁺ t T.≈ Tm⁺ t'
-- abstraction {A}{t}{t'} p = ≤r (Tm≤⁺' t) (p ◾≤ Tm≤⁺' t')
