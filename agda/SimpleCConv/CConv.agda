
{-# OPTIONS --without-K #-}

module CConv where

open import Lib
import Source as S
import Target as T
import ClosureBuilding as T

Ty⁺ : S.Ty → T.Ty
Ty⁺ S.𝔹       = T.𝔹
Ty⁺ (A S.⇒ B) = Ty⁺ A T.⇒⁺ Ty⁺ B

Con⁺ : S.Con → T.Con
Con⁺ S.∙       = T.∙
Con⁺ (Γ S.▶ A) = Con⁺ Γ T.▶ Ty⁺ A

∈⁺ : ∀ {Γ A} → A S.∈ Γ → Ty⁺ A T.∈ Con⁺ Γ
∈⁺ S.vz     = T.vz
∈⁺ (S.vs x) = T.vs (∈⁺ x)

Tm⁺ : ∀ {Γ A} → S.Tm Γ A → T.Tm (Con⁺ Γ) (Ty⁺ A)
Tm⁺ S.true       = T.true
Tm⁺ S.false      = T.false
Tm⁺ (S.if t u v) = T.if (Tm⁺ t) (Tm⁺ u) (Tm⁺ v)
Tm⁺ (S.var x)    = T.var (∈⁺ x)
Tm⁺ (S.lam t)    = T.lam⁺ (Tm⁺ t)
Tm⁺ (S.app t u)  = T.app⁺ (Tm⁺ t) (Tm⁺ u)
