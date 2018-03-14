
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

OPE⁺ : ∀ {Γ Δ} → S.OPE Γ Δ → T.OPE (Con⁺ Γ) (Con⁺ Δ)
OPE⁺ S.∙        = T.∙
OPE⁺ (S.drop σ) = T.drop (OPE⁺ σ)
OPE⁺ (S.keep σ) = T.keep (OPE⁺ σ)

∈ₑ⁺ : ∀ {Γ Δ A}(σ : S.OPE Γ Δ)(x : A S.∈ Δ) → ∈⁺ (S.∈ₑ σ x) ≡ T.∈ₑ (OPE⁺ σ) (∈⁺ x)
∈ₑ⁺ S.∙ ()
∈ₑ⁺ (S.drop σ) x        = T.vs & ∈ₑ⁺ σ x
∈ₑ⁺ (S.keep σ) S.vz     = refl
∈ₑ⁺ (S.keep σ) (S.vs x) = T.vs & ∈ₑ⁺ σ x

idₑ⁺ : ∀ {Γ} → OPE⁺ (S.idₑ {Γ}) ≡ T.idₑ
idₑ⁺ {S.∙}     = refl
idₑ⁺ {Γ S.▶ A} = T.keep & idₑ⁺ {Γ}

Tmₑ⁺ :
  ∀ {Γ Δ A}(σ : S.OPE Γ Δ)(t : S.Tm Δ A) → Tm⁺ (S.Tmₑ σ t) T.~ T.Tmₑ (OPE⁺ σ) (Tm⁺ t)
Tmₑ⁺ σ S.true       = T.~refl
Tmₑ⁺ σ S.false      = T.~refl
Tmₑ⁺ σ (S.if t u v) = T.if (Tmₑ⁺ σ t) (Tmₑ⁺ σ u) (Tmₑ⁺ σ v)
Tmₑ⁺ σ (S.var x)    = T.≡~ (T.var & ∈ₑ⁺ σ x)
Tmₑ⁺ σ (S.lam t)    = T.lam⁺~ (Tmₑ⁺ (S.keep σ) t) T.~◾ T.Tmₑ-lam⁺ (OPE⁺ σ) (Tm⁺ t) T.~⁻¹
Tmₑ⁺ σ (S.app t u)  = T.app⁺ (Tmₑ⁺ σ t) (Tmₑ⁺ σ u)

Sub⁺ : ∀ {Γ Δ} → S.Sub Γ Δ → T.Sub (Con⁺ Γ) (Con⁺ Δ)
Sub⁺ S.∙       = T.∙
Sub⁺ (σ S., t) = Sub⁺ σ T., Tm⁺ t

ₛ∘ₑ⁺ : ∀ {Γ Δ Σ}(σ : S.Sub Δ Σ)(δ : S.OPE Γ Δ) → Sub⁺ (σ S.ₛ∘ₑ δ) T.~ₛ Sub⁺ σ T.ₛ∘ₑ OPE⁺ δ
ₛ∘ₑ⁺ S.∙       δ = T.~ₛrefl _
ₛ∘ₑ⁺ (σ S., t) δ = ₛ∘ₑ⁺ σ δ T., Tmₑ⁺ δ t

dropₛ⁺ : ∀ {Γ Δ A} (σ : S.Sub Γ Δ) → Sub⁺ (S.dropₛ {A} σ) T.~ₛ T.dropₛ (Sub⁺ σ)
dropₛ⁺ σ = ₛ∘ₑ⁺ σ S.wk T.~ₛ◾ T.≡~ₛ ((Sub⁺ σ T.ₛ∘ₑ_) & (T.drop & idₑ⁺))

keepₛ⁺ : ∀ {Γ Δ A} (σ : S.Sub Γ Δ) → Sub⁺ (S.keepₛ {A} σ) T.~ₛ T.keepₛ (Sub⁺ σ)
keepₛ⁺ σ = dropₛ⁺ σ T., T.~refl

idₛ⁺ : ∀ {Γ} → Sub⁺ (S.idₛ {Γ}) T.~ₛ T.idₛ
idₛ⁺ {S.∙}     = T.∙
idₛ⁺ {Γ S.▶ A} = keepₛ⁺ (S.idₛ{Γ}) T.~ₛ◾ T.keepₛ~ (idₛ⁺{Γ})

∈ₛ⁺ :
  ∀ {Γ Δ A}(σ : S.Sub Γ Δ)(x : A S.∈ Δ) → Tm⁺ (S.∈ₛ σ x) T.~ T.Tmₛ (Sub⁺ σ) (Tm⁺ (S.var x))
∈ₛ⁺ (σ S., _) S.vz     = T.~refl
∈ₛ⁺ (σ S., _) (S.vs x) = ∈ₛ⁺ σ x

Tmₛ⁺ :
  ∀ {Γ Δ A}(σ : S.Sub Γ Δ)(t : S.Tm Δ A) → Tm⁺ (S.Tmₛ σ t) T.~ T.Tmₛ (Sub⁺ σ) (Tm⁺ t)
Tmₛ⁺ σ S.true = T.~refl
Tmₛ⁺ σ S.false = T.~refl
Tmₛ⁺ σ (S.if t u v) = T.if (Tmₛ⁺ σ t) (Tmₛ⁺ σ u) (Tmₛ⁺ σ v)
Tmₛ⁺ σ (S.var x) = ∈ₛ⁺ σ x
Tmₛ⁺ σ (S.lam t) =
       T.lam⁺~ (Tmₛ⁺ (S.keepₛ σ) t
  T.~◾ T.Tmₛ~t (keepₛ⁺ σ) (Tm⁺ t))
  T.~◾ T.Tmₛ-lam⁺ (Sub⁺ σ) (Tm⁺ t) T.~⁻¹
Tmₛ⁺ σ (S.app t u) = T.app⁺ (Tmₛ⁺ σ t) (Tmₛ⁺ σ u)

~⁺ : ∀ {Γ A}{t t' : S.Tm Γ A} → t S.~ t' → Tm⁺ t T.~ Tm⁺ t'
~⁺ (S.β t t') =
       T.β⁺ (Tm⁺ t) (Tm⁺ t')
  T.~◾ T.Tmₛ~t ((idₛ⁺ T.~ₛ⁻¹) T., T.~refl) (Tm⁺ t)
  T.~◾ Tmₛ⁺ (S.idₛ S., t') t T.~⁻¹
~⁺ {Γ} (S.η {A} {B} t) =
       T.η⁺ (Tm⁺ t)
  T.~◾ T.lam⁺~ {t = (T.app⁺ (T.Tmₑ T.wk (Tm⁺ t)) (T.var T.vz))}
               {(T.app⁺ (Tm⁺ (S.Tmₑ S.wk t)) (T.var T.vz))}
               (T.app⁺ (T.≡~ ((λ x → T.Tmₑ x (Tm⁺ t)) & (T.drop & (idₑ⁺ ⁻¹)))
                         T.~◾ Tmₑ⁺ S.wk t T.~⁻¹) T.~refl)
~⁺ (S.lam t) = T.lam⁺~ (~⁺ t)
~⁺ (S.app t u) = T.app⁺ (~⁺ t) (~⁺ u)
~⁺ S.true = T.true
~⁺ S.false = T.false
~⁺ (S.if t u v) = T.if (~⁺ t) (~⁺ u) (~⁺ v)
~⁺ S.~refl = T.~refl
~⁺ (t S.~⁻¹) = ~⁺ t T.~⁻¹
~⁺ (t S.~◾ u) = ~⁺ t T.~◾ ~⁺ u
