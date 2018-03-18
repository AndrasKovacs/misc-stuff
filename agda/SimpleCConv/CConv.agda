{-# OPTIONS --without-K #-}

module CConv where

open import Lib

import Source.Syntax as S
import Source.LogicalEqv as S
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
open T.Ty
open T.Con
open T.Tm
open T._∈_
open T.OPE
open T.Sub
open T._~_
open T._~ₛ_

-- Closure conversion
--------------------------------------------------------------------------------

Ty⁺ : S.Ty → T.Ty
Ty⁺ 𝔹       = 𝔹
Ty⁺ Top     = Top
Ty⁺ (A * B) = Ty⁺ A * Ty⁺ B
Ty⁺ (A ⇒ B) = Ty⁺ A ⇒⁺ Ty⁺ B

Con⁺ : S.Con → T.Con
Con⁺ ∙       = ∙
Con⁺ (Γ S.▶ A) = Con⁺ Γ T.▶ Ty⁺ A

∈⁺ : ∀ {Γ A} → A S.∈ Γ → Ty⁺ A T.∈ Con⁺ Γ
∈⁺ vz     = vz
∈⁺ (vs x) = vs (∈⁺ x)

Tm⁺ : ∀ {Γ A} → S.Tm Γ A → T.Tm (Con⁺ Γ) (Ty⁺ A)
Tm⁺ true       = true
Tm⁺ false      = false
Tm⁺ (S.if t u v) = T.if (Tm⁺ t) (Tm⁺ u) (Tm⁺ v)
Tm⁺ (S.var x)    = T.var (∈⁺ x)
Tm⁺ (S.lam t)    = T.lam⁺ (Tm⁺ t)
Tm⁺ (S.app t u)  = T.app⁺ (Tm⁺ t) (Tm⁺ u)
Tm⁺ S.tt         = T.tt
Tm⁺ (S.π₁ t)     = T.π₁ (Tm⁺ t)
Tm⁺ (S.π₂ t)     = T.π₂ (Tm⁺ t)
Tm⁺ (t S., u)    = Tm⁺ t T., Tm⁺ u

-- Def. eq. preservation
--------------------------------------------------------------------------------

OPE⁺ : ∀ {Γ Δ} → S.OPE Γ Δ → T.OPE (Con⁺ Γ) (Con⁺ Δ)
OPE⁺ ∙        = ∙
OPE⁺ (drop σ) = drop (OPE⁺ σ)
OPE⁺ (keep σ) = keep (OPE⁺ σ)

∈ₑ⁺ : ∀ {Γ Δ A}(σ : S.OPE Γ Δ)(x : A S.∈ Δ) → ∈⁺ (S.∈ₑ σ x) ≡ T.∈ₑ (OPE⁺ σ) (∈⁺ x)
∈ₑ⁺ ∙ ()
∈ₑ⁺ (drop σ) x      = vs & ∈ₑ⁺ σ x
∈ₑ⁺ (keep σ) vz     = refl
∈ₑ⁺ (keep σ) (vs x) = vs & ∈ₑ⁺ σ x

idₑ⁺ : ∀ {Γ} → OPE⁺ (S.idₑ {Γ}) ≡ T.idₑ
idₑ⁺ {∙}     = refl
idₑ⁺ {Γ ▶ A} = keep & idₑ⁺ {Γ}

Tmₑ⁺ :
  ∀ {Γ Δ A}(σ : S.OPE Γ Δ)(t : S.Tm Δ A) → Tm⁺ (S.Tmₑ σ t) T.~ T.Tmₑ (OPE⁺ σ) (Tm⁺ t)
Tmₑ⁺ σ true       = ~refl
Tmₑ⁺ σ false      = ~refl
Tmₑ⁺ σ (if t u v) = if (Tmₑ⁺ σ t) (Tmₑ⁺ σ u) (Tmₑ⁺ σ v)
Tmₑ⁺ σ (var x)    = T.≡~ (var & ∈ₑ⁺ σ x)
Tmₑ⁺ σ (lam t)    = T.lam⁺~ (Tmₑ⁺ (keep σ) t) ~◾ T.Tmₑ-lam⁺ (OPE⁺ σ) (Tm⁺ t) ~⁻¹
Tmₑ⁺ σ (app t u)  = app⁺ (Tmₑ⁺ σ t) (Tmₑ⁺ σ u)
Tmₑ⁺ σ tt         = ~refl
Tmₑ⁺ σ (π₁ t)     = π₁ (Tmₑ⁺ σ t)
Tmₑ⁺ σ (π₂ t)     = π₂ (Tmₑ⁺ σ t)
Tmₑ⁺ σ (t , u)    = Tmₑ⁺ σ t , Tmₑ⁺ σ u

Sub⁺ : ∀ {Γ Δ} → S.Sub Γ Δ → T.Sub (Con⁺ Γ) (Con⁺ Δ)
Sub⁺ ∙       = ∙
Sub⁺ (σ , t) = Sub⁺ σ , Tm⁺ t

ₛ∘ₑ⁺ : ∀ {Γ Δ Σ}(σ : S.Sub Δ Σ)(δ : S.OPE Γ Δ) → Sub⁺ (σ S.ₛ∘ₑ δ) T.~ₛ Sub⁺ σ T.ₛ∘ₑ OPE⁺ δ
ₛ∘ₑ⁺ ∙       δ = T.~ₛrefl _
ₛ∘ₑ⁺ (σ , t) δ = ₛ∘ₑ⁺ σ δ , Tmₑ⁺ δ t

dropₛ⁺ : ∀ {Γ Δ A} (σ : S.Sub Γ Δ) → Sub⁺ (S.dropₛ {A} σ) T.~ₛ T.dropₛ (Sub⁺ σ)
dropₛ⁺ σ = ₛ∘ₑ⁺ σ S.wk T.~ₛ◾ T.≡~ₛ ((Sub⁺ σ T.ₛ∘ₑ_) & (drop & idₑ⁺))

keepₛ⁺ : ∀ {Γ Δ A} (σ : S.Sub Γ Δ) → Sub⁺ (S.keepₛ {A} σ) T.~ₛ T.keepₛ (Sub⁺ σ)
keepₛ⁺ σ = dropₛ⁺ σ , ~refl

idₛ⁺ : ∀ {Γ} → Sub⁺ (S.idₛ {Γ}) T.~ₛ T.idₛ
idₛ⁺ {∙}     = ∙
idₛ⁺ {Γ ▶ A} = keepₛ⁺ (S.idₛ{Γ}) T.~ₛ◾ T.keepₛ~ (idₛ⁺{Γ})

∈ₛ⁺ :
  ∀ {Γ Δ A}(σ : S.Sub Γ Δ)(x : A S.∈ Δ) → Tm⁺ (S.∈ₛ σ x) T.~ T.Tmₛ (Sub⁺ σ) (Tm⁺ (S.var x))
∈ₛ⁺ (σ , _) vz     = ~refl
∈ₛ⁺ (σ , _) (vs x) = ∈ₛ⁺ σ x

Tmₛ⁺ :
  ∀ {Γ Δ A}(σ : S.Sub Γ Δ)(t : S.Tm Δ A) → Tm⁺ (S.Tmₛ σ t) T.~ T.Tmₛ (Sub⁺ σ) (Tm⁺ t)
Tmₛ⁺ σ true = ~refl
Tmₛ⁺ σ false = ~refl
Tmₛ⁺ σ (if t u v) = if (Tmₛ⁺ σ t) (Tmₛ⁺ σ u) (Tmₛ⁺ σ v)
Tmₛ⁺ σ (var x) = ∈ₛ⁺ σ x
Tmₛ⁺ σ (lam t) =
       T.lam⁺~ (Tmₛ⁺ (S.keepₛ σ) t
  ~◾ T.Tmₛ~t (keepₛ⁺ σ) (Tm⁺ t))
  ~◾ T.Tmₛ-lam⁺ (Sub⁺ σ) (Tm⁺ t) ~⁻¹
Tmₛ⁺ σ (app t u) = app⁺ (Tmₛ⁺ σ t) (Tmₛ⁺ σ u)
Tmₛ⁺ σ tt        = ~refl
Tmₛ⁺ σ (π₁ t)    = π₁ (Tmₛ⁺ σ t)
Tmₛ⁺ σ (π₂ t)    = π₂ (Tmₛ⁺ σ t)
Tmₛ⁺ σ (t , u)   = Tmₛ⁺ σ t , Tmₛ⁺ σ u

~⁺ : ∀ {Γ A}{t t' : S.Tm Γ A} → t S.~ t' → Tm⁺ t T.~ Tm⁺ t'
~⁺ (β t t') =
       T.β⁺ (Tm⁺ t) (Tm⁺ t')
  ~◾ T.Tmₛ~t ((idₛ⁺ T.~ₛ⁻¹) , ~refl) (Tm⁺ t)
  ~◾ Tmₛ⁺ (S.idₛ , t') t ~⁻¹
~⁺ {Γ} {t = t} {t'} (η {A} {B} p) =
       T.η⁺ (Tm⁺ t)
  ~◾ T.lam⁺~ (app⁺ (T.≡~ ((λ x → T.Tmₑ (drop x) (Tm⁺ t)) & (idₑ⁺ ⁻¹)) ~◾ Tmₑ⁺ S.wk t ~⁻¹) ~refl
          ~◾ ~⁺ p ~◾ app⁺ (Tmₑ⁺ S.wk t' ~◾ T.≡~ ((λ x → T.Tmₑ (drop x) (Tm⁺ t')) & idₑ⁺)) ~refl)
  ~◾ T.η⁺ (Tm⁺ t') ~⁻¹
~⁺ (lam t) = T.lam⁺~ (~⁺ t)
~⁺ (app t u) = app⁺ (~⁺ t) (~⁺ u)
~⁺ true = true
~⁺ false = false
~⁺ (if t u v) = if (~⁺ t) (~⁺ u) (~⁺ v)
~⁺ ~refl = ~refl
~⁺ (t ~⁻¹) = ~⁺ t ~⁻¹
~⁺ (t ~◾ u) = ~⁺ t ~◾ ~⁺ u
~⁺ (π₁ t)    = π₁ (~⁺ t)
~⁺ (π₂ t)    = π₂ (~⁺ t)
~⁺ (t , u)   = ~⁺ t , ~⁺ u
~⁺ (π₁β t u) = π₁β (Tm⁺ t) (Tm⁺ u)
~⁺ (π₂β t u) = π₂β (Tm⁺ t) (Tm⁺ u)
~⁺ (,η t)    = ,η (Tm⁺ t)
~⁺ ttη       = ttη

-- Forward relation
--------------------------------------------------------------------------------

infixr 4 _≤_
_≤_ : ∀ {A} → S.Tm ∙ A → T.Tm ∙ (Ty⁺ A) → Set
_≤_ {Top}   t t' = ⊤
_≤_ {A * B} t t' = (π₁ t ≤ π₁ t') × (π₂ t ≤ π₂ t')
_≤_ {𝔹}     t t' = (t S.~ true × (t' T.~ true)) ⊎ (t S.~ false × (t' T.~ false))
_≤_ {A ⇒ B} t t' = ∀ {a a'} → a ≤ a' → app t a ≤ app⁺ t' a'

infixr 4 _◾≤_
_◾≤_ : ∀ {A}{t t' : S.Tm ∙ A}{t'' : T.Tm ∙ (Ty⁺ A)} → t S.≈ t' → t' ≤ t'' → t ≤ t''
_◾≤_ {S.𝔹} (inl (p , q)) (inl (r , s)) = inl (p , s)
_◾≤_ {S.𝔹} (inl (p , q)) (inr (r , s)) = inr ((p S.~◾ q S.~⁻¹ S.~◾ r) , s)
_◾≤_ {S.𝔹} (inr (p , q)) (inl (r , s)) = inl ((p S.~◾ q S.~⁻¹ S.~◾ r) , s)
_◾≤_ {S.𝔹} (inr (p , q)) (inr (r , s)) = inr (p , s)
_◾≤_ {A S.* B} (p , q) (r , s) = (p ◾≤ r) , (q ◾≤ s)
_◾≤_ {S.Top} p q = tt
_◾≤_ {A S.⇒ B} p q r = p S.≈refl ◾≤ q r

infixr 4 _~◾≤_
_~◾≤_ : ∀ {A}{t t' : S.Tm ∙ A}{t'' : T.Tm ∙ (Ty⁺ A)} → t S.~ t' → t' ≤ t'' → t ≤ t''
p ~◾≤ q = S.~≈ p ◾≤ q

infixl 5 _≤◾_
_≤◾_ : ∀ {A}{t : S.Tm ∙ A}{t' t'' : T.Tm ∙ (Ty⁺ A)} → t ≤ t' → t' T.≈ t'' → t ≤ t''
_≤◾_ {𝔹} (inl (p , q)) (inl (r , s)) = inl (p , s)
_≤◾_ {𝔹} (inl (p , q)) (inr (r , s)) = inl (p , (s ~◾ r ~⁻¹ ~◾ q))
_≤◾_ {𝔹} (inr (p , q)) (inl (r , s)) = inr (p , (s ~◾ r ~⁻¹ ~◾ q))
_≤◾_ {𝔹} (inr (p , q)) (inr (r , s)) = inr (p , s)
_≤◾_ {Top}   p q = tt
_≤◾_ {A * B} (p , q) (r , s) = (p ≤◾ r) , (q ≤◾ s)
_≤◾_ {A ⇒ B} p q r = p r ≤◾ q T.≈refl

infixl 5 _≤◾~_
_≤◾~_ : ∀ {A}{t : S.Tm ∙ A}{t' t'' : T.Tm ∙ (Ty⁺ A)} → t ≤ t' → t' T.~ t'' → t ≤ t''
_≤◾~_ p q = p ≤◾ T.~≈ q

infixr 4 _≤ₛ_
_≤ₛ_ : ∀ {Γ} → S.Sub ∙ Γ → T.Sub ∙ (Con⁺ Γ) → Set
∙       ≤ₛ ∙        = ⊤
(σ , t) ≤ₛ (δ , t') = (σ ≤ₛ δ) × t ≤ t'

∈≤⁺ : ∀ {Γ A}(x : A S.∈ Γ) σ σ' → σ ≤ₛ σ' → S.∈ₛ σ x ≤ T.∈ₛ σ' (∈⁺ x)
∈≤⁺ vz (σ , x) (σ' , x₁) σ≤ = ₂ σ≤
∈≤⁺ (vs x) (σ , x₁) (σ' , x₂) σ≤ = ∈≤⁺ x σ σ' (₁ σ≤)

Tm≤⁺ : ∀ {Γ A}(t : S.Tm Γ A) σ σ' → σ ≤ₛ σ' → S.Tmₛ σ t ≤ T.Tmₛ σ' (Tm⁺ t)
Tm≤⁺ (var x) σ σ' σ≤ = ∈≤⁺ x σ σ' σ≤
Tm≤⁺ tt σ σ' σ≤ = tt
Tm≤⁺ true σ σ' σ≤ = inl (~refl , ~refl)
Tm≤⁺ false σ σ' σ≤ = inr (~refl , ~refl)
Tm≤⁺ (if t u v) σ σ' σ≤ with Tm≤⁺ t σ σ' σ≤
... | inl (p , q) =
      if p ~refl ~refl
  ~◾≤ true
  ~◾≤ Tm≤⁺ u σ σ' σ≤
  ≤◾~ true T.~⁻¹
  ≤◾~ if (q T.~⁻¹) ~refl ~refl
... | inr (p , q) =
      if p ~refl ~refl
  ~◾≤ false
  ~◾≤ Tm≤⁺ v σ σ' σ≤
  ≤◾~ false ~⁻¹
  ≤◾~ if (q ~⁻¹) ~refl ~refl
Tm≤⁺ (π₁ t) σ σ' σ≤ = Tm≤⁺ t σ σ' σ≤ .₁
Tm≤⁺ (π₂ t) σ σ' σ≤ = Tm≤⁺ t σ σ' σ≤ .₂
Tm≤⁺ (t , u) σ σ' σ≤ =
  (π₁β _ _  ~◾≤ Tm≤⁺ t σ σ' σ≤ ≤◾~ π₁β _ _ ~⁻¹) ,
  (π₂β _ _  ~◾≤ Tm≤⁺ u σ σ' σ≤ ≤◾~ π₂β _ _ ~⁻¹)
Tm≤⁺ (app t u) σ σ' σ≤ = Tm≤⁺ t σ σ' σ≤ (Tm≤⁺ u σ σ' σ≤)
Tm≤⁺ (lam t) σ σ' σ≤ {a}{a'} p =
      β _ _
  ~◾≤ S.≡~ (S.Tm-∘ₛ (S.keepₛ σ) (S.idₛ , a) t ⁻¹)
  ~◾≤ S.≡~ ((λ x → S.Tmₛ (x , a) t) & (S.assₛₑₛ _ _ _ ◾ S.idrₛ σ))
  ~◾≤ Tm≤⁺ t (σ , a) (σ' , a') (σ≤ , p)
  ≤◾~ T.≡~ ((λ x → T.Tmₛ (x , a') (Tm⁺ t)) &
           (T.idrₛ σ' ⁻¹ ◾ T.assₛₑₛ σ' T.wk (∙ , a') ⁻¹))
  ≤◾~ T.≡~ (T.Tm-∘ₛ (T.keepₛ σ') (∙ , a') (Tm⁺ t))
  ≤◾~ T.β⁺ (T.Tmₛ (T.keepₛ σ') (Tm⁺ t)) a' ~⁻¹
  ≤◾~ app⁺ (T.Tmₛ-lam⁺ σ' (Tm⁺ t)) ~refl ~⁻¹

Tm≤⁺' : ∀ {A}(t : S.Tm ∙ A) → t ≤ Tm⁺ t
Tm≤⁺' {A} t = coe (_≤_ & S.Tm-idₛ t ⊗ T.Tm-idₛ (Tm⁺ t)) (Tm≤⁺ t S.idₛ T.idₛ tt)
