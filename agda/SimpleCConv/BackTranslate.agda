
{-# OPTIONS --without-K #-}

module BackTranslate where

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

import Target.Syntax as T
import Target.LogicalEqv as T
open T.Ty
open T.Con
open T.Tm
open T._∈_
open T.OPE
open T.Sub
open T._~_

--------------------------------------------------------------------------------

Ty⁻ : T.Ty → S.Ty
Ty⁻ 𝔹        = 𝔹
Ty⁻ Top      = Top
Ty⁻ (A *  B) = Ty⁻ A * Ty⁻ B
Ty⁻ (A ⇒⁺ B) = Ty⁻ A ⇒ Ty⁻ B
Ty⁻ (A ⇒  B) = Ty⁻ A ⇒ Ty⁻ B

Con⁻ : T.Con → S.Con
Con⁻ ∙       = ∙
Con⁻ (Γ ▶ A) = Con⁻ Γ ▶ Ty⁻ A

∈⁻ : ∀ {Γ A} → A T.∈ Γ → Ty⁻ A S.∈ Con⁻ Γ
∈⁻ vz     = vz
∈⁻ (vs x) = vs (∈⁻ x)

Tm⁻ : ∀ {Γ A} → T.Tm Γ A → S.Tm (Con⁻ Γ) (Ty⁻ A)
Tm⁻ (var x) = var (∈⁻ x)
Tm⁻ tt = tt
Tm⁻ true = true
Tm⁻ false = false
Tm⁻ (if t u v) = if (Tm⁻ t) (Tm⁻ u) (Tm⁻ v)
Tm⁻ (π₁ t) = π₁ (Tm⁻ t)
Tm⁻ (π₂ t) = π₂ (Tm⁻ t)
Tm⁻ (t , u) = Tm⁻ t , Tm⁻ u
Tm⁻ (pack t u) = lam (app (S.Tmₑ S.wk (Tm⁻ u)) (S.Tmₑ S.wk (Tm⁻ t) , var vz))
Tm⁻ (app⁺ t u) = app (Tm⁻ t) (Tm⁻ u)
Tm⁻ (lam t) = lam (S.Tmₑ (keep S.εₑ) (Tm⁻ t))
Tm⁻ (app t u) = app (Tm⁻ t) (Tm⁻ u)

-- Def. eq. preservation
--------------------------------------------------------------------------------

OPE⁻ : ∀ {Γ Δ} → T.OPE Γ Δ → S.OPE (Con⁻ Γ) (Con⁻ Δ)
OPE⁻ ∙        = ∙
OPE⁻ (drop σ) = drop (OPE⁻ σ)
OPE⁻ (keep σ) = keep (OPE⁻ σ)

∈ₑ⁻ : ∀ {Γ Δ A}(σ : T.OPE Γ Δ)(x : A T.∈ Δ) → ∈⁻ (T.∈ₑ σ x) ≡ S.∈ₑ (OPE⁻ σ) (∈⁻ x)
∈ₑ⁻ ∙ ()
∈ₑ⁻ (drop σ) x      = vs & ∈ₑ⁻ σ x
∈ₑ⁻ (keep σ) vz     = refl
∈ₑ⁻ (keep σ) (vs x) = vs & ∈ₑ⁻ σ x

idₑ⁻ : ∀ {Γ} → OPE⁻ (T.idₑ {Γ}) ≡ S.idₑ
idₑ⁻ {∙}     = refl
idₑ⁻ {Γ ▶ A} = keep & idₑ⁻ {Γ}

Tmₑ⁻ : ∀ {Γ Δ A}(σ : T.OPE Γ Δ)(t : T.Tm Δ A) → Tm⁻ (T.Tmₑ σ t) ≡ S.Tmₑ (OPE⁻ σ) (Tm⁻ t)
Tmₑ⁻ σ (var x) = var & ∈ₑ⁻ σ x
Tmₑ⁻ σ tt = refl
Tmₑ⁻ σ true = refl
Tmₑ⁻ σ false = refl
Tmₑ⁻ σ (if t u v) = if & Tmₑ⁻ σ t ⊗ Tmₑ⁻ σ u ⊗ Tmₑ⁻ σ v
Tmₑ⁻ σ (π₁ t) = π₁ & Tmₑ⁻ σ t
Tmₑ⁻ σ (π₂ t) = π₂ & Tmₑ⁻ σ t
Tmₑ⁻ σ (t , u) = _,_ & Tmₑ⁻ σ t ⊗ Tmₑ⁻ σ u
Tmₑ⁻ σ (pack t u) =
   lam &
     (app &
         (S.Tmₑ S.wk & Tmₑ⁻ σ u
            ◾ S.Tm-∘ₑ (OPE⁻ σ) S.wk (Tm⁻ u) ⁻¹
            ◾ (λ x → S.Tmₑ (drop x) (Tm⁻ u)) & (S.idrₑ (OPE⁻ σ) ◾ S.idlₑ (OPE⁻ σ) ⁻¹)
            ◾ S.Tm-∘ₑ S.wk (keep (OPE⁻ σ)) (Tm⁻ u))
       ⊗ (_, var vz) & (S.Tmₑ S.wk & Tmₑ⁻ σ t ◾ S.Tm-∘ₑ (OPE⁻ σ) S.wk _ ⁻¹
            ◾ (λ x → S.Tmₑ (drop x) (Tm⁻ t)) & (S.idrₑ (OPE⁻ σ) ◾ S.idlₑ (OPE⁻ σ) ⁻¹)
            ◾ S.Tm-∘ₑ S.wk (keep (OPE⁻ σ)) _))
Tmₑ⁻ σ (app⁺ t u) = app & Tmₑ⁻ σ t ⊗ Tmₑ⁻ σ u
Tmₑ⁻ σ (lam t) =
  lam & ((λ x → S.Tmₑ (keep x) (Tm⁻ t)) & (S.εₑη (S.εₑ S.∘ₑ OPE⁻ σ) ⁻¹)
        ◾ S.Tm-∘ₑ (keep S.εₑ) (keep (OPE⁻ σ)) (Tm⁻ t))
Tmₑ⁻ σ (app t u) = app & Tmₑ⁻ σ t ⊗ Tmₑ⁻ σ u

Sub⁻ : ∀ {Γ Δ} → T.Sub Γ Δ → S.Sub (Con⁻ Γ) (Con⁻ Δ)
Sub⁻ ∙       = ∙
Sub⁻ (σ , t) = Sub⁻ σ , Tm⁻ t

ₛ∘ₑ⁻ : ∀ {Γ Δ Σ}(σ : T.Sub Δ Σ)(δ : T.OPE Γ Δ) → Sub⁻ (σ T.ₛ∘ₑ δ) ≡ Sub⁻ σ S.ₛ∘ₑ OPE⁻ δ
ₛ∘ₑ⁻ ∙       δ = refl
ₛ∘ₑ⁻ (σ , t) δ = _,_ & ₛ∘ₑ⁻ σ δ ⊗ Tmₑ⁻ δ t

dropₛ⁻ : ∀ {Γ Δ A} (σ : T.Sub Γ Δ) → Sub⁻ (T.dropₛ {A} σ) ≡ S.dropₛ (Sub⁻ σ)
dropₛ⁻ σ = ₛ∘ₑ⁻ σ T.wk ◾ (Sub⁻ σ S.ₛ∘ₑ_) & (drop & idₑ⁻)

keepₛ⁻ : ∀ {Γ Δ A} (σ : T.Sub Γ Δ) → Sub⁻ (T.keepₛ {A} σ) ≡ S.keepₛ (Sub⁻ σ)
keepₛ⁻ σ = (_, var vz) & dropₛ⁻ σ

idₛ⁻ : ∀ {Γ} → Sub⁻ (T.idₛ {Γ}) ≡ S.idₛ
idₛ⁻ {∙}     = refl
idₛ⁻ {Γ ▶ A} = keepₛ⁻ T.idₛ ◾ S.keepₛ & idₛ⁻

∈ₛ⁻ :
  ∀ {Γ Δ A}(σ : T.Sub Γ Δ)(x : A T.∈ Δ) → Tm⁻ (T.∈ₛ σ x) ≡ S.Tmₛ (Sub⁻ σ) (Tm⁻ (var x))
∈ₛ⁻ (σ , _) vz     = refl
∈ₛ⁻ (σ , _) (vs x) = ∈ₛ⁻ σ x

Tmₛ⁻ :
  ∀ {Γ Δ A}(σ : T.Sub Γ Δ)(t : T.Tm Δ A) → Tm⁻ (T.Tmₛ σ t) ≡ S.Tmₛ (Sub⁻ σ) (Tm⁻ t)
Tmₛ⁻ σ (var x) = ∈ₛ⁻ σ x
Tmₛ⁻ σ tt = refl
Tmₛ⁻ σ true = refl
Tmₛ⁻ σ false = refl
Tmₛ⁻ σ (if t u v) = if & Tmₛ⁻ σ t ⊗ Tmₛ⁻ σ u ⊗ Tmₛ⁻ σ v
Tmₛ⁻ σ (π₁ t) = π₁ & Tmₛ⁻ σ t
Tmₛ⁻ σ (π₂ t) = π₂ & Tmₛ⁻ σ t
Tmₛ⁻ σ (t , u) = _,_ & Tmₛ⁻ σ t ⊗ Tmₛ⁻ σ u
Tmₛ⁻ σ (pack t u) =
  lam & (app & (S.Tmₑ S.wk & Tmₛ⁻ σ u ◾ S.Tm-ₛ∘ₑ (Sub⁻ σ) S.wk (Tm⁻
  u) ⁻¹ ◾ (λ x → S.Tmₛ x (Tm⁻ u)) & (S.idlₑₛ (Sub⁻ σ S.ₛ∘ₑ drop
  S.idₑ) ⁻¹) ◾ S.Tm-ₑ∘ₛ S.wk (S.keepₛ (Sub⁻ σ))(Tm⁻ u)) ⊗ (_, var vz)
  & (S.Tmₑ S.wk & Tmₛ⁻ σ t ◾ S.Tm-ₛ∘ₑ (Sub⁻ σ) S.wk (Tm⁻ t) ⁻¹ ◾ (λ
  x → S.Tmₛ x (Tm⁻ t)) & (S.idlₑₛ (Sub⁻ σ S.ₛ∘ₑ drop S.idₑ) ⁻¹) ◾
  S.Tm-ₑ∘ₛ S.wk (S.keepₛ (Sub⁻ σ)) (Tm⁻ t) ))
Tmₛ⁻ σ (app⁺ t u) = app & Tmₛ⁻ σ t ⊗ Tmₛ⁻ σ u
Tmₛ⁻ σ (lam t) =
  lam & ((S.⌜Tmₑ⌝ (keep S.εₑ) (Tm⁻ t) ◾ (λ x → S.Tmₛ (x , var vz)
  (Tm⁻ t)) & ((S._ₛ∘ₑ S.wk) & (S.∙ₛη S.⌜ S.εₑ ⌝ᵒᵖᵉ ◾ S.∙ₛη _ ⁻¹) ◾
  S.assₑₛₑ S.εₑ (Sub⁻ σ) S.wk)) ◾ S.Tm-ₑ∘ₛ (keep S.εₑ) (S.keepₛ (Sub⁻
  σ))(Tm⁻ t))
Tmₛ⁻ σ (app t u) = app & Tmₛ⁻ σ t ⊗ Tmₛ⁻ σ u

~⁻ : ∀ {Γ A}{t t' : T.Tm Γ A} → t T.~ t' → Tm⁻ t S.~ Tm⁻ t'
~⁻ (β t t') = β _ _
           ~◾ S.≡~ (S.Tm-ₑ∘ₛ (keep S.εₑ) (S.idₛ , Tm⁻ t') (Tm⁻ t) ⁻¹)
           ~◾ S.≡~ ((λ x → S.Tmₛ (x , Tm⁻ t') (Tm⁻ t)) & S.∙ₛη (S.εₑ S.ₑ∘ₛ S.idₛ))
           ~◾ S.≡~ (Tmₛ⁻ (∙ , t') t ⁻¹)
~⁻ {t = t} {t'} (η p) =
  η (S.≡~ ((λ x → app x (var vz)) & ((λ x → S.Tmₑ (drop x) (Tm⁻ t)) &
  (idₑ⁻ ⁻¹) ◾ Tmₑ⁻ T.wk t ⁻¹)) ~◾ ~⁻ p ~◾ app (S.≡~ (Tmₑ⁻ T.wk t'
  ◾ (λ x → S.Tmₑ (drop x) (Tm⁻ t')) & idₑ⁻)) ~refl)
~⁻ (lam {t = t₁} {t'} t) = lam (S.Tmₑσ~ (keep S.εₑ) (~⁻ t))
~⁻ (app t u) = app (~⁻ t) (~⁻ u)
~⁻ true = true
~⁻ false = false
~⁻ (if t u v) = if (~⁻ t) (~⁻ u) (~⁻ v)
~⁻ (π₁ t) = π₁ (~⁻ t)
~⁻ (π₂ t) = π₂ (~⁻ t)
~⁻ (t , u) = ~⁻ t , ~⁻ u
~⁻ (π₁β t u) = π₁β (Tm⁻ t) (Tm⁻ u)
~⁻ (π₂β t u) = π₂β (Tm⁻ t) (Tm⁻ u)
~⁻ (,η t) = ,η (Tm⁻ t)
~⁻ ttη = ttη
~⁻ (pack t u) = lam (app (S.Tmₑσ~ S.wk (~⁻ u)) (S.Tmₑσ~ S.wk (~⁻ t) , ~refl))
~⁻ (app⁺ t u) = app (~⁻ t) (~⁻ u)
~⁻ (βᶜ e t t') =
  β _ _ ~◾ app (S.≡~ (S.Tm-ₑ∘ₛ S.wk (S.idₛ , Tm⁻ t') (Tm⁻ t ) ⁻¹) ~◾
  S.≡~ ((λ x → S.Tmₛ x (Tm⁻ t)) & S.idlₑₛ S.idₛ) ~◾ S.≡~ (S.Tm-idₛ
  (Tm⁻ t))) ((S.≡~ (S.Tm-ₑ∘ₛ S.wk (S.idₛ , Tm⁻ t') (Tm⁻ e) ⁻¹) ~◾
  S.≡~ ((λ x → S.Tmₛ x (Tm⁻ e)) & (S.idlₑₛ S.idₛ)) ~◾ S.≡~ (S.Tm-idₛ
  (Tm⁻ e))) , ~refl)
~⁻ {t = t} {t'} (ηᶜ p) =
  η (S.≡~ ((λ x → app x (var vz)) & ((λ x → S.Tmₑ (drop x) (Tm⁻ t)) &
  (idₑ⁻ ⁻¹) ◾ Tmₑ⁻ T.wk t ⁻¹)) ~◾ ~⁻ p ~◾ app (S.≡~ (Tmₑ⁻ T.wk t'
  ◾ (λ x → S.Tmₑ (drop x) (Tm⁻ t')) & idₑ⁻)) ~refl)
~⁻ ~refl = ~refl
~⁻ (t ~⁻¹) = ~⁻ t ~⁻¹
~⁻ (t ~◾ u) = ~⁻ t ~◾ ~⁻ u

-- Backward relation
--------------------------------------------------------------------------------

infixr 4 _≥_
_≥_ : ∀ {A} → T.Tm ∙ A → S.Tm ∙ (Ty⁻ A) → Set
_≥_ {𝔹} t t' = (t T.~ true × t' S.~ true) ⊎ (t T.~ false × t' S.~ false)
_≥_ {Top} t t' = ⊤
_≥_ {A * B} t t' = (π₁ t ≥ π₁ t') × (π₂ t ≥ π₂ t')
_≥_ {A ⇒⁺ B} t t' = ∀ {a a'} → a ≥ a' → app⁺ t a ≥ app t' a'
_≥_ {A ⇒ B} t t'  = ∀ {a a'} → a ≥ a' → app t a ≥ app t' a'

infixr 4 _◾≥_
_◾≥_ : ∀ {A}{t t' : T.Tm ∙ A}{t'' : S.Tm ∙ (Ty⁻ A)} → t T.≈ t' → t' ≥ t'' → t ≥ t''
_◾≥_ {𝔹} (inl (p , q)) (inl (r , s)) = inl (p , s)
_◾≥_ {𝔹} (inl (p , q)) (inr (r , s)) = inr ((p ~◾ q ~⁻¹ ~◾ r) , s)
_◾≥_ {𝔹} (inr (p , q)) (inl (r , s)) = inl ((p ~◾ q ~⁻¹ ~◾ r) , s)
_◾≥_ {𝔹} (inr (p , q)) (inr (r , s)) = inr (p , s)
_◾≥_ {Top} p q = tt
_◾≥_ {A * B} (p , q) (r , s) = (p ◾≥ r) , (q ◾≥ s)
_◾≥_ {A ⇒⁺ B} p q r = p T.≈refl ◾≥ q r
_◾≥_ {A ⇒ B} p q r = p T.≈refl ◾≥ q r

infixr 4 _~◾≥_
_~◾≥_ : ∀ {A}{t t' : T.Tm ∙ A}{t'' : S.Tm ∙ (Ty⁻ A)} → t T.~ t' → t' ≥ t'' → t ≥ t''
p ~◾≥ q = T.~≈ p ◾≥ q

infixl 5 _≥◾_
_≥◾_ : ∀ {A}{t : T.Tm ∙ A}{t' t'' : S.Tm ∙ (Ty⁻ A)} → t ≥ t' → t' S.≈ t'' → t ≥ t''
_≥◾_ {𝔹} (inl (p , q)) (inl (r , s)) = inl (p , s)
_≥◾_ {𝔹} (inl (p , q)) (inr (r , s)) = inl (p , (s ~◾ r ~⁻¹ ~◾ q))
_≥◾_ {𝔹} (inr (p , q)) (inl (r , s)) = inr (p , (s ~◾ r ~⁻¹ ~◾ q))
_≥◾_ {𝔹} (inr (p , q)) (inr (r , s)) = inr (p , s)
_≥◾_ {Top} p q = tt
_≥◾_ {A * B} (p , q) (r , s) = (p ≥◾ r) , (q ≥◾ s)
_≥◾_ {A ⇒⁺ B} p q r = p r ≥◾ q S.≈refl
_≥◾_ {A ⇒ B} p q r = p r ≥◾ q S.≈refl

infixl 5 _≥◾~_
_≥◾~_ : ∀ {A}{t : T.Tm ∙ A}{t' t'' : S.Tm ∙ (Ty⁻ A)} → t ≥ t' → t' S.~ t'' → t ≥ t''
_≥◾~_ p q = p ≥◾ S.~≈ q

infixr 4 _≥ₛ_
_≥ₛ_ : ∀ {Γ} → T.Sub ∙ Γ → S.Sub ∙ (Con⁻ Γ) → Set
∙       ≥ₛ ∙        = ⊤
(σ , t) ≥ₛ (δ , t') = (σ ≥ₛ δ) × t ≥ t'

∈≥⁻ : ∀ {Γ A}(x : A T.∈ Γ) σ σ' → σ ≥ₛ σ' → T.∈ₛ σ x ≥ S.∈ₛ σ' (∈⁻ x)
∈≥⁻ vz (σ , x) (σ' , x₁) σ≥ = ₂ σ≥
∈≥⁻ (vs x) (σ , x₁) (σ' , x₂) σ≥ = ∈≥⁻ x σ σ' (₁ σ≥)

Tm≥⁻ : ∀ {Γ A}(t : T.Tm Γ A) σ σ' → σ ≥ₛ σ' → T.Tmₛ σ t ≥ S.Tmₛ σ' (Tm⁻ t)
Tm≥⁻ (var x) σ σ' σ≥ = ∈≥⁻ x σ σ' σ≥
Tm≥⁻ tt σ σ' σ≥ = tt
Tm≥⁻ true σ σ' σ≥ = inl (~refl , ~refl)
Tm≥⁻ false σ σ' σ≥ = inr (~refl , ~refl)
Tm≥⁻ (if t u v) σ σ' σ≥ with Tm≥⁻ t σ σ' σ≥
... | inl (p , q) =
      if p ~refl ~refl
  ~◾≥ true
  ~◾≥ Tm≥⁻ u σ σ' σ≥
  ≥◾~ true ~⁻¹
  ≥◾~ if (q ~⁻¹) ~refl ~refl
... | inr (p , q) =
      if p ~refl ~refl
  ~◾≥ false
  ~◾≥ Tm≥⁻ v σ σ' σ≥
  ≥◾~ false ~⁻¹
  ≥◾~ if (q ~⁻¹) ~refl ~refl
Tm≥⁻ (π₁ t) σ σ' σ≥ = ₁ (Tm≥⁻ t σ σ' σ≥)
Tm≥⁻ (π₂ t) σ σ' σ≥ = ₂ (Tm≥⁻ t σ σ' σ≥)
Tm≥⁻ (t , u) σ σ' σ≥ =
  (π₁β _ _  ~◾≥ Tm≥⁻ t σ σ' σ≥ ≥◾~ π₁β _ _ ~⁻¹) ,
  (π₂β _ _  ~◾≥ Tm≥⁻ u σ σ' σ≥ ≥◾~ π₂β _ _ ~⁻¹)
Tm≥⁻ (pack t u) σ σ' σ≥ {a}{a'} p =
      βᶜ _ _ _
  ~◾≥ Tm≥⁻ u σ σ' σ≥ ((π₁β _ _  ~◾≥ Tm≥⁻ t σ σ' σ≥ ≥◾~ π₁β _ _ ~⁻¹) ,
                      (π₂β _ _  ~◾≥ p              ≥◾~ π₂β _ _ ~⁻¹))
  ≥◾~ S.≡~ (app & ((((λ x → S.Tmₛ x (Tm⁻ u)) &
       ((S.idrₛ σ' ⁻¹ ◾ S.assₛₑₛ σ' S.wk (∙ , a') ⁻¹) ◾ (S._∘ₛ (∙ ,
       a')) & S.idlₑₛ (S.dropₛ σ') ⁻¹) ◾ S.Tm-∘ₛ (S.wk S.ₑ∘ₛ S.keepₛ
       σ') (∙ , a') (Tm⁻ u)) ◾ S.Tmₛ (∙ , a') & S.Tm-ₑ∘ₛ S.wk
       (S.keepₛ σ') (Tm⁻ u))) ⊗
     (_, a') &
     (((λ x → S.Tmₛ x (Tm⁻ t)) &
       ((S.idrₛ σ' ⁻¹ ◾ S.assₛₑₛ σ' S.wk (∙ , a') ⁻¹) ◾ (S._∘ₛ (∙ ,
       a')) & S.idlₑₛ (S.dropₛ σ') ⁻¹) ◾ S.Tm-∘ₛ (S.wk S.ₑ∘ₛ S.keepₛ
       σ') (∙ , a') (Tm⁻ t)) ◾ S.Tmₛ (∙ , a') & S.Tm-ₑ∘ₛ S.wk
       (S.keepₛ σ') (Tm⁻ t)))
  ≥◾~ β _ _ ~⁻¹
Tm≥⁻ (app⁺ t u) σ σ' σ≥ = Tm≥⁻ t σ σ' σ≥ (Tm≥⁻ u σ σ' σ≥)
Tm≥⁻ (lam t) σ σ' σ≥ {a}{a'} p =
      β _ _
  ~◾≥ Tm≥⁻ t (∙ , a) (∙ , a') (tt , p)
  ≥◾~ S.≡~ ((λ x → S.Tmₛ (x , a') (Tm⁻ t)) & (S.∙ₛη _ ⁻¹))
  ≥◾~ S.≡~ (S.Tm-∘ₛ (keep S.εₑ S.ₑ∘ₛ S.keepₛ σ') (∙ , a') (Tm⁻ t))
  ≥◾~ S.≡~ (S.Tmₛ (∙ , a') & S.Tm-ₑ∘ₛ (keep S.εₑ) (S.keepₛ σ') (Tm⁻ t))
  ≥◾~ β _ _ ~⁻¹
Tm≥⁻ (app t u) σ σ' σ≥ = Tm≥⁻ t σ σ' σ≥ (Tm≥⁻ u σ σ' σ≥)

Tm≥⁻' : ∀ {A}(t : T.Tm ∙ A) → t ≥ Tm⁻ t
Tm≥⁻' {A} t = coe (_≥_ & T.Tm-idₛ t ⊗ S.Tm-idₛ (Tm⁻ t)) (Tm≥⁻ t T.idₛ S.idₛ tt)
