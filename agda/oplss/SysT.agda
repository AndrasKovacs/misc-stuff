
{-# OPTIONS --without-K #-}

module SysT where

open import Lib

-- Syntax
--------------------------------------------------------------------------------

infixr 4 _⇒_

data Ty : Set where
  Nat  : Ty
  _⇒_  : Ty → Ty → Ty

data Con : Set where
  ∙   : Con
  _,_ : Con → Ty → Con

data _∈_ (A : Ty) : Con → Set where
  vz : ∀ {Γ} → A ∈ (Γ , A)
  vs : ∀ {B Γ} → A ∈ Γ → A ∈ (Γ , B)

data Tm Γ : Ty → Set where
  var   : ∀ {A} → A ∈ Γ → Tm Γ A
  lam   : ∀ {A B} → Tm (Γ , A) B → Tm Γ (A ⇒ B)
  app   : ∀ {A B} → Tm Γ (A ⇒ B) → Tm Γ A → Tm Γ B  
  zero  : Tm Γ Nat
  suc   : Tm Γ Nat → Tm Γ Nat
  iter  : ∀ {A} → Tm Γ Nat → Tm Γ (Nat ⇒ A ⇒ A) → Tm Γ A → Tm Γ A

-- Order-preserving embedding
--------------------------------------------------------------------------------

infixr 9 _∘ₑ_
infixl 8 _[_]∈ₑ _[_]ₑ

data OPE : Con → Con → Set where
  ∙    : OPE ∙ ∙
  drop : ∀ {A Γ Δ} → OPE Γ Δ → OPE (Γ , A) Δ
  keep : ∀ {A Γ Δ} → OPE Γ Δ → OPE (Γ , A) (Δ , A)

-- OPE is a category

idₑ : ∀ {Γ} → OPE Γ Γ
idₑ {∙}     = ∙
idₑ {Γ , A} = keep (idₑ {Γ})

wk : ∀ {A Γ} → OPE (Γ , A) Γ
wk = drop idₑ

_∘ₑ_ : ∀ {Γ Δ Σ} → OPE Δ Σ → OPE Γ Δ → OPE Γ Σ
σ      ∘ₑ ∙      = σ
σ      ∘ₑ drop δ = drop (σ ∘ₑ δ)
drop σ ∘ₑ keep δ = drop (σ ∘ₑ δ)
keep σ ∘ₑ keep δ = keep (σ ∘ₑ δ)

idlₑ : ∀ {Γ Δ}(σ : OPE Γ Δ) → idₑ ∘ₑ σ ≡ σ
idlₑ ∙        = refl
idlₑ (drop σ) = drop & idlₑ σ
idlₑ (keep σ) = keep & idlₑ σ

idrₑ : ∀ {Γ Δ}(σ : OPE Γ Δ) → σ ∘ₑ idₑ ≡ σ
idrₑ ∙        = refl
idrₑ (drop σ) = drop & idrₑ σ
idrₑ (keep σ) = keep & idrₑ σ

assₑ :
  ∀ {Γ Δ Σ Ξ}(σ : OPE Σ Ξ)(δ : OPE Δ Σ)(ν : OPE Γ Δ)
  → (σ ∘ₑ δ) ∘ₑ ν ≡ σ ∘ₑ (δ ∘ₑ ν)
assₑ σ        δ        ∙        = refl
assₑ σ        δ        (drop ν) = drop & assₑ σ δ ν
assₑ σ        (drop δ) (keep ν) = drop & assₑ σ δ ν
assₑ (drop σ) (keep δ) (keep ν) = drop & assₑ σ δ ν
assₑ (keep σ) (keep δ) (keep ν) = keep & assₑ σ δ ν

-- (A ∈_) : is a presheaf on OPE

_[_]∈ₑ : ∀ {Γ Δ A} → A ∈ Δ → OPE Γ Δ → A ∈ Γ
v    [ ∙      ]∈ₑ = v
v    [ drop σ ]∈ₑ = vs (v [ σ ]∈ₑ)
vz   [ keep σ ]∈ₑ = vz
vs v [ keep σ ]∈ₑ = vs (v [ σ ]∈ₑ)

idₑ∈ : ∀ {Γ A}(v : A ∈ Γ) → v [ idₑ ]∈ₑ ≡ v
idₑ∈ vz     = refl
idₑ∈ (vs v) = vs & idₑ∈ v

∘ₑ∈ :
  ∀ {Γ Δ Σ A}(v : A ∈ Σ)(σ : OPE Δ Σ)(δ : OPE Γ Δ)
  →  v [ σ ]∈ₑ [ δ ]∈ₑ ≡ v [ σ ∘ₑ δ ]∈ₑ
∘ₑ∈ () ∙       ∙
∘ₑ∈ v       σ       (drop δ)  = vs & ∘ₑ∈ v σ δ
∘ₑ∈ v      (drop σ) (keep δ)  = vs & ∘ₑ∈ v σ δ
∘ₑ∈ vz     (keep σ) (keep δ)  = refl
∘ₑ∈ (vs v) (keep σ) (keep δ)  = vs & ∘ₑ∈ v σ δ

-- (Tm _ A) is a presheaf on OPE 

_[_]ₑ : ∀ {Γ Δ A} → Tm Δ A → OPE Γ Δ → Tm Γ A
var v      [ σ ]ₑ = var (v [ σ ]∈ₑ)
lam t      [ σ ]ₑ = lam (t [ keep σ ]ₑ)
app f a    [ σ ]ₑ = app (f [ σ ]ₑ) (a [ σ ]ₑ)

zero       [ σ ]ₑ = zero
suc n      [ σ ]ₑ = suc (n [ σ ]ₑ)
iter n s z [ σ ]ₑ = iter (n [ σ ]ₑ) (s [ σ ]ₑ) (z [ σ ]ₑ)    

idₑTm : ∀ {Γ A}(t : Tm Γ A) → t [ idₑ ]ₑ ≡ t
idₑTm (var v     ) = var & idₑ∈ v
idₑTm (lam t     ) = lam & idₑTm t
idₑTm (app f a   ) = app & idₑTm f ⊗ idₑTm a
idₑTm (zero      ) = refl
idₑTm (suc n     ) = suc & idₑTm n
idₑTm (iter n s z) = iter & idₑTm n ⊗ idₑTm s ⊗ idₑTm z

∘ₑTm :
  ∀ {Γ Δ Σ A}(t : Tm Σ A)(σ : OPE Δ Σ)(δ : OPE Γ Δ)
  → t [ σ ]ₑ [ δ ]ₑ ≡ t [ σ ∘ₑ δ ]ₑ
∘ₑTm (var v     ) σ δ = var & ∘ₑ∈ v σ δ
∘ₑTm (lam t     ) σ δ = lam & ∘ₑTm t (keep σ) (keep δ)
∘ₑTm (app f a   ) σ δ = app & ∘ₑTm f σ δ ⊗ ∘ₑTm a σ δ
∘ₑTm (zero      ) σ δ = refl
∘ₑTm (suc n     ) σ δ = suc & ∘ₑTm n σ δ
∘ₑTm (iter n s z) σ δ = iter & ∘ₑTm n σ δ ⊗ ∘ₑTm s σ δ ⊗ ∘ₑTm z σ δ

-- Substitution
-- (Satisfies the category-with-families equations except the β and η conversions)
--------------------------------------------------------------------------------

infixr  6 _ₑ∘ₛ_ _ₛ∘ₑ_
infixl 8 _[_] _[_]∈

data Tms (Γ : Con) : Con → Set where
  ∙   : Tms Γ ∙
  _,_ : ∀ {A Δ} → Tms Γ Δ → Tm Γ A → Tms Γ (Δ , A)

_ₛ∘ₑ_ : ∀ {Γ Δ Σ} → Tms Δ Σ → OPE Γ Δ → Tms Γ Σ
∙       ₛ∘ₑ δ = ∙
(σ , t) ₛ∘ₑ δ = σ ₛ∘ₑ δ , t [ δ ]ₑ

_ₑ∘ₛ_ : ∀ {Γ Δ Σ} → OPE Δ Σ → Tms Γ Δ → Tms Γ Σ
∙      ₑ∘ₛ δ       = δ
drop σ ₑ∘ₛ (δ , t) = σ ₑ∘ₛ δ
keep σ ₑ∘ₛ (δ , t) = σ ₑ∘ₛ δ , t

dropₛ : ∀ {A Γ Δ} → Tms Γ Δ → Tms (Γ , A) Δ
dropₛ σ = σ ₛ∘ₑ wk 

keepₛ : ∀ {A Γ Δ} → Tms Γ Δ → Tms (Γ , A) (Δ , A)
keepₛ σ = dropₛ σ , var vz

idₛ : ∀ {Γ} → Tms Γ Γ
idₛ {∙}     = ∙
idₛ {Γ , A} = keepₛ {A} idₛ

assₛₑₑ :
  ∀ {Γ Δ Σ Ξ}(σ : Tms Σ Ξ)(δ : OPE Δ Σ)(ν : OPE Γ Δ)
  → (σ ₛ∘ₑ δ) ₛ∘ₑ ν ≡ σ ₛ∘ₑ (δ ∘ₑ ν)
assₛₑₑ ∙       δ ν = refl
assₛₑₑ (σ , t) δ ν = _,_ & assₛₑₑ σ δ ν ⊗ ∘ₑTm t δ ν

assₑₑₛ :
  ∀ {Γ Δ Σ Ξ}(σ : OPE Σ Ξ)(δ : OPE Δ Σ)(ν : Tms Γ Δ)
  → (σ ∘ₑ δ) ₑ∘ₛ ν ≡ σ ₑ∘ₛ (δ ₑ∘ₛ ν)
assₑₑₛ σ        ∙        ν       = refl
assₑₑₛ σ        (drop δ) (ν , _) = assₑₑₛ σ δ ν
assₑₑₛ (drop σ) (keep δ) (ν , _) = assₑₑₛ σ δ ν
assₑₑₛ (keep σ) (keep δ) (ν , t) = (_, t) & assₑₑₛ σ δ ν

assₑₛₑ :
  ∀ {Γ Δ Σ Ξ}(σ : OPE Σ Ξ)(δ : Tms Δ Σ)(ν : OPE Γ Δ)
  → (σ ₑ∘ₛ δ) ₛ∘ₑ ν ≡ σ ₑ∘ₛ (δ ₛ∘ₑ ν)
assₑₛₑ ∙        δ       ν = refl
assₑₛₑ (drop σ) (δ , t) ν = assₑₛₑ σ δ ν
assₑₛₑ (keep σ) (δ , t) ν = (_, t [ ν ]ₑ) & assₑₛₑ σ δ ν

⌜_⌝ʳ : ∀ {Γ Δ} → OPE Γ Δ → Tms Γ Δ
⌜ ∙      ⌝ʳ = ∙
⌜ drop σ ⌝ʳ = dropₛ ⌜ σ ⌝ʳ
⌜ keep σ ⌝ʳ = keepₛ ⌜ σ ⌝ʳ

idlₑₛ : ∀ {Γ Δ}(σ : Tms Γ Δ) → idₑ ₑ∘ₛ σ ≡ σ
idlₑₛ ∙       = refl
idlₑₛ (σ , t) = (_, t) & idlₑₛ σ

idrₛₑ : ∀ {Γ Δ}(σ : Tms Γ Δ) → σ ₛ∘ₑ idₑ ≡ σ
idrₛₑ ∙       = refl
idrₛₑ (σ , t) = _,_ & idrₛₑ σ ⊗ idₑTm t

idlₛₑ : ∀ {Γ Δ}(σ : OPE Γ Δ) → idₛ ₛ∘ₑ σ ≡ ⌜ σ ⌝ʳ
idlₛₑ ∙        = refl
idlₛₑ (drop σ) =
      (λ σ → idₛ ₛ∘ₑ drop σ) & idrₑ σ ⁻¹
    ◾ assₛₑₑ idₛ σ wk ⁻¹
    ◾ dropₛ & idlₛₑ σ    
idlₛₑ (keep σ) =
  (_, var vz) &
      (assₛₑₑ idₛ wk (keep σ)
    ◾ (λ σ → idₛ ₛ∘ₑ drop σ) & (idlₑ σ ◾ idrₑ σ ⁻¹)
    ◾ assₛₑₑ idₛ σ wk ⁻¹
    ◾ (_ₛ∘ₑ wk) & idlₛₑ σ )

idrₑₛ : ∀ {Γ Δ}(σ : OPE Γ Δ) → σ ₑ∘ₛ idₛ ≡ ⌜ σ ⌝ʳ
idrₑₛ ∙        = refl
idrₑₛ (drop σ) = assₑₛₑ σ idₛ wk ⁻¹ ◾ dropₛ & idrₑₛ σ
idrₑₛ (keep σ) = (_, var vz) & (assₑₛₑ σ idₛ wk ⁻¹ ◾ (_ₛ∘ₑ wk) & idrₑₛ σ)

_[_]∈ : ∀ {Γ Δ A} → A ∈ Δ → Tms Γ Δ → Tm Γ A
vz   [ σ , t ]∈ = t
vs v [ σ , _ ]∈ = v [ σ ]∈

_[_] : ∀ {Γ Δ A} → Tm Δ A → Tms Γ Δ → Tm Γ A
var v      [ σ ] = v [ σ ]∈
lam t      [ σ ] = lam (t [ keepₛ σ ])
app f a    [ σ ] = app (f [ σ ]) (a [ σ ])
zero       [ σ ] = zero
suc n      [ σ ] = suc (n [ σ ])
iter n s z [ σ ] = iter (n [ σ ]) (s [ σ ]) (z [ σ ])    

_∘ₛ_ : ∀ {Γ Δ Σ} → Tms Δ Σ → Tms Γ Δ → Tms Γ Σ
∙       ∘ₛ δ = ∙
(σ , t) ∘ₛ δ = σ ∘ₛ δ , t [ δ ]

ₑ∘ₛ∈ :
  ∀ {Γ Δ Σ A}(v : A ∈ Σ)(σ : OPE Δ Σ)(δ : Tms Γ Δ)
  → v [ σ ]∈ₑ [ δ ]∈ ≡ v [ σ ₑ∘ₛ δ ]∈
ₑ∘ₛ∈ v      ∙        δ       = refl
ₑ∘ₛ∈ v      (drop σ) (δ , t) = ₑ∘ₛ∈ v σ δ
ₑ∘ₛ∈ vz     (keep σ) (δ , t) = refl
ₑ∘ₛ∈ (vs v) (keep σ) (δ , t) = ₑ∘ₛ∈ v σ δ

ₑ∘ₛTm :
  ∀ {Γ Δ Σ A}(t : Tm Σ A)(σ : OPE Δ Σ)(δ : Tms Γ Δ)
  → t [ σ ]ₑ [ δ ] ≡ t [ σ ₑ∘ₛ δ ]
ₑ∘ₛTm (var v     ) σ δ = ₑ∘ₛ∈ v σ δ
ₑ∘ₛTm (lam t     ) σ δ = lam &
      (ₑ∘ₛTm t (keep σ) (keepₛ δ)
    ◾ (λ σ → t [ σ , var vz ]) & (assₑₛₑ σ δ wk ⁻¹))
ₑ∘ₛTm (app f a   ) σ δ = app & ₑ∘ₛTm f σ δ ⊗ ₑ∘ₛTm a σ δ
ₑ∘ₛTm (zero      ) σ δ = refl
ₑ∘ₛTm (suc n     ) σ δ = suc & ₑ∘ₛTm n σ δ
ₑ∘ₛTm (iter n s z) σ δ = iter & ₑ∘ₛTm n σ δ ⊗ ₑ∘ₛTm s σ δ ⊗ ₑ∘ₛTm z σ δ 

ₛ∘ₑ∈ :
  ∀ {Γ Δ Σ A}(v : A ∈ Σ)(σ : Tms Δ Σ)(δ : OPE Γ Δ)
  → v [ σ ]∈ [ δ ]ₑ ≡ v [ σ ₛ∘ₑ δ ]∈
ₛ∘ₑ∈ vz     (σ , _) δ = refl
ₛ∘ₑ∈ (vs v) (σ , _) δ = ₛ∘ₑ∈ v σ δ  

ₛ∘ₑTm :
  ∀ {Γ Δ Σ A}(t : Tm Σ A)(σ : Tms Δ Σ)(δ : OPE Γ Δ)
  → t [ σ ] [ δ ]ₑ ≡ t [ σ ₛ∘ₑ δ ]
ₛ∘ₑTm (var v     ) σ δ = ₛ∘ₑ∈ v σ δ
ₛ∘ₑTm (lam t     ) σ δ = 
  lam & (
      ₛ∘ₑTm t (keepₛ σ) (keep δ)
    ◾ (λ σ → t [ σ , var vz ]) &
        (assₛₑₑ σ wk (keep δ)
      ◾ ((λ δ → σ ₛ∘ₑ (drop δ)) &
          idlₑ δ
        ◾ (λ δ → σ ₛ∘ₑ drop δ) & (idrₑ δ ⁻¹)
        ◾ assₛₑₑ σ δ wk ⁻¹)))
ₛ∘ₑTm (app f a   ) σ δ = app & ₛ∘ₑTm f σ δ ⊗ ₛ∘ₑTm a σ δ
ₛ∘ₑTm (zero      ) σ δ = refl
ₛ∘ₑTm (suc n     ) σ δ = suc & ₛ∘ₑTm n σ δ
ₛ∘ₑTm (iter n s z) σ δ = iter & ₛ∘ₑTm n σ δ ⊗ ₛ∘ₑTm s σ δ ⊗ ₛ∘ₑTm z σ δ

assₛₑₛ :
  ∀ {Γ Δ Σ Ξ}(σ : Tms Σ Ξ)(δ : OPE Δ Σ)(ν : Tms Γ Δ)
  → (σ ₛ∘ₑ δ) ∘ₛ ν ≡ σ ∘ₛ (δ ₑ∘ₛ ν)
assₛₑₛ ∙       δ ν = refl
assₛₑₛ (σ , t) δ ν = _,_ & assₛₑₛ σ δ ν ⊗ ₑ∘ₛTm t δ ν

assₛₛₑ :
  ∀ {Γ Δ Σ Ξ}(σ : Tms Σ Ξ)(δ : Tms Δ Σ)(ν : OPE Γ Δ)
  → (σ ∘ₛ δ) ₛ∘ₑ ν ≡ σ ∘ₛ (δ ₛ∘ₑ ν)
assₛₛₑ ∙       δ ν = refl
assₛₛₑ (σ , t) δ ν = _,_ & assₛₛₑ σ δ ν ⊗ ₛ∘ₑTm t δ ν

∘ₛ∈ :
  ∀ {Γ Δ Σ A}(v : A ∈ Σ)(σ : Tms Δ Σ)(δ : Tms Γ Δ)
  → v [ σ ]∈ [ δ ] ≡ v [ σ ∘ₛ δ ]∈
∘ₛ∈ vz     (σ , _) δ = refl
∘ₛ∈ (vs v) (σ , t) δ = ∘ₛ∈ v σ δ

∘ₛTm :
  ∀ {Γ Δ Σ A}(t : Tm Σ A)(σ : Tms Δ Σ)(δ : Tms Γ Δ)
  → t [ σ ] [ δ ] ≡ t [ σ ∘ₛ δ ]
∘ₛTm (var v     ) σ δ = ∘ₛ∈ v σ δ
∘ₛTm (lam t     ) σ δ =
  lam & (
      ∘ₛTm t (keepₛ σ) (keepₛ δ)
    ◾ (λ σ → t [ σ , var vz ]) &
        (assₛₑₛ σ wk (keepₛ δ)
      ◾ (σ ∘ₛ_) & idlₑₛ (δ ₛ∘ₑ wk) ◾ assₛₛₑ σ δ wk ⁻¹))
∘ₛTm (app f a   ) σ δ = app & ∘ₛTm f σ δ ⊗ ∘ₛTm a σ δ
∘ₛTm (zero      ) σ δ = refl
∘ₛTm (suc n     ) σ δ = suc & ∘ₛTm n σ δ
∘ₛTm (iter n s z) σ δ = iter & ∘ₛTm n σ δ ⊗ ∘ₛTm s σ δ ⊗ ∘ₛTm z σ δ

assₛ :
  ∀ {Γ Δ Σ Ξ}(σ : Tms Σ Ξ)(δ : Tms Δ Σ)(ν : Tms Γ Δ)
  → (σ ∘ₛ δ) ∘ₛ ν ≡ σ ∘ₛ (δ ∘ₛ ν)
assₛ ∙       δ ν = refl
assₛ (σ , t) δ ν = _,_ & assₛ σ δ ν ⊗ ∘ₛTm t δ ν

idlₛ : ∀ {Γ Δ}(σ : Tms Γ Δ) → idₛ ∘ₛ σ ≡ σ
idlₛ ∙       = refl
idlₛ (σ , t) = (_, t) & (assₛₑₛ idₛ wk (σ , t) ◾ (idₛ ∘ₛ_) & idlₑₛ σ ◾ idlₛ σ)

idₛ∈ : ∀ {Γ A}(v : A ∈ Γ) → v [ idₛ ]∈ ≡ var v
idₛ∈ vz     = refl
idₛ∈ (vs v) = ₛ∘ₑ∈ v idₛ wk ⁻¹ ◾ (_[ wk ]ₑ) & idₛ∈ v ◾ (λ v → var (vs v)) & idₑ∈ v

idₛTm : ∀ {Γ A}(t : Tm Γ A) → t [ idₛ ] ≡ t
idₛTm (var v     ) = idₛ∈ v
idₛTm (lam t     ) = lam & idₛTm t
idₛTm (app f a   ) = app & idₛTm f ⊗ idₛTm a
idₛTm (zero      ) = refl
idₛTm (suc n     ) = suc & idₛTm n
idₛTm (iter n s z) = iter & idₛTm n ⊗ idₛTm s ⊗ idₛTm z

idrₛ : ∀ {Γ Δ}(σ : Tms Γ Δ) → σ ∘ₛ idₛ ≡ σ
idrₛ ∙       = refl
idrₛ (σ , t) = _,_ & idrₛ σ ⊗ idₛTm t

