{-# OPTIONS --without-K #-}

open import Lib

-- Syntax
--------------------------------------------------------------------------------

infixr 4 _⇒_

data Ty : Set where
  ι   : Ty
  _⇒_ : Ty → Ty → Ty

data Con : Set where
  ∙   : Con
  _,_ : Con → Ty → Con

data _∈_ (A : Ty) : Con → Set where
  vz : ∀ {Γ} → A ∈ (Γ , A)
  vs : ∀ {B Γ} → A ∈ Γ → A ∈ (Γ , B)

data Tm Γ : Ty → Set where
  var : ∀ {A} → A ∈ Γ → Tm Γ A
  lam : ∀ {A B} → Tm (Γ , A) B → Tm Γ (A ⇒ B)
  app : ∀ {A B} → Tm Γ (A ⇒ B) → Tm Γ A → Tm Γ B

-- Renaming
--------------------------------------------------------------------------------

infixr 9 _∘ᵣ_
infixl 8 _[_]∈ᵣ _[_]ᵣ

data Ren : Con → Con → Set where
  ∙    : Ren ∙ ∙
  drop : ∀ {A Γ Δ} → Ren Γ Δ → Ren (Γ , A) Δ
  keep : ∀ {A Γ Δ} → Ren Γ Δ → Ren (Γ , A) (Δ , A)

-- Ren is a category

idᵣ : ∀ {Γ} → Ren Γ Γ
idᵣ {∙}     = ∙
idᵣ {Γ , A} = keep (idᵣ {Γ})

wk : ∀ {A Γ} → Ren (Γ , A) Γ
wk = drop idᵣ

_∘ᵣ_ : ∀ {Γ Δ Σ} → Ren Δ Σ → Ren Γ Δ → Ren Γ Σ
σ      ∘ᵣ ∙      = σ
σ      ∘ᵣ drop δ = drop (σ ∘ᵣ δ)
drop σ ∘ᵣ keep δ = drop (σ ∘ᵣ δ)
keep σ ∘ᵣ keep δ = keep (σ ∘ᵣ δ)

idlᵣ : ∀ {Γ Δ}(σ : Ren Γ Δ) → idᵣ ∘ᵣ σ ≡ σ
idlᵣ ∙        = refl
idlᵣ (drop σ) = drop & idlᵣ σ
idlᵣ (keep σ) = keep & idlᵣ σ

idrᵣ : ∀ {Γ Δ}(σ : Ren Γ Δ) → σ ∘ᵣ idᵣ ≡ σ
idrᵣ ∙        = refl
idrᵣ (drop σ) = drop & idrᵣ σ
idrᵣ (keep σ) = keep & idrᵣ σ

assᵣ :
  ∀ {Γ Δ Σ Ξ}(σ : Ren Σ Ξ)(δ : Ren Δ Σ)(ν : Ren Γ Δ)
  → (σ ∘ᵣ δ) ∘ᵣ ν ≡ σ ∘ᵣ (δ ∘ᵣ ν)
assᵣ σ        δ        ∙        = refl
assᵣ σ        δ        (drop ν) = drop & assᵣ σ δ ν
assᵣ σ        (drop δ) (keep ν) = drop & assᵣ σ δ ν
assᵣ (drop σ) (keep δ) (keep ν) = drop & assᵣ σ δ ν
assᵣ (keep σ) (keep δ) (keep ν) = keep & assᵣ σ δ ν

-- (A ∈_) : is a presheaf on Ren

_[_]∈ᵣ : ∀ {Γ Δ A} → A ∈ Δ → Ren Γ Δ → A ∈ Γ
v    [ ∙      ]∈ᵣ = v
v    [ drop σ ]∈ᵣ = vs (v [ σ ]∈ᵣ)
vz   [ keep σ ]∈ᵣ = vz
vs v [ keep σ ]∈ᵣ = vs (v [ σ ]∈ᵣ)

idᵣ∈ : ∀ {Γ A}(v : A ∈ Γ) → v [ idᵣ ]∈ᵣ ≡ v
idᵣ∈ vz     = refl
idᵣ∈ (vs v) = vs & idᵣ∈ v

∘ᵣ∈ :
  ∀ {Γ Δ Σ A}(v : A ∈ Σ)(σ : Ren Δ Σ)(δ : Ren Γ Δ)
  →  v [ σ ]∈ᵣ [ δ ]∈ᵣ ≡ v [ σ ∘ᵣ δ ]∈ᵣ
∘ᵣ∈ () ∙       ∙
∘ᵣ∈ v       σ       (drop δ)  = vs & ∘ᵣ∈ v σ δ
∘ᵣ∈ v      (drop σ) (keep δ)  = vs & ∘ᵣ∈ v σ δ
∘ᵣ∈ vz     (keep σ) (keep δ)  = refl
∘ᵣ∈ (vs v) (keep σ) (keep δ)  = vs & ∘ᵣ∈ v σ δ

-- (Tm _ A) is a presheaf on Ren 

_[_]ᵣ : ∀ {Γ Δ A} → Tm Δ A → Ren Γ Δ → Tm Γ A
var v   [ σ ]ᵣ = var (v [ σ ]∈ᵣ)
lam t   [ σ ]ᵣ = lam (t [ keep σ ]ᵣ)
app f a [ σ ]ᵣ = app (f [ σ ]ᵣ) (a [ σ ]ᵣ)

idᵣTm : ∀ {Γ A}(t : Tm Γ A) → t [ idᵣ ]ᵣ ≡ t
idᵣTm (var v)   = var & idᵣ∈ v
idᵣTm (lam t)   = lam & idᵣTm t
idᵣTm (app f a) = app & idᵣTm f ⊗ idᵣTm a

∘ᵣTm :
  ∀ {Γ Δ Σ A}(t : Tm Σ A)(σ : Ren Δ Σ)(δ : Ren Γ Δ)
  → t [ σ ]ᵣ [ δ ]ᵣ ≡ t [ σ ∘ᵣ δ ]ᵣ
∘ᵣTm (var v)   σ δ = var & ∘ᵣ∈ v σ δ
∘ᵣTm (lam t)   σ δ = lam & ∘ᵣTm t (keep σ) (keep δ)
∘ᵣTm (app f a) σ δ = app & ∘ᵣTm f σ δ ⊗ ∘ᵣTm a σ δ  

-- Substitution
-- (Satisfies the category-with-families equations except the β and η conversions)
--------------------------------------------------------------------------------

infixr  6 _ᵣ∘ₛ_ _ₛ∘ᵣ_
infixl 8 _[_] _[_]∈

data Tms (Γ : Con) : Con → Set where
  ∙   : Tms Γ ∙
  _,_ : ∀ {A Δ} → Tms Γ Δ → Tm Γ A → Tms Γ (Δ , A)

_ₛ∘ᵣ_ : ∀ {Γ Δ Σ} → Tms Δ Σ → Ren Γ Δ → Tms Γ Σ
∙       ₛ∘ᵣ δ = ∙
(σ , t) ₛ∘ᵣ δ = σ ₛ∘ᵣ δ , t [ δ ]ᵣ

_ᵣ∘ₛ_ : ∀ {Γ Δ Σ} → Ren Δ Σ → Tms Γ Δ → Tms Γ Σ
∙      ᵣ∘ₛ δ       = δ
drop σ ᵣ∘ₛ (δ , t) = σ ᵣ∘ₛ δ
keep σ ᵣ∘ₛ (δ , t) = σ ᵣ∘ₛ δ , t

dropₛ : ∀ {A Γ Δ} → Tms Γ Δ → Tms (Γ , A) Δ
dropₛ σ = σ ₛ∘ᵣ wk 

keepₛ : ∀ {A Γ Δ} → Tms Γ Δ → Tms (Γ , A) (Δ , A)
keepₛ σ = dropₛ σ , var vz

idₛ : ∀ {Γ} → Tms Γ Γ
idₛ {∙}     = ∙
idₛ {Γ , A} = keepₛ {A} idₛ

assₛᵣᵣ :
  ∀ {Γ Δ Σ Ξ}(σ : Tms Σ Ξ)(δ : Ren Δ Σ)(ν : Ren Γ Δ)
  → (σ ₛ∘ᵣ δ) ₛ∘ᵣ ν ≡ σ ₛ∘ᵣ (δ ∘ᵣ ν)
assₛᵣᵣ ∙       δ ν = refl
assₛᵣᵣ (σ , t) δ ν = _,_ & assₛᵣᵣ σ δ ν ⊗ ∘ᵣTm t δ ν

assᵣᵣₛ :
  ∀ {Γ Δ Σ Ξ}(σ : Ren Σ Ξ)(δ : Ren Δ Σ)(ν : Tms Γ Δ)
  → (σ ∘ᵣ δ) ᵣ∘ₛ ν ≡ σ ᵣ∘ₛ (δ ᵣ∘ₛ ν)
assᵣᵣₛ σ        ∙        ν       = refl
assᵣᵣₛ σ        (drop δ) (ν , _) = assᵣᵣₛ σ δ ν
assᵣᵣₛ (drop σ) (keep δ) (ν , _) = assᵣᵣₛ σ δ ν
assᵣᵣₛ (keep σ) (keep δ) (ν , t) = (_, t) & assᵣᵣₛ σ δ ν

assᵣₛᵣ :
  ∀ {Γ Δ Σ Ξ}(σ : Ren Σ Ξ)(δ : Tms Δ Σ)(ν : Ren Γ Δ)
  → (σ ᵣ∘ₛ δ) ₛ∘ᵣ ν ≡ σ ᵣ∘ₛ (δ ₛ∘ᵣ ν)
assᵣₛᵣ ∙        δ       ν = refl
assᵣₛᵣ (drop σ) (δ , t) ν = assᵣₛᵣ σ δ ν
assᵣₛᵣ (keep σ) (δ , t) ν = (_, t [ ν ]ᵣ) & assᵣₛᵣ σ δ ν

⌜_⌝ʳ : ∀ {Γ Δ} → Ren Γ Δ → Tms Γ Δ
⌜ ∙      ⌝ʳ = ∙
⌜ drop σ ⌝ʳ = dropₛ ⌜ σ ⌝ʳ
⌜ keep σ ⌝ʳ = keepₛ ⌜ σ ⌝ʳ

idlᵣₛ : ∀ {Γ Δ}(σ : Tms Γ Δ) → idᵣ ᵣ∘ₛ σ ≡ σ
idlᵣₛ ∙       = refl
idlᵣₛ (σ , t) = (_, t) & idlᵣₛ σ

idrₛᵣ : ∀ {Γ Δ}(σ : Tms Γ Δ) → σ ₛ∘ᵣ idᵣ ≡ σ
idrₛᵣ ∙       = refl
idrₛᵣ (σ , t) = _,_ & idrₛᵣ σ ⊗ idᵣTm t

idlₛᵣ : ∀ {Γ Δ}(σ : Ren Γ Δ) → idₛ ₛ∘ᵣ σ ≡ ⌜ σ ⌝ʳ
idlₛᵣ ∙        = refl
idlₛᵣ (drop σ) =
      (λ σ → idₛ ₛ∘ᵣ drop σ) & idrᵣ σ ⁻¹
    ◾ assₛᵣᵣ idₛ σ wk ⁻¹
    ◾ dropₛ & idlₛᵣ σ    
idlₛᵣ (keep σ) =
  (_, var vz) &
      (assₛᵣᵣ idₛ wk (keep σ)
    ◾ (λ σ → idₛ ₛ∘ᵣ drop σ) & (idlᵣ σ ◾ idrᵣ σ ⁻¹)
    ◾ assₛᵣᵣ idₛ σ wk ⁻¹
    ◾ (_ₛ∘ᵣ wk) & idlₛᵣ σ )

idrᵣₛ : ∀ {Γ Δ}(σ : Ren Γ Δ) → σ ᵣ∘ₛ idₛ ≡ ⌜ σ ⌝ʳ
idrᵣₛ ∙        = refl
idrᵣₛ (drop σ) = assᵣₛᵣ σ idₛ wk ⁻¹ ◾ dropₛ & idrᵣₛ σ
idrᵣₛ (keep σ) = (_, var vz) & (assᵣₛᵣ σ idₛ wk ⁻¹ ◾ (_ₛ∘ᵣ wk) & idrᵣₛ σ)

_[_]∈ : ∀ {Γ Δ A} → A ∈ Δ → Tms Γ Δ → Tm Γ A
vz   [ σ , t ]∈ = t
vs v [ σ , _ ]∈ = v [ σ ]∈

_[_] : ∀ {Γ Δ A} → Tm Δ A → Tms Γ Δ → Tm Γ A
var v   [ σ ] = v [ σ ]∈
lam t   [ σ ] = lam (t [ keepₛ σ ])
app f a [ σ ] = app (f [ σ ]) (a [ σ ])

_∘ₛ_ : ∀ {Γ Δ Σ} → Tms Δ Σ → Tms Γ Δ → Tms Γ Σ
∙       ∘ₛ δ = ∙
(σ , t) ∘ₛ δ = σ ∘ₛ δ , t [ δ ]

ᵣ∘ₛ∈ :
  ∀ {Γ Δ Σ A}(v : A ∈ Σ)(σ : Ren Δ Σ)(δ : Tms Γ Δ)
  → v [ σ ]∈ᵣ [ δ ]∈ ≡ v [ σ ᵣ∘ₛ δ ]∈
ᵣ∘ₛ∈ v      ∙        δ       = refl
ᵣ∘ₛ∈ v      (drop σ) (δ , t) = ᵣ∘ₛ∈ v σ δ
ᵣ∘ₛ∈ vz     (keep σ) (δ , t) = refl
ᵣ∘ₛ∈ (vs v) (keep σ) (δ , t) = ᵣ∘ₛ∈ v σ δ

ᵣ∘ₛTm :
  ∀ {Γ Δ Σ A}(t : Tm Σ A)(σ : Ren Δ Σ)(δ : Tms Γ Δ)
  → t [ σ ]ᵣ [ δ ] ≡ t [ σ ᵣ∘ₛ δ ]
ᵣ∘ₛTm (var v)   σ δ = ᵣ∘ₛ∈ v σ δ
ᵣ∘ₛTm (lam t)   σ δ =
  lam &
      (ᵣ∘ₛTm t (keep σ) (keepₛ δ)
    ◾ (λ σ → t [ σ , var vz ]) & (assᵣₛᵣ σ δ wk ⁻¹))
ᵣ∘ₛTm (app f a) σ δ = app & ᵣ∘ₛTm f σ δ ⊗ ᵣ∘ₛTm a σ δ

ₛ∘ᵣ∈ :
  ∀ {Γ Δ Σ A}(v : A ∈ Σ)(σ : Tms Δ Σ)(δ : Ren Γ Δ)
  → v [ σ ]∈ [ δ ]ᵣ ≡ v [ σ ₛ∘ᵣ δ ]∈
ₛ∘ᵣ∈ vz     (σ , _) δ = refl
ₛ∘ᵣ∈ (vs v) (σ , _) δ = ₛ∘ᵣ∈ v σ δ  

ₛ∘ᵣTm :
  ∀ {Γ Δ Σ A}(t : Tm Σ A)(σ : Tms Δ Σ)(δ : Ren Γ Δ)
  → t [ σ ] [ δ ]ᵣ ≡ t [ σ ₛ∘ᵣ δ ]
ₛ∘ᵣTm (var v)   σ δ = ₛ∘ᵣ∈ v σ δ
ₛ∘ᵣTm (lam t)   σ δ =
  lam & (
      ₛ∘ᵣTm t (keepₛ σ) (keep δ)
    ◾ (λ σ → t [ σ , var vz ]) &
        (assₛᵣᵣ σ wk (keep δ)
      ◾ ((λ δ → σ ₛ∘ᵣ (drop δ)) &
          idlᵣ δ
        ◾ (λ δ → σ ₛ∘ᵣ drop δ) & (idrᵣ δ ⁻¹)
        ◾ assₛᵣᵣ σ δ wk ⁻¹)))
ₛ∘ᵣTm (app f a) σ δ = app & ₛ∘ᵣTm f σ δ ⊗ ₛ∘ᵣTm a σ δ

assₛᵣₛ :
  ∀ {Γ Δ Σ Ξ}(σ : Tms Σ Ξ)(δ : Ren Δ Σ)(ν : Tms Γ Δ)
  → (σ ₛ∘ᵣ δ) ∘ₛ ν ≡ σ ∘ₛ (δ ᵣ∘ₛ ν)
assₛᵣₛ ∙       δ ν = refl
assₛᵣₛ (σ , t) δ ν = _,_ & assₛᵣₛ σ δ ν ⊗ ᵣ∘ₛTm t δ ν

assₛₛᵣ :
  ∀ {Γ Δ Σ Ξ}(σ : Tms Σ Ξ)(δ : Tms Δ Σ)(ν : Ren Γ Δ)
  → (σ ∘ₛ δ) ₛ∘ᵣ ν ≡ σ ∘ₛ (δ ₛ∘ᵣ ν)
assₛₛᵣ ∙       δ ν = refl
assₛₛᵣ (σ , t) δ ν = _,_ & assₛₛᵣ σ δ ν ⊗ ₛ∘ᵣTm t δ ν

∘ₛ∈ :
  ∀ {Γ Δ Σ A}(v : A ∈ Σ)(σ : Tms Δ Σ)(δ : Tms Γ Δ)
  → v [ σ ]∈ [ δ ] ≡ v [ σ ∘ₛ δ ]∈
∘ₛ∈ vz     (σ , _) δ = refl
∘ₛ∈ (vs v) (σ , t) δ = ∘ₛ∈ v σ δ

∘ₛTm :
  ∀ {Γ Δ Σ A}(t : Tm Σ A)(σ : Tms Δ Σ)(δ : Tms Γ Δ)
  → t [ σ ] [ δ ] ≡ t [ σ ∘ₛ δ ]
∘ₛTm (var v)   σ δ = ∘ₛ∈ v σ δ
∘ₛTm (lam t)   σ δ =
  lam & (
      ∘ₛTm t (keepₛ σ) (keepₛ δ)
    ◾ (λ σ → t [ σ , var vz ]) &
        (assₛᵣₛ σ wk (keepₛ δ)
      ◾ (σ ∘ₛ_) & idlᵣₛ (δ ₛ∘ᵣ wk) ◾ assₛₛᵣ σ δ wk ⁻¹))
∘ₛTm (app f a) σ δ = app & ∘ₛTm f σ δ ⊗ ∘ₛTm a σ δ

assₛ :
  ∀ {Γ Δ Σ Ξ}(σ : Tms Σ Ξ)(δ : Tms Δ Σ)(ν : Tms Γ Δ)
  → (σ ∘ₛ δ) ∘ₛ ν ≡ σ ∘ₛ (δ ∘ₛ ν)
assₛ ∙       δ ν = refl
assₛ (σ , t) δ ν = _,_ & assₛ σ δ ν ⊗ ∘ₛTm t δ ν

idlₛ : ∀ {Γ Δ}(σ : Tms Γ Δ) → idₛ ∘ₛ σ ≡ σ
idlₛ ∙       = refl
idlₛ (σ , t) = (_, t) & (assₛᵣₛ idₛ wk (σ , t) ◾ (idₛ ∘ₛ_) & idlᵣₛ σ ◾ idlₛ σ)

idₛ∈ : ∀ {Γ A}(v : A ∈ Γ) → v [ idₛ ]∈ ≡ var v
idₛ∈ vz     = refl
idₛ∈ (vs v) = ₛ∘ᵣ∈ v idₛ wk ⁻¹ ◾ (_[ wk ]ᵣ) & idₛ∈ v ◾ (λ v → var (vs v)) & idᵣ∈ v

idₛTm : ∀ {Γ A}(t : Tm Γ A) → t [ idₛ ] ≡ t
idₛTm (var v)   = idₛ∈ v
idₛTm (lam t)   = lam & idₛTm t
idₛTm (app f x) = app & idₛTm f ⊗ idₛTm x

idrₛ : ∀ {Γ Δ}(σ : Tms Γ Δ) → σ ∘ₛ idₛ ≡ σ
idrₛ ∙       = refl
idrₛ (σ , t) = _,_ & idrₛ σ ⊗ idₛTm t

-- Reduction
--------------------------------------------------------------------------------

data _~>_ {Γ} : ∀ {A} → Tm Γ A → Tm Γ A → Set where
  β    : ∀ {A B}(t : Tm (Γ , A) B) t'     →  app (lam t) t' ~> t [ idₛ , t' ]
  lam  : ∀ {A B}{t t' : Tm (Γ , A) B}     → t ~> t' →  lam t   ~> lam t'
  app₁ : ∀ {A B}{f}{f' : Tm Γ (A ⇒ B)}{a} → f ~> f' →  app f a ~> app f' a
  app₂ : ∀ {A B}{f : Tm Γ (A ⇒ B)} {a a'} → a ~> a' →  app f a ~> app f  a'
infix 3 _~>_

~>ₛ : ∀ {Γ Δ A}{t t' : Tm Γ A}(σ : Tms Δ Γ) → t ~> t' → t [ σ ] ~> t' [ σ ]
~>ₛ σ (β t t') =
  coe ((app (lam (t [ keepₛ σ ])) (t' [ σ ]) ~>_)
      & (∘ₛTm t (keepₛ σ) (idₛ , (t' [ σ ]))
      ◾ (t [_]) & ((_, (t' [ σ ])) &
          (assₛᵣₛ σ wk (idₛ , (t' [ σ ]))
        ◾ (σ ∘ₛ_) & (idlᵣₛ idₛ) ◾ idrₛ σ ◾ idlₛ σ ⁻¹))
      ◾ ∘ₛTm t (idₛ , t') σ ⁻¹))
  (β (t [ keepₛ σ ]) (t' [ σ ]))  
~>ₛ σ (lam  step) = lam  (~>ₛ (keepₛ σ) step)
~>ₛ σ (app₁ step) = app₁ (~>ₛ σ step)
~>ₛ σ (app₂ step) = app₂ (~>ₛ σ step)

~>ᵣ : ∀ {Γ Δ A}{t t' : Tm Γ A}(σ : Ren Δ Γ) → t ~> t' → t [ σ ]ᵣ ~> t' [ σ ]ᵣ
~>ᵣ σ (β t t')    =
  coe ((app (lam (t [ keep σ ]ᵣ)) (t' [ σ ]ᵣ) ~>_) &
      (ᵣ∘ₛTm t (keep σ) (idₛ , (t' [ σ ]ᵣ))
    ◾ (t [_]) & ((_, (t' [ σ ]ᵣ)) & (idrᵣₛ σ ◾ idlₛᵣ σ ⁻¹))
    ◾ ₛ∘ᵣTm t (idₛ , t') σ ⁻¹))
  (β (t [ keep σ ]ᵣ) (t' [ σ ]ᵣ))
~>ᵣ σ (lam step)  = lam (~>ᵣ (keep σ) step)
~>ᵣ σ (app₁ step) = app₁ (~>ᵣ σ step)
~>ᵣ σ (app₂ step) = app₂ (~>ᵣ σ step)

~>un-r :
  ∀ {Γ Δ A}{t : Tm Γ A}{σ : Ren Δ Γ}{t'}
  → t [ σ ]ᵣ ~> t' → Σ _ λ t'' → (t ~> t'') × (t'' [ σ ]ᵣ ≡ t')
~>un-r {t = var x} ()
~>un-r {t = lam t} (lam step) with ~>un-r step
... | t'' , (p , refl) = lam t'' , (lam p , refl)
~>un-r {t = app (var v) a} (app₁ ())
~>un-r {t = app (var v) a} (app₂ step) with ~>un-r step
... | t'' , (p , refl) = app (var v) t'' , (app₂ p , refl)
~>un-r {t = app (lam f) a} {σ} (β _ _) =
  f [ idₛ , a ] , (β _ _ ,
    (ₛ∘ᵣTm f (idₛ , a) σ
  ◾ (f [_]) & ((_, (a [ σ ]ᵣ)) & (idlₛᵣ σ ◾ idrᵣₛ σ ⁻¹))
  ◾ ᵣ∘ₛTm f (keep σ) (idₛ , (a [ σ ]ᵣ)) ⁻¹))
~>un-r {t = app (lam f) a}     (app₁ (lam step)) with ~>un-r step
... | t'' , (p , refl) = (app (lam t'') a) , (app₁ (lam p) , refl)
~>un-r {t = app (lam f) a}     (app₂ step) with ~>un-r step
... | t'' , (p , refl) = (app (lam f) t'') , (app₂ p , refl)
~>un-r {t = app (app f a) a'}  (app₁ step) with ~>un-r step
... | t'' , (p , refl) = (app t'' a') , (app₁ p , refl)
~>un-r {t = app (app f a) a''} (app₂ step) with ~>un-r step
... | t'' , (p , refl) = app (app f a) t'' , (app₂ p , refl)

-- Strong normalization definition + lemmas
--------------------------------------------------------------------------------

data SN {Γ A} (t : Tm Γ A) : Set where
  sn : (∀ {t'} → t ~> t' → SN t') → SN t

SNᵣ→ : ∀ {Γ Δ A}{t : Tm Γ A}(σ : Ren Δ Γ) → SN t → SN (t [ σ ]ᵣ)
SNᵣ→ σ (sn s) = sn λ {t'} step →
  let (t'' , (p , q)) = ~>un-r step in coe (SN & q) (SNᵣ→ σ (s p))

SNᵣ← : ∀ {Γ Δ A}{t : Tm Γ A}(σ : Ren Δ Γ) → SN (t [ σ ]ᵣ) → SN t
SNᵣ← σ (sn s) = sn λ step → SNᵣ← σ (s (~>ᵣ σ step))

SN-app₁ : ∀ {Γ A B}{f : Tm Γ (A ⇒ B)}{a} → SN (app f a) → SN f
SN-app₁ (sn s) = sn λ f~>f' → SN-app₁ (s (app₁ f~>f'))

neu : ∀ {Γ A} → Tm Γ A → Set
neu (var _)   = ⊤
neu (lam _)   = ⊥
neu (app _ _) = ⊤

neuᵣ : ∀ {Γ Δ A}(σ : Ren Δ Γ)(t : Tm Γ A) → neu t → neu (t [ σ ]ᵣ)
neuᵣ σ (var v)   nt = tt
neuᵣ σ (app f a) nt = tt
neuᵣ σ (lam t) ()

--------------------------------------------------------------------------------

Tmᴺ : ∀ {Γ A} → Tm Γ A → Set
Tmᴺ {Γ}{ι}     t = SN t
Tmᴺ {Γ}{A ⇒ B} t = ∀ {Δ}(σ : Ren Δ Γ){a} → Tmᴺ a → Tmᴺ (app (t [ σ ]ᵣ) a)

data Tmsᴺ {Γ} : ∀ {Δ} → Tms Γ Δ → Set where
  ∙   : Tmsᴺ ∙
  _,_ : ∀ {A Δ}{σ : Tms Γ Δ}{t : Tm Γ A}(σᴺ : Tmsᴺ σ)(tᴺ : Tmᴺ t) → Tmsᴺ (σ , t)

infixl 6 _ᴺ[_]ᵣ
_ᴺ[_]ᵣ : ∀ {A Γ Δ}{t : Tm Γ A} → Tmᴺ t → (σ : Ren Δ Γ) → Tmᴺ (t [ σ ]ᵣ)
_ᴺ[_]ᵣ {ι} tᴺ σ = SNᵣ→ σ tᴺ
_ᴺ[_]ᵣ {A ⇒ B} {t = t} tᴺ σ δ aᴺ rewrite ∘ᵣTm t σ δ = tᴺ (σ ∘ᵣ δ) aᴺ

infixr 6 _ᴺ∘ᵣ_
_ᴺ∘ᵣ_ : ∀ {Γ Δ Σ}{σ : Tms Δ Σ} → Tmsᴺ σ → (δ : Ren Γ Δ) → Tmsᴺ (σ ₛ∘ᵣ δ)
∙         ᴺ∘ᵣ δ = ∙
(σᴺ , tᴺ) ᴺ∘ᵣ δ = (σᴺ ᴺ∘ᵣ δ) , (tᴺ ᴺ[ δ ]ᵣ)

~>ᴺ : ∀ {Γ A}{t t' : Tm Γ A} → t ~> t' → Tmᴺ t → Tmᴺ t'
~>ᴺ {A = ι}     t~>t' (sn st) = st t~>t'
~>ᴺ {A = A ⇒ B} t~>t' tᴺ      = λ σ aᴺ → ~>ᴺ (app₁ (~>ᵣ σ t~>t')) (tᴺ σ aᴺ)

mutual
  qᴺ : ∀ {Γ A}{t : Tm Γ A} → Tmᴺ t → SN t
  qᴺ {Γ}{ι} tᴺ = tᴺ
  qᴺ {Γ}{A ⇒ B} {t} tᴺ =
    SNᵣ← wk $ SN-app₁ (qᴺ $ tᴺ wk (uᴺ (var vz) (λ ())))

  uᴺ : ∀ {Γ A}(t : Tm Γ A){nt : neu t} → (∀ {t'} → t ~> t' → Tmᴺ t') → Tmᴺ t
  uᴺ {Γ} {A = ι} t      f     = sn f  
  uᴺ {Γ} {A ⇒ B} t {nt} f {Δ} σ {a} aᴺ =
    uᴺ (app (t [ σ ]ᵣ) a) (go (t [ σ ]ᵣ) (neuᵣ σ t nt) f' a aᴺ (qᴺ aᴺ))
    where
      f' : ∀ {t'} → t [ σ ]ᵣ ~> t' → Tmᴺ t'
      f' step δ aᴺ with ~>un-r step
      ... | t'' , (step' , refl) rewrite ∘ᵣTm t'' σ δ = f step' (σ ∘ᵣ δ) aᴺ

      go :
        ∀ {Γ A B}(t : Tm Γ (A ⇒ B)) → neu t → (∀ {t'} → t ~> t' → Tmᴺ t')
        → ∀ a → Tmᴺ a → SN a → ∀ {t'} → app t a ~> t' → Tmᴺ t'
      go _ () _ _ _ _ (β _ _)
      go t nt f a aᴺ sna (app₁ {f' = f'} step) =
        coe ((λ x → Tmᴺ (app x a)) & idᵣTm f') (f step idᵣ aᴺ)
      go t nt f a aᴺ (sn sa) (app₂ {a' = a'} step) =
        uᴺ (app t a') (go t nt f a' (~>ᴺ step aᴺ) (sa step))
     
∈↑ᴺ : ∀ {Γ A}(v : A ∈ Γ) → ∀ {Δ}{σ : Tms Δ Γ} → Tmsᴺ σ → Tmᴺ (v [ σ ]∈)
∈↑ᴺ vz     (σᴺ , tᴺ) = tᴺ
∈↑ᴺ (vs v) (σᴺ , tᴺ) = ∈↑ᴺ v σᴺ

lamᴺ :
  ∀ {Γ A B}(t : Tm (Γ , A) B)
  → SN t
  → (∀ {a} → Tmᴺ a → Tmᴺ (t [ idₛ , a ]))
  → ∀ a → SN a → Tmᴺ a
  → Tmᴺ (app (lam t) a)
lamᴺ {Γ} t (sn st) f a (sn sa) aᴺ = uᴺ (app (lam t) a)
  λ {(β _ _) → f aᴺ;
     (app₁ (lam {t' = t'} t~>t')) →
       lamᴺ t' (st t~>t') (λ aᴺ → ~>ᴺ (~>ₛ _ t~>t') (f aᴺ)) a (sn sa) aᴺ;     
     (app₂ a~>a') →
       lamᴺ t (sn st) f _ (sa a~>a') (~>ᴺ a~>a' aᴺ)}

Tm↑ᴺ : ∀ {Γ A}(t : Tm Γ A) → ∀ {Δ}{σ : Tms Δ Γ} → Tmsᴺ σ → Tmᴺ (t [ σ ])
Tm↑ᴺ (var v) σᴺ = ∈↑ᴺ v σᴺ
Tm↑ᴺ (lam {A} t) {σ = σ} σᴺ δ {a} aᴺ
  rewrite ₛ∘ᵣTm t (keepₛ σ) (keep δ) | assₛᵣᵣ σ (wk {A}) (keep δ) | idlᵣ δ
  = lamᴺ 
      (t [ σ ₛ∘ᵣ drop δ , var vz ])      
      (qᴺ (Tm↑ᴺ t (σᴺ ᴺ∘ᵣ drop δ , uᴺ (var vz) (λ ()))))
      
      (λ {a} aᴺ →
        coe
          (Tmᴺ &
            ((t [_]) & ((_, a) &
                (idrₛ (σ ₛ∘ᵣ δ) ⁻¹
               ◾ assₛᵣₛ  σ δ idₛ
               ◾ assₛᵣₛ σ (drop δ) (idₛ , a) ⁻¹))
            ◾ ∘ₛTm t ((σ ₛ∘ᵣ drop δ) , var vz) (idₛ , a) ⁻¹))
        (Tm↑ᴺ t (σᴺ ᴺ∘ᵣ δ , aᴺ)))
        
      a (qᴺ aᴺ) aᴺ
      
Tm↑ᴺ (app f a) {σ = σ} σᴺ
  rewrite idᵣTm (f [ σ ]) ⁻¹ = Tm↑ᴺ f σᴺ idᵣ (Tm↑ᴺ a σᴺ)

idₛᴺ : ∀ {Γ} → Tmsᴺ (idₛ {Γ})
idₛᴺ {∙}     = ∙
idₛᴺ {Γ , A} = (idₛᴺ ᴺ∘ᵣ wk) , uᴺ (var vz) (λ ())

norm : ∀ {Γ A}(t : Tm Γ A) → SN t
norm t = qᴺ (coe (Tmᴺ & idₛTm t ) (Tm↑ᴺ t idₛᴺ))

