
{-
Strong β-normalization for Gödel's System T
as appears in chapter 7 of
http://www.paultaylor.eu/stable/prot.pdf
-}

{-# OPTIONS --without-K #-}

open import Lib

-- Syntax
--------------------------------------------------------------------------------

infixr 4 _⇒_

data Ty : Set where
  ι    : Ty
  _*_  : Ty → Ty → Ty
  Bool : Ty
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

  _,_   : ∀ {A B} → Tm Γ A → Tm Γ B → Tm Γ (A * B)
  π₁    : ∀ {A B} → Tm Γ (A * B) → Tm Γ A
  π₂    : ∀ {A B} → Tm Γ (A * B) → Tm Γ B

  true  : Tm Γ Bool
  false : Tm Γ Bool
  if    : ∀ {A} → Tm Γ Bool → Tm Γ A → Tm Γ A → Tm Γ A

  zero  : Tm Γ Nat
  suc   : Tm Γ Nat → Tm Γ Nat
  iter  : ∀ {A} → Tm Γ Nat → Tm Γ (Nat ⇒ A ⇒ A) → Tm Γ A → Tm Γ A

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
var v      [ σ ]ᵣ = var (v [ σ ]∈ᵣ)
lam t      [ σ ]ᵣ = lam (t [ keep σ ]ᵣ)
app f a    [ σ ]ᵣ = app (f [ σ ]ᵣ) (a [ σ ]ᵣ)
(a , b)    [ σ ]ᵣ = a [ σ ]ᵣ , b [ σ ]ᵣ
π₁ p       [ σ ]ᵣ = π₁ (p [ σ ]ᵣ)
π₂ p       [ σ ]ᵣ = π₂ (p [ σ ]ᵣ)
true       [ σ ]ᵣ = true
false      [ σ ]ᵣ = false
if b t f   [ σ ]ᵣ = if (b [ σ ]ᵣ) (t [ σ ]ᵣ) (f [ σ ]ᵣ)
zero       [ σ ]ᵣ = zero
suc n      [ σ ]ᵣ = suc (n [ σ ]ᵣ)
iter n s z [ σ ]ᵣ = iter (n [ σ ]ᵣ) (s [ σ ]ᵣ) (z [ σ ]ᵣ)    

idᵣTm : ∀ {Γ A}(t : Tm Γ A) → t [ idᵣ ]ᵣ ≡ t
idᵣTm (var v     ) = var & idᵣ∈ v
idᵣTm (lam t     ) = lam & idᵣTm t
idᵣTm (app f a   ) = app & idᵣTm f ⊗ idᵣTm a
idᵣTm (a , b     ) = _,_ & idᵣTm a ⊗ idᵣTm b
idᵣTm (π₁ p      ) = π₁ & idᵣTm p
idᵣTm (π₂ p      ) = π₂ & idᵣTm p
idᵣTm (true      ) = refl
idᵣTm (false     ) = refl
idᵣTm (if b t f  ) = if & idᵣTm b ⊗ idᵣTm t ⊗ idᵣTm f
idᵣTm (zero      ) = refl
idᵣTm (suc n     ) = suc & idᵣTm n
idᵣTm (iter n s z) = iter & idᵣTm n ⊗ idᵣTm s ⊗ idᵣTm z

∘ᵣTm :
  ∀ {Γ Δ Σ A}(t : Tm Σ A)(σ : Ren Δ Σ)(δ : Ren Γ Δ)
  → t [ σ ]ᵣ [ δ ]ᵣ ≡ t [ σ ∘ᵣ δ ]ᵣ
∘ᵣTm (var v     ) σ δ = var & ∘ᵣ∈ v σ δ
∘ᵣTm (lam t     ) σ δ = lam & ∘ᵣTm t (keep σ) (keep δ)
∘ᵣTm (app f a   ) σ δ = app & ∘ᵣTm f σ δ ⊗ ∘ᵣTm a σ δ
∘ᵣTm (a , b     ) σ δ = _,_ & ∘ᵣTm a σ δ ⊗ ∘ᵣTm b σ δ
∘ᵣTm (π₁ p      ) σ δ = π₁ & ∘ᵣTm p σ δ
∘ᵣTm (π₂ p      ) σ δ = π₂ & ∘ᵣTm p σ δ
∘ᵣTm (true      ) σ δ = refl
∘ᵣTm (false     ) σ δ = refl
∘ᵣTm (if b t f  ) σ δ = if & ∘ᵣTm b σ δ ⊗ ∘ᵣTm t σ δ ⊗ ∘ᵣTm f σ δ
∘ᵣTm (zero      ) σ δ = refl
∘ᵣTm (suc n     ) σ δ = suc & ∘ᵣTm n σ δ
∘ᵣTm (iter n s z) σ δ = iter & ∘ᵣTm n σ δ ⊗ ∘ᵣTm s σ δ ⊗ ∘ᵣTm z σ δ

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
var v      [ σ ] = v [ σ ]∈
lam t      [ σ ] = lam (t [ keepₛ σ ])
app f a    [ σ ] = app (f [ σ ]) (a [ σ ])
(a , b)    [ σ ] = a [ σ ] , b [ σ ]
π₁ p       [ σ ] = π₁ (p [ σ ])
π₂ p       [ σ ] = π₂ (p [ σ ])
true       [ σ ] = true
false      [ σ ] = false
if b t f   [ σ ] = if (b [ σ ]) (t [ σ ]) (f [ σ ])
zero       [ σ ] = zero
suc n      [ σ ] = suc (n [ σ ])
iter n s z [ σ ] = iter (n [ σ ]) (s [ σ ]) (z [ σ ])    

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
ᵣ∘ₛTm (var v     ) σ δ = ᵣ∘ₛ∈ v σ δ
ᵣ∘ₛTm (lam t     ) σ δ = lam &
      (ᵣ∘ₛTm t (keep σ) (keepₛ δ)
    ◾ (λ σ → t [ σ , var vz ]) & (assᵣₛᵣ σ δ wk ⁻¹))
ᵣ∘ₛTm (app f a   ) σ δ = app & ᵣ∘ₛTm f σ δ ⊗ ᵣ∘ₛTm a σ δ
ᵣ∘ₛTm (a , b     ) σ δ = _,_ & ᵣ∘ₛTm a σ δ ⊗ ᵣ∘ₛTm b σ δ
ᵣ∘ₛTm (π₁ p      ) σ δ = π₁ & ᵣ∘ₛTm p σ δ
ᵣ∘ₛTm (π₂ p      ) σ δ = π₂ & ᵣ∘ₛTm p σ δ
ᵣ∘ₛTm (true      ) σ δ = refl
ᵣ∘ₛTm (false     ) σ δ = refl
ᵣ∘ₛTm (if b t f  ) σ δ = if & ᵣ∘ₛTm b σ δ ⊗ ᵣ∘ₛTm t σ δ ⊗ ᵣ∘ₛTm f σ δ
ᵣ∘ₛTm (zero      ) σ δ = refl
ᵣ∘ₛTm (suc n     ) σ δ = suc & ᵣ∘ₛTm n σ δ
ᵣ∘ₛTm (iter n s z) σ δ = iter & ᵣ∘ₛTm n σ δ ⊗ ᵣ∘ₛTm s σ δ ⊗ ᵣ∘ₛTm z σ δ 

ₛ∘ᵣ∈ :
  ∀ {Γ Δ Σ A}(v : A ∈ Σ)(σ : Tms Δ Σ)(δ : Ren Γ Δ)
  → v [ σ ]∈ [ δ ]ᵣ ≡ v [ σ ₛ∘ᵣ δ ]∈
ₛ∘ᵣ∈ vz     (σ , _) δ = refl
ₛ∘ᵣ∈ (vs v) (σ , _) δ = ₛ∘ᵣ∈ v σ δ  

ₛ∘ᵣTm :
  ∀ {Γ Δ Σ A}(t : Tm Σ A)(σ : Tms Δ Σ)(δ : Ren Γ Δ)
  → t [ σ ] [ δ ]ᵣ ≡ t [ σ ₛ∘ᵣ δ ]
ₛ∘ᵣTm (var v     ) σ δ = ₛ∘ᵣ∈ v σ δ
ₛ∘ᵣTm (lam t     ) σ δ = 
  lam & (
      ₛ∘ᵣTm t (keepₛ σ) (keep δ)
    ◾ (λ σ → t [ σ , var vz ]) &
        (assₛᵣᵣ σ wk (keep δ)
      ◾ ((λ δ → σ ₛ∘ᵣ (drop δ)) &
          idlᵣ δ
        ◾ (λ δ → σ ₛ∘ᵣ drop δ) & (idrᵣ δ ⁻¹)
        ◾ assₛᵣᵣ σ δ wk ⁻¹)))
ₛ∘ᵣTm (app f a   ) σ δ = app & ₛ∘ᵣTm f σ δ ⊗ ₛ∘ᵣTm a σ δ
ₛ∘ᵣTm (a , b     ) σ δ = _,_ & ₛ∘ᵣTm a σ δ ⊗ ₛ∘ᵣTm b σ δ
ₛ∘ᵣTm (π₁ p      ) σ δ = π₁ & ₛ∘ᵣTm p σ δ
ₛ∘ᵣTm (π₂ p      ) σ δ = π₂ & ₛ∘ᵣTm p σ δ
ₛ∘ᵣTm (true      ) σ δ = refl
ₛ∘ᵣTm (false     ) σ δ = refl
ₛ∘ᵣTm (if b t f  ) σ δ = if & ₛ∘ᵣTm b σ δ ⊗ ₛ∘ᵣTm t σ δ ⊗ ₛ∘ᵣTm f σ δ
ₛ∘ᵣTm (zero      ) σ δ = refl
ₛ∘ᵣTm (suc n     ) σ δ = suc & ₛ∘ᵣTm n σ δ
ₛ∘ᵣTm (iter n s z) σ δ = iter & ₛ∘ᵣTm n σ δ ⊗ ₛ∘ᵣTm s σ δ ⊗ ₛ∘ᵣTm z σ δ

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
∘ₛTm (var v     ) σ δ = ∘ₛ∈ v σ δ
∘ₛTm (lam t     ) σ δ =
  lam & (
      ∘ₛTm t (keepₛ σ) (keepₛ δ)
    ◾ (λ σ → t [ σ , var vz ]) &
        (assₛᵣₛ σ wk (keepₛ δ)
      ◾ (σ ∘ₛ_) & idlᵣₛ (δ ₛ∘ᵣ wk) ◾ assₛₛᵣ σ δ wk ⁻¹))
∘ₛTm (app f a   ) σ δ = app & ∘ₛTm f σ δ ⊗ ∘ₛTm a σ δ
∘ₛTm (a , b     ) σ δ = _,_ & ∘ₛTm a σ δ ⊗ ∘ₛTm b σ δ
∘ₛTm (π₁ p      ) σ δ = π₁ & ∘ₛTm p σ δ
∘ₛTm (π₂ p      ) σ δ = π₂ & ∘ₛTm p σ δ
∘ₛTm (true      ) σ δ = refl
∘ₛTm (false     ) σ δ = refl
∘ₛTm (if b t f  ) σ δ = if & ∘ₛTm b σ δ ⊗ ∘ₛTm t σ δ ⊗ ∘ₛTm f σ δ
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
idlₛ (σ , t) = (_, t) & (assₛᵣₛ idₛ wk (σ , t) ◾ (idₛ ∘ₛ_) & idlᵣₛ σ ◾ idlₛ σ)

idₛ∈ : ∀ {Γ A}(v : A ∈ Γ) → v [ idₛ ]∈ ≡ var v
idₛ∈ vz     = refl
idₛ∈ (vs v) = ₛ∘ᵣ∈ v idₛ wk ⁻¹ ◾ (_[ wk ]ᵣ) & idₛ∈ v ◾ (λ v → var (vs v)) & idᵣ∈ v

idₛTm : ∀ {Γ A}(t : Tm Γ A) → t [ idₛ ] ≡ t
idₛTm (var v     ) = idₛ∈ v
idₛTm (lam t     ) = lam & idₛTm t
idₛTm (app f a   ) = app & idₛTm f ⊗ idₛTm a
idₛTm (a , b     ) = _,_ & idₛTm a ⊗ idₛTm b
idₛTm (π₁ p      ) = π₁ & idₛTm p
idₛTm (π₂ p      ) = π₂ & idₛTm p
idₛTm (true      ) = refl
idₛTm (false     ) = refl
idₛTm (if b t f  ) = if & idₛTm b ⊗ idₛTm t ⊗ idₛTm f
idₛTm (zero      ) = refl
idₛTm (suc n     ) = suc & idₛTm n
idₛTm (iter n s z) = iter & idₛTm n ⊗ idₛTm s ⊗ idₛTm z

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
  
  π₁   : ∀ {A B}{p p' : Tm Γ (A * B)}        → p ~> p' →  π₁ p    ~> π₁ p'
  π₂   : ∀ {A B}{p p' : Tm Γ (A * B)}        → p ~> p' →  π₂ p    ~> π₂ p'
  π₁β  : ∀ {A B}{a : Tm Γ A}{b : Tm Γ B}     → π₁ (a , b) ~> a
  π₂β  : ∀ {A B}{a : Tm Γ A}{b : Tm Γ B}     → π₂ (a , b) ~> b
  ,₁   : ∀ {A B}{a a' : Tm Γ A}{b : Tm Γ B}  → a ~> a' → (a , b) ~> (a' , b)
  ,₂   : ∀ {A B}{a : Tm Γ A}{b b' : Tm Γ B}  → b ~> b' → (a , b) ~> (a , b')

  if-true  : ∀ {A}{t f : Tm Γ A} → if true  t f ~> t
  if-false : ∀ {A}{t f : Tm Γ A} → if false t f ~> f
  if₁      : ∀ {A}{b b'}{t f : Tm Γ A} → b ~> b' → if b t f ~> if b' t f
  if₂      : ∀ {A}{b}{t t' f : Tm Γ A} → t ~> t' → if b t f ~> if b t' f
  if₃      : ∀ {A}{b}{t f f' : Tm Γ A} → f ~> f' → if b t f ~> if b t f'    

  suc       : ∀ {n n'} → n ~> n' → suc n ~> suc n'
  iter-suc  : ∀ {A}{n}{s}{z : Tm Γ A} → iter (suc n) s z ~> app (app s n) (iter n s z)
  iter-zero : ∀ {A}{s}{z : Tm Γ A}    → iter zero s z    ~> z
  iter₁     : ∀ {A}{n n'}{s}{z : Tm Γ A} → n ~> n' → iter n s z ~> iter n' s z
  iter₂     : ∀ {A}{n}{s s'}{z : Tm Γ A} → s ~> s' → iter n s z ~> iter n s' z
  iter₃     : ∀ {A}{n}{s}{z z' : Tm Γ A} → z ~> z' → iter n s z ~> iter n s z'

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
~>ₛ σ (lam t~>t') = lam (~>ₛ ((σ ₛ∘ᵣ drop idᵣ) , var vz) t~>t')
~>ₛ σ (app₁ t~>t') = app₁ (~>ₛ σ t~>t')
~>ₛ σ (app₂ t~>t') = app₂ (~>ₛ σ t~>t')
~>ₛ σ (π₁ t~>t') = π₁ (~>ₛ σ t~>t')
~>ₛ σ (π₂ t~>t') = π₂ (~>ₛ σ t~>t')
~>ₛ σ π₁β = π₁β
~>ₛ σ π₂β = π₂β
~>ₛ σ (,₁ t~>t') = ,₁ (~>ₛ σ t~>t')
~>ₛ σ (,₂ t~>t') = ,₂ (~>ₛ σ t~>t')
~>ₛ σ if-true = if-true
~>ₛ σ if-false = if-false
~>ₛ σ (if₁ t~>t') = if₁ (~>ₛ σ t~>t')
~>ₛ σ (if₂ t~>t') = if₂ (~>ₛ σ t~>t')
~>ₛ σ (if₃ t~>t') = if₃ (~>ₛ σ t~>t')
~>ₛ σ (suc t~>t') = suc (~>ₛ σ t~>t')
~>ₛ σ iter-suc = iter-suc
~>ₛ σ iter-zero = iter-zero
~>ₛ σ (iter₁ t~>t') = iter₁ (~>ₛ σ t~>t')
~>ₛ σ (iter₂ t~>t') = iter₂ (~>ₛ σ t~>t')
~>ₛ σ (iter₃ t~>t') = iter₃ (~>ₛ σ t~>t')

~>ᵣ : ∀ {Γ Δ A}{t t' : Tm Γ A}(σ : Ren Δ Γ) → t ~> t' → t [ σ ]ᵣ ~> t' [ σ ]ᵣ
~>ᵣ σ (β t t') =
  coe ((app (lam (t [ keep σ ]ᵣ)) (t' [ σ ]ᵣ) ~>_) &
      (ᵣ∘ₛTm t (keep σ) (idₛ , (t' [ σ ]ᵣ))
    ◾ (t [_]) & ((_, (t' [ σ ]ᵣ)) & (idrᵣₛ σ ◾ idlₛᵣ σ ⁻¹))
    ◾ ₛ∘ᵣTm t (idₛ , t') σ ⁻¹))
  (β (t [ keep σ ]ᵣ) (t' [ σ ]ᵣ))
~>ᵣ σ (lam t~>t') = lam (~>ᵣ (keep σ) t~>t')
~>ᵣ σ (app₁ t~>t') = app₁ (~>ᵣ σ t~>t')
~>ᵣ σ (app₂ t~>t') = app₂ (~>ᵣ σ t~>t')
~>ᵣ σ (π₁ t~>t') = π₁ (~>ᵣ σ t~>t')
~>ᵣ σ (π₂ t~>t') = π₂ (~>ᵣ σ t~>t')
~>ᵣ σ π₁β = π₁β
~>ᵣ σ π₂β = π₂β
~>ᵣ σ (,₁ t~>t') = ,₁ (~>ᵣ σ t~>t')
~>ᵣ σ (,₂ t~>t') = ,₂ (~>ᵣ σ t~>t')
~>ᵣ σ if-true = if-true
~>ᵣ σ if-false = if-false
~>ᵣ σ (if₁ t~>t') = if₁ (~>ᵣ σ t~>t')
~>ᵣ σ (if₂ t~>t') = if₂ (~>ᵣ σ t~>t')
~>ᵣ σ (if₃ t~>t') = if₃ (~>ᵣ σ t~>t')
~>ᵣ σ (suc t~>t') = suc (~>ᵣ σ t~>t')
~>ᵣ σ iter-suc = iter-suc
~>ᵣ σ iter-zero = iter-zero
~>ᵣ σ (iter₁ t~>t') = iter₁ (~>ᵣ σ t~>t')
~>ᵣ σ (iter₂ t~>t') = iter₂ (~>ᵣ σ t~>t')
~>ᵣ σ (iter₃ t~>t') = iter₃ (~>ᵣ σ t~>t')

-- no point writing out this shit
~>un-r :
  ∀ {Γ Δ A}{t : Tm Γ A}{σ : Ren Δ Γ}{t'}
  → t [ σ ]ᵣ ~> t' → Σ _ λ t'' → (t ~> t'') × (t'' [ σ ]ᵣ ≡ t')
~>un-r = {!!}  


-- Strong normalization definition + lemmas
--------------------------------------------------------------------------------

data SN {Γ A} (t : Tm Γ A) : Set where
  sn : (∀ {t'} → t ~> t' → SN t') → SN t

runSN : ∀ {Γ A}{t : Tm Γ A} → SN t → ∀ {t'} → t ~> t' → SN t'
runSN (sn s) = s

SNᵣ→ : ∀ {Γ Δ A}{t : Tm Γ A}(σ : Ren Δ Γ) → SN t → SN (t [ σ ]ᵣ)
SNᵣ→ σ (sn s) = sn λ {t'} step →
  let (t'' , (p , q)) = ~>un-r step in coe (SN & q) (SNᵣ→ σ (s p))

SNᵣ← : ∀ {Γ Δ A}{t : Tm Γ A}(σ : Ren Δ Γ) → SN (t [ σ ]ᵣ) → SN t
SNᵣ← σ (sn s) = sn λ step → SNᵣ← σ (s (~>ᵣ σ step))

SN-app₁ : ∀ {Γ A B}{f : Tm Γ (A ⇒ B)}{a} → SN (app f a) → SN f
SN-app₁ (sn s) = sn λ f~>f' → SN-app₁ (s (app₁ f~>f'))

SN-suc→ : ∀ {Γ}{n : Tm Γ Nat} → SN n → SN (suc n)
SN-suc→ (sn s) = sn (λ {(suc step) → SN-suc→ (s step)})

SN-suc← : ∀ {Γ}{n : Tm Γ Nat} → SN (suc n) → SN n
SN-suc← (sn s) = sn (λ step → SN-suc← (s (suc step)))

SN-π₁ : ∀ {Γ A B}{p : Tm Γ (A * B)} → SN (π₁ p) → SN p
SN-π₁ (sn s) = sn (λ step → SN-π₁ (s (π₁ step)))

Neu : ∀ {Γ A} → Tm Γ A → Set
Neu (var _)      = ⊤
Neu (lam _)      = ⊥
Neu (app _ _)    = ⊤
Neu (_ , _)      = ⊥
Neu (π₁ _)       = ⊤
Neu (π₂ _)       = ⊤
Neu true         = ⊥
Neu false        = ⊥
Neu (if _ _ _)   = ⊤
Neu zero         = ⊥
Neu (suc _)      = ⊥
Neu (iter _ _ _) = ⊤

Neuᵣ : ∀ {Γ Δ A}(σ : Ren Δ Γ)(t : Tm Γ A) → Neu t → Neu (t [ σ ]ᵣ)
Neuᵣ σ (var _)      nt = tt
Neuᵣ σ (lam _)      nt = nt
Neuᵣ σ (app _ _)    nt = tt
Neuᵣ σ (_ , _)      nt = nt
Neuᵣ σ (π₁ _)       nt = tt
Neuᵣ σ (π₂ _)       nt = tt
Neuᵣ σ true         nt = nt
Neuᵣ σ false        nt = nt
Neuᵣ σ (if _ _ _)   nt = tt
Neuᵣ σ zero         nt = nt
Neuᵣ σ (suc _)      nt = nt
Neuᵣ σ (iter _ _ _) nt = tt


--------------------------------------------------------------------------------

Tmᴺ : ∀ {Γ A} → Tm Γ A → Set
Tmᴺ {Γ} {ι}     t = SN t
Tmᴺ {Γ} {A * B} p = Tmᴺ (π₁ p) × Tmᴺ (π₂ p)
Tmᴺ {Γ} {Bool}  b = SN b
Tmᴺ {Γ} {Nat}   n = SN n
Tmᴺ {Γ} {A ⇒ B} t = ∀ {Δ}(σ : Ren Δ Γ){a} → Tmᴺ a → Tmᴺ (app (t [ σ ]ᵣ) a)

data Tmsᴺ {Γ} : ∀ {Δ} → Tms Γ Δ → Set where
  ∙   : Tmsᴺ ∙
  _,_ : ∀ {A Δ}{σ : Tms Γ Δ}{t : Tm Γ A}(σᴺ : Tmsᴺ σ)(tᴺ : Tmᴺ t) → Tmsᴺ (σ , t)

infixl 6 _,_ᴺ[_]ᵣ
_,_ᴺ[_]ᵣ : ∀ {A Γ Δ}(t : Tm Γ A) → Tmᴺ t → (σ : Ren Δ Γ) → Tmᴺ (t [ σ ]ᵣ)
_,_ᴺ[_]ᵣ {ι}     t tᴺ σ = SNᵣ→ σ tᴺ
_,_ᴺ[_]ᵣ {A * B} t (aᴺ , bᴺ) σ = (π₁ t , aᴺ ᴺ[ σ ]ᵣ) , (π₂ t , bᴺ ᴺ[ σ ]ᵣ)
_,_ᴺ[_]ᵣ {Bool}  t tᴺ σ = SNᵣ→ σ tᴺ
_,_ᴺ[_]ᵣ {Nat}   t tᴺ σ = SNᵣ→ σ tᴺ
_,_ᴺ[_]ᵣ {A ⇒ B} t tᴺ σ δ aᴺ rewrite ∘ᵣTm t σ δ = tᴺ (σ ∘ᵣ δ) aᴺ

infixr 6 _ᴺ∘ᵣ_
_ᴺ∘ᵣ_ : ∀ {Γ Δ Σ}{σ : Tms Δ Σ} → Tmsᴺ σ → (δ : Ren Γ Δ) → Tmsᴺ (σ ₛ∘ᵣ δ)
∙                 ᴺ∘ᵣ δ = ∙
_,_ {t = t} σᴺ tᴺ ᴺ∘ᵣ δ = (σᴺ ᴺ∘ᵣ δ) , (t , tᴺ ᴺ[ δ ]ᵣ)

~>ᴺ : ∀ {Γ A}{t t' : Tm Γ A} → t ~> t' → Tmᴺ t → Tmᴺ t'
~>ᴺ {A = ι}     t~>t' (sn st)   = st t~>t'
~>ᴺ {A = A * B} t~>t' (aᴺ , bᴺ) = (~>ᴺ (π₁ t~>t') aᴺ) , (~>ᴺ (π₂ t~>t') bᴺ)
~>ᴺ {A = Bool}  t~>t' (sn st)   = st t~>t'
~>ᴺ {A = Nat}   t~>t' (sn st)   = st t~>t'
~>ᴺ {A = A ⇒ B} t~>t' tᴺ        = λ σ aᴺ → ~>ᴺ (app₁ (~>ᵣ σ t~>t')) (tᴺ σ aᴺ)

mutual
  qᴺ : ∀ {Γ A}{t : Tm Γ A} → Tmᴺ t → SN t
  qᴺ {A = ι}     tᴺ        = tᴺ
  qᴺ {A = A * B} (aᴺ , bᴺ) = SN-π₁ (qᴺ aᴺ)
  qᴺ {A = Bool}  tᴺ        = tᴺ
  qᴺ {A = Nat}   tᴺ        = tᴺ
  qᴺ {A = A ⇒ B} tᴺ        = SNᵣ← wk $ SN-app₁ (qᴺ $ tᴺ wk (uᴺ (var (vz {A})) (λ ())))

  uᴺ : ∀ {Γ A}(t : Tm Γ A){_ : Neu t} → (∀ {t'} → t ~> t' → Tmᴺ t') → Tmᴺ t
  uᴺ {A = ι}     t f = sn f
  uᴺ {A = A * B} t {nt} f =
    uᴺ (π₁ t) (λ {(π₁ t~>t') → proj₁ (f t~>t'); π₁β → ⊥-elim nt}) ,
    uᴺ (π₂ t) (λ {(π₂ t~>t') → proj₂ (f t~>t'); π₂β → ⊥-elim nt})
  uᴺ {A = Bool}  t f = sn f
  uᴺ {A = Nat}   t f = sn f
  uᴺ {A = A ⇒ B} t {nt} f {Δ} σ {a} aᴺ = 
    uᴺ (app (t [ σ ]ᵣ) a) (go (t [ σ ]ᵣ) (Neuᵣ σ t nt) f' a aᴺ (qᴺ aᴺ))
    where
      f' : ∀ {t'} → t [ σ ]ᵣ ~> t' → Tmᴺ t'
      f' step δ aᴺ with ~>un-r step
      ... | t'' , (step' , refl) rewrite ∘ᵣTm t'' σ δ = f step' (σ ∘ᵣ δ) aᴺ

      go :
        ∀ {Γ A B}(t : Tm Γ (A ⇒ B)) → Neu t → (∀ {t'} → t ~> t' → Tmᴺ t')
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

ifᴺ :
  ∀ {Γ A}(b : Tm Γ Bool)(t f : Tm Γ A)
  → SN b → SN t → SN f
  → Tmᴺ t → Tmᴺ f
  → Tmᴺ (if b t f)
ifᴺ b t f (sn sb) (sn st) (sn sf) tᴺ fᴺ = uᴺ (if b t f)
  λ {if-true     → tᴺ;
     if-false    → fᴺ;
     (if₁ b~>b') → ifᴺ _ t f (sb b~>b') (sn st) (sn sf) tᴺ fᴺ;
     (if₂ t~>t') → ifᴺ b _ f (sn sb) (st t~>t') (sn sf) (~>ᴺ t~>t' tᴺ) fᴺ;
     (if₃ f~>f') → ifᴺ b t _ (sn sb) (sn st) (sf f~>f') tᴺ (~>ᴺ f~>f' fᴺ)}

π₁ᴺ :
  ∀ {Γ A B}(a : Tm Γ A)(b : Tm Γ B)
  → SN a → SN b → Tmᴺ a → Tmᴺ b → Tmᴺ (π₁ (a , b))
π₁ᴺ a b (sn sa) (sn sb) aᴺ bᴺ = uᴺ (π₁ (a , b))
  λ {(π₁ (,₁ a~>a')) → π₁ᴺ _ b (sa a~>a') (sn sb) (~>ᴺ a~>a' aᴺ) bᴺ;
     (π₁ (,₂ b~>b')) → π₁ᴺ a _ (sn sa) (sb b~>b') aᴺ (~>ᴺ b~>b' bᴺ);
      π₁β            → aᴺ}

π₂ᴺ :
  ∀ {Γ A B}(a : Tm Γ A)(b : Tm Γ B)
  → SN a → SN b → Tmᴺ a → Tmᴺ b → Tmᴺ (π₂ (a , b))
π₂ᴺ a b (sn sa) (sn sb) aᴺ bᴺ = uᴺ (π₂ (a , b))
  λ {(π₂ (,₁ a~>a')) → π₂ᴺ _ b (sa a~>a') (sn sb) (~>ᴺ a~>a' aᴺ) bᴺ;
     (π₂ (,₂ b~>b')) → π₂ᴺ a _ (sn sa) (sb b~>b') aᴺ (~>ᴺ b~>b' bᴺ);
      π₂β            → bᴺ}

appᴺ : ∀ {Γ A B}{f : Tm Γ (A ⇒ B)}{a} → Tmᴺ f → Tmᴺ a → Tmᴺ (app f a)
appᴺ {f = f} {a} fᴺ aᴺ = coe ((λ x → Tmᴺ (app x a)) & idᵣTm f) (fᴺ idᵣ aᴺ)

{-# TERMINATING #-} -- I swear it's Agda's fault
iterᴺ :
  ∀ {Γ A}(n : Tm Γ Nat)(s : Tm Γ (Nat ⇒ A ⇒ A))(z : Tm Γ A)
  → SN n → SN s → SN z
  → Tmᴺ s → Tmᴺ z
  → Tmᴺ (iter n s z)
iterᴺ n s z (sn sₙ) (sn ss) (sn sz) sᴺ zᴺ = uᴺ (iter n s z)
  λ {(iter-suc {n = n}) →
       let snn = SN-suc← (sn sₙ)
           nextᴺ = iterᴺ n s z snn (sn ss) (sn sz) sᴺ zᴺ
       in appᴺ {f = app s n} (appᴺ {f = s} sᴺ snn) nextᴺ; -- Agda can't see n decreasing
     iter-zero          → zᴺ;
     (iter₁ n~>n')      → iterᴺ _ s z (sₙ n~>n') (sn ss) (sn sz) sᴺ zᴺ;
     (iter₂ s~>s')      → iterᴺ n _ z (sn sₙ) (ss s~>s') (sn sz) (~>ᴺ s~>s' sᴺ) zᴺ;
     (iter₃ z~>z')      → iterᴺ n s _ (sn sₙ) (sn ss) (sz z~>z') sᴺ (~>ᴺ z~>z' zᴺ)}         
     
Tm↑ᴺ : ∀ {Γ A}(t : Tm Γ A) → ∀ {Δ}{σ : Tms Δ Γ} → Tmsᴺ σ → Tmᴺ (t [ σ ])
Tm↑ᴺ (var v)      σᴺ = ∈↑ᴺ v σᴺ

Tm↑ᴺ (lam {A} t) {σ = σ} σᴺ δ {a} aᴺ
  rewrite ₛ∘ᵣTm t (keepₛ σ) (keep δ) | assₛᵣᵣ σ (wk {A}) (keep δ) | idlᵣ δ
  = lamᴺ 
      (t [ σ ₛ∘ᵣ drop δ , var vz ])      
      (qᴺ (Tm↑ᴺ t (σᴺ ᴺ∘ᵣ drop δ , uᴺ (var (vz {A})) (λ ()))))      
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
      
Tm↑ᴺ (app f a) {σ = σ} σᴺ = appᴺ {f = f [ σ ]} (Tm↑ᴺ f σᴺ) (Tm↑ᴺ a σᴺ)

Tm↑ᴺ (a , b) {σ = σ} σᴺ =
  let aᴺ = Tm↑ᴺ a σᴺ; bᴺ = Tm↑ᴺ b σᴺ
  in (π₁ᴺ (a [ σ ]) (b [ σ ]) (qᴺ aᴺ) (qᴺ bᴺ) aᴺ bᴺ) ,
     (π₂ᴺ (a [ σ ]) (b [ σ ]) (qᴺ aᴺ) (qᴺ bᴺ) aᴺ bᴺ)

Tm↑ᴺ (π₁ p)       σᴺ = proj₁ (Tm↑ᴺ p σᴺ)
Tm↑ᴺ (π₂ p)       σᴺ = proj₂ (Tm↑ᴺ p σᴺ)
Tm↑ᴺ true         σᴺ = sn (λ ())
Tm↑ᴺ false        σᴺ = sn (λ ())

Tm↑ᴺ (if b t f) {σ = σ} σᴺ =
  let bᴺ = Tm↑ᴺ b σᴺ; tᴺ = Tm↑ᴺ t σᴺ; fᴺ = Tm↑ᴺ f σᴺ in
  ifᴺ (b [ σ ]) (t [ σ ]) (f [ σ ]) bᴺ (qᴺ tᴺ) (qᴺ fᴺ) tᴺ fᴺ
  
Tm↑ᴺ zero         σᴺ = sn (λ ())
Tm↑ᴺ (suc n)      σᴺ = SN-suc→ (Tm↑ᴺ n σᴺ)

Tm↑ᴺ (iter n s z) {σ = σ} σᴺ =
  let nᴺ = Tm↑ᴺ n σᴺ; sᴺ = Tm↑ᴺ s σᴺ; zᴺ = Tm↑ᴺ z σᴺ
  in iterᴺ (n [ σ ]) (s [ σ ]) (z [ σ ]) nᴺ (qᴺ (λ {x} → sᴺ {x})) (qᴺ zᴺ) sᴺ zᴺ

idₛᴺ : ∀ {Γ} → Tmsᴺ (idₛ {Γ})
idₛᴺ {∙}     = ∙
idₛᴺ {Γ , A} = (idₛᴺ ᴺ∘ᵣ wk) , uᴺ (var (vz {A})) (λ ())

norm : ∀ {Γ A}(t : Tm Γ A) → SN t
norm t = qᴺ (coe (Tmᴺ & idₛTm t ) (Tm↑ᴺ t idₛᴺ))

