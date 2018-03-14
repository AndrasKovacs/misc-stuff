{-# OPTIONS --without-K #-}

module Target where

open import Lib
open import Data.Bool

infixr 4 _⇒_ _⇒⁺_ _▶_
infixr 5 _*_

data Ty : Set where
  𝔹   : Ty
  Top  : Ty
  _*_  : Ty → Ty → Ty
  _⇒⁺_ : Ty → Ty → Ty
  _⇒_  : Ty → Ty → Ty

data Con : Set where
  ∙   : Con
  _▶_ : Con → Ty → Con

data _∈_ (A : Ty) : Con → Set where
  vz : ∀ {Γ} → A ∈ (Γ ▶ A)
  vs : ∀ {B Γ} → A ∈ Γ → A ∈ (Γ ▶ B)

data Tm Γ : Ty → Set where
  var  : ∀ {A} → A ∈ Γ → Tm Γ A
  tt   : Tm Γ Top

  true false : Tm Γ 𝔹
  if   : ∀ {A} → Tm Γ 𝔹 → Tm Γ A → Tm Γ A → Tm Γ A

  π₁   : ∀ {A B} → Tm Γ (A * B) → Tm Γ A
  π₂   : ∀ {A B} → Tm Γ (A * B) → Tm Γ B
  _,_  : ∀ {A B} → Tm Γ A → Tm Γ B → Tm Γ (A * B)

  pack : ∀ {E A B} → Tm Γ E → Tm Γ (E * A ⇒ B) → Tm Γ (A ⇒⁺ B)
  app⁺ : ∀ {A B} → Tm Γ (A ⇒⁺ B) → Tm Γ A → Tm Γ B

  lam  : ∀ {A B} → Tm (∙ ▶ A) B → Tm Γ (A ⇒ B)
  app  : ∀ {A B} → Tm Γ (A ⇒ B) → Tm Γ A → Tm Γ B


-- Embedding
--------------------------------------------------------------------------------

-- Order-preserving embedding
data OPE : Con → Con → Set where
  ∙    : OPE ∙ ∙
  drop : ∀ {A Γ Δ} → OPE Γ Δ → OPE (Γ ▶ A) Δ
  keep : ∀ {A Γ Δ} → OPE Γ Δ → OPE (Γ ▶ A) (Δ ▶ A)

-- OPE is a category
idₑ : ∀ {Γ} → OPE Γ Γ
idₑ {∙}     = ∙
idₑ {Γ ▶ A} = keep (idₑ {Γ})

wk : ∀ {A Γ} → OPE (Γ ▶ A) Γ
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

-- (A ∈_) : PSh OPE
∈ₑ : ∀ {A Γ Δ} → OPE Γ Δ → A ∈ Δ → A ∈ Γ
∈ₑ ∙        v      = v
∈ₑ (drop σ) v      = vs (∈ₑ σ v)
∈ₑ (keep σ) vz     = vz
∈ₑ (keep σ) (vs v) = vs (∈ₑ σ v)

∈-idₑ : ∀ {A Γ}(v : A ∈ Γ) → ∈ₑ idₑ v ≡ v
∈-idₑ vz     = refl
∈-idₑ (vs v) = vs & ∈-idₑ v

∈-∘ₑ : ∀ {A Γ Δ Σ}(σ : OPE Δ Σ)(δ : OPE Γ Δ)(v : A ∈ Σ) → ∈ₑ (σ ∘ₑ δ) v ≡ ∈ₑ δ (∈ₑ σ v)
∈-∘ₑ ∙        ∙        v      = refl
∈-∘ₑ σ        (drop δ) v      = vs & ∈-∘ₑ σ δ v
∈-∘ₑ (drop σ) (keep δ) v      = vs & ∈-∘ₑ σ δ v
∈-∘ₑ (keep σ) (keep δ) vz     = refl
∈-∘ₑ (keep σ) (keep δ) (vs v) = vs & ∈-∘ₑ σ δ v

-- (Tm _ A) : PSh OPE
Tmₑ : ∀ {A Γ Δ} → OPE Γ Δ → Tm Δ A → Tm Γ A
Tmₑ σ tt         = tt
Tmₑ σ (t , u)    = Tmₑ σ t , Tmₑ σ u
Tmₑ σ (π₁ t)     = π₁ (Tmₑ σ t)
Tmₑ σ (π₂ t)     = π₂ (Tmₑ σ t)
Tmₑ σ (pack e t) = pack (Tmₑ σ e) (Tmₑ σ t)
Tmₑ σ (app⁺ t u) = app⁺ (Tmₑ σ t) (Tmₑ σ u)
Tmₑ σ (if t u v) = if (Tmₑ σ t) (Tmₑ σ u) (Tmₑ σ v)
Tmₑ σ false      = false
Tmₑ σ true       = true
Tmₑ σ (var v)    = var (∈ₑ σ v)
Tmₑ σ (lam t)    = lam t
Tmₑ σ (app f a)  = app (Tmₑ σ f) (Tmₑ σ a)

Tm-idₑ : ∀ {A Γ}(t : Tm Γ A) → Tmₑ idₑ t ≡ t
Tm-idₑ tt         = refl
Tm-idₑ (t , u)    = _,_ & Tm-idₑ t ⊗ Tm-idₑ u
Tm-idₑ (π₁ t)     = π₁ & Tm-idₑ t
Tm-idₑ (π₂ t)     = π₂ & Tm-idₑ t
Tm-idₑ (pack e t) = pack & Tm-idₑ e ⊗ Tm-idₑ t
Tm-idₑ (app⁺ t u) = app⁺ & Tm-idₑ t ⊗ Tm-idₑ u
Tm-idₑ (if t u v) = if & Tm-idₑ t ⊗ Tm-idₑ u ⊗ Tm-idₑ v
Tm-idₑ false      = refl
Tm-idₑ true       = refl
Tm-idₑ (var v)    = var & ∈-idₑ v
Tm-idₑ (lam t)    = refl
Tm-idₑ (app f a)  = app & Tm-idₑ f ⊗ Tm-idₑ a

Tm-∘ₑ : ∀ {A Γ Δ Σ}(σ : OPE Δ Σ)(δ : OPE Γ Δ)(t : Tm Σ A) → Tmₑ (σ ∘ₑ δ) t ≡ Tmₑ δ (Tmₑ σ t)
Tm-∘ₑ σ δ tt         = refl
Tm-∘ₑ σ δ (t , u)    = _,_ & Tm-∘ₑ σ δ t ⊗ Tm-∘ₑ σ δ u
Tm-∘ₑ σ δ (π₁ t)     = π₁ & Tm-∘ₑ σ δ t
Tm-∘ₑ σ δ (π₂ t)     = π₂ & Tm-∘ₑ σ δ t
Tm-∘ₑ σ δ (pack e t) = pack & Tm-∘ₑ σ δ e ⊗ Tm-∘ₑ σ δ t
Tm-∘ₑ σ δ (app⁺ t u) = app⁺ & Tm-∘ₑ σ δ t ⊗ Tm-∘ₑ σ δ u
Tm-∘ₑ Σ δ (if t u v) = if & Tm-∘ₑ Σ δ t ⊗ Tm-∘ₑ Σ δ u ⊗ Tm-∘ₑ Σ δ v
Tm-∘ₑ Σ δ false      = refl
Tm-∘ₑ Σ δ true       = refl
Tm-∘ₑ σ δ (var v)    = var & ∈-∘ₑ σ δ v
Tm-∘ₑ σ δ (lam t)    = refl
Tm-∘ₑ σ δ (app f a)  = app & Tm-∘ₑ σ δ f ⊗ Tm-∘ₑ σ δ a

-- Theory of substitution & embedding
--------------------------------------------------------------------------------

infixr 6 _ₑ∘ₛ_ _ₛ∘ₑ_ _∘ₛ_

data Sub (Γ : Con) : Con → Set where
  ∙   : Sub Γ ∙
  _,_ : ∀ {A : Ty}{Δ : Con} → Sub Γ Δ → Tm Γ A → Sub Γ (Δ ▶ A)

_ₛ∘ₑ_ : ∀ {Γ Δ Σ} → Sub Δ Σ → OPE Γ Δ → Sub Γ Σ
∙       ₛ∘ₑ δ = ∙
(σ , t) ₛ∘ₑ δ = σ ₛ∘ₑ δ , Tmₑ δ t

_ₑ∘ₛ_ : ∀ {Γ Δ Σ} → OPE Δ Σ → Sub Γ Δ → Sub Γ Σ
∙      ₑ∘ₛ δ       = δ
drop σ ₑ∘ₛ (δ , t) = σ ₑ∘ₛ δ
keep σ ₑ∘ₛ (δ , t) = σ ₑ∘ₛ δ , t

dropₛ : ∀ {A Γ Δ} → Sub Γ Δ → Sub (Γ ▶ A) Δ
dropₛ σ = σ ₛ∘ₑ wk

keepₛ : ∀ {A Γ Δ} → Sub Γ Δ → Sub (Γ ▶ A) (Δ ▶ A)
keepₛ σ = dropₛ σ , var vz

⌜_⌝ᵒᵖᵉ : ∀ {Γ Δ} → OPE Γ Δ → Sub Γ Δ
⌜ ∙      ⌝ᵒᵖᵉ = ∙
⌜ drop σ ⌝ᵒᵖᵉ = dropₛ ⌜ σ ⌝ᵒᵖᵉ
⌜ keep σ ⌝ᵒᵖᵉ = keepₛ ⌜ σ ⌝ᵒᵖᵉ

∈ₛ : ∀ {A Γ Δ} → Sub Γ Δ → A ∈ Δ → Tm Γ A
∈ₛ (σ , t) vz     = t
∈ₛ (σ  , t)(vs v) = ∈ₛ σ v

Tmₛ : ∀ {A Γ Δ} → Sub Γ Δ → Tm Δ A → Tm Γ A
Tmₛ σ tt         = tt
Tmₛ σ (t , u)    = Tmₛ σ t , Tmₛ σ u
Tmₛ σ (π₁ t)     = π₁ (Tmₛ σ t)
Tmₛ σ (π₂ t)     = π₂ (Tmₛ σ t)
Tmₛ σ (pack e t) = pack (Tmₛ σ e) (Tmₛ σ t)
Tmₛ σ (app⁺ t u) = app⁺ (Tmₛ σ t) (Tmₛ σ u)
Tmₛ σ (if t u v) = if (Tmₛ σ t) (Tmₛ σ u) (Tmₛ σ v)
Tmₛ σ false      = false
Tmₛ σ true       = true
Tmₛ σ (var v)    = ∈ₛ σ v
Tmₛ σ (lam t)    = lam t
Tmₛ σ (app f a)  = app (Tmₛ σ f) (Tmₛ σ a)

idₛ : ∀ {Γ} → Sub Γ Γ
idₛ {∙}     = ∙
idₛ {Γ ▶ A} = (idₛ {Γ} ₛ∘ₑ drop idₑ) , var vz

_∘ₛ_ : ∀ {Γ Δ Σ} → Sub Δ Σ → Sub Γ Δ → Sub Γ Σ
∙       ∘ₛ δ = ∙
(σ , t) ∘ₛ δ = σ ∘ₛ δ , Tmₛ δ t

assₛₑₑ :
  ∀ {Γ Δ Σ Ξ}(σ : Sub Σ Ξ)(δ : OPE Δ Σ)(ν : OPE Γ Δ)
  → (σ ₛ∘ₑ δ) ₛ∘ₑ ν ≡ σ ₛ∘ₑ (δ ∘ₑ ν)
assₛₑₑ ∙       δ ν = refl
assₛₑₑ (σ , t) δ ν = _,_ & assₛₑₑ σ δ ν ⊗ (Tm-∘ₑ δ ν t ⁻¹)

assₑₛₑ :
  ∀ {Γ Δ Σ Ξ}(σ : OPE Σ Ξ)(δ : Sub Δ Σ)(ν : OPE Γ Δ)
  → (σ ₑ∘ₛ δ) ₛ∘ₑ ν ≡ σ ₑ∘ₛ (δ ₛ∘ₑ ν)
assₑₛₑ ∙        δ       ν = refl
assₑₛₑ (drop σ) (δ , t) ν = assₑₛₑ σ δ ν
assₑₛₑ (keep σ) (δ , t) ν = (_, Tmₑ ν t) & assₑₛₑ σ δ ν

idlₑₛ : ∀ {Γ Δ}(σ : Sub Γ Δ) → idₑ ₑ∘ₛ σ ≡ σ
idlₑₛ ∙       = refl
idlₑₛ (σ , t) = (_, t) & idlₑₛ σ

idlₛₑ : ∀ {Γ Δ}(σ : OPE Γ Δ) → idₛ ₛ∘ₑ σ ≡ ⌜ σ ⌝ᵒᵖᵉ
idlₛₑ ∙        = refl
idlₛₑ (drop σ) =
      ((idₛ ₛ∘ₑ_) ∘ drop) & idrₑ σ ⁻¹
    ◾ assₛₑₑ idₛ σ wk ⁻¹
    ◾ dropₛ & idlₛₑ σ
idlₛₑ (keep σ) =
  (_, var vz) &
      (assₛₑₑ idₛ wk (keep σ)
    ◾ ((idₛ ₛ∘ₑ_) ∘ drop) & (idlₑ σ ◾ idrₑ σ ⁻¹)
    ◾ assₛₑₑ idₛ σ wk ⁻¹
    ◾ (_ₛ∘ₑ wk) & idlₛₑ σ )

idrₑₛ : ∀ {Γ Δ}(σ : OPE Γ Δ) → σ ₑ∘ₛ idₛ ≡ ⌜ σ ⌝ᵒᵖᵉ
idrₑₛ ∙        = refl
idrₑₛ (drop σ) = assₑₛₑ σ idₛ wk ⁻¹ ◾ dropₛ & idrₑₛ σ
idrₑₛ (keep σ) = (_, var vz) & (assₑₛₑ σ idₛ wk ⁻¹ ◾ (_ₛ∘ₑ wk) & idrₑₛ σ)

∈-ₑ∘ₛ : ∀ {A Γ Δ Σ}(σ : OPE Δ Σ)(δ : Sub Γ Δ)(v : A ∈ Σ) → ∈ₛ (σ ₑ∘ₛ δ) v ≡ ∈ₛ δ (∈ₑ σ v)
∈-ₑ∘ₛ ∙        δ       v      = refl
∈-ₑ∘ₛ (drop σ) (δ , t) v      = ∈-ₑ∘ₛ σ δ v
∈-ₑ∘ₛ (keep σ) (δ , t) vz     = refl
∈-ₑ∘ₛ (keep σ) (δ , t) (vs v) = ∈-ₑ∘ₛ σ δ v

Tm-ₑ∘ₛ : ∀ {A Γ Δ Σ}(σ : OPE Δ Σ)(δ : Sub Γ Δ)(t : Tm Σ A) → Tmₛ (σ ₑ∘ₛ δ) t ≡ Tmₛ δ (Tmₑ σ t)
Tm-ₑ∘ₛ σ δ tt         = refl
Tm-ₑ∘ₛ σ δ (t , u)    = _,_ & Tm-ₑ∘ₛ σ δ t ⊗ Tm-ₑ∘ₛ σ δ u
Tm-ₑ∘ₛ σ δ (π₁ t)     = π₁ & Tm-ₑ∘ₛ σ δ t
Tm-ₑ∘ₛ σ δ (π₂ t)     = π₂ & Tm-ₑ∘ₛ σ δ t
Tm-ₑ∘ₛ σ δ (pack e t) = pack & Tm-ₑ∘ₛ σ δ e ⊗ Tm-ₑ∘ₛ σ δ t
Tm-ₑ∘ₛ σ δ (app⁺ t u) = app⁺ & Tm-ₑ∘ₛ σ δ t ⊗ Tm-ₑ∘ₛ σ δ u
Tm-ₑ∘ₛ σ δ (if t u v) = if & Tm-ₑ∘ₛ σ δ t ⊗ Tm-ₑ∘ₛ σ δ u ⊗ Tm-ₑ∘ₛ σ δ v
Tm-ₑ∘ₛ σ δ false      = refl
Tm-ₑ∘ₛ σ δ true       = refl
Tm-ₑ∘ₛ σ δ (var v)    = ∈-ₑ∘ₛ σ δ v
Tm-ₑ∘ₛ σ δ (lam t)    = refl
Tm-ₑ∘ₛ σ δ (app f a)  = app & Tm-ₑ∘ₛ σ δ f ⊗ Tm-ₑ∘ₛ σ δ a

∈-ₛ∘ₑ : ∀ {A Γ Δ Σ}(σ : Sub Δ Σ)(δ : OPE Γ Δ)(v : A ∈ Σ) → ∈ₛ (σ ₛ∘ₑ δ) v ≡ Tmₑ δ (∈ₛ σ v)
∈-ₛ∘ₑ (σ , _) δ vz     = refl
∈-ₛ∘ₑ (σ , _) δ (vs v) = ∈-ₛ∘ₑ σ δ v

Tm-ₛ∘ₑ : ∀ {A Γ Δ Σ}(σ : Sub Δ Σ)(δ : OPE Γ Δ)(t : Tm Σ A) → Tmₛ (σ ₛ∘ₑ δ) t ≡ Tmₑ δ (Tmₛ σ t)
Tm-ₛ∘ₑ σ δ tt         = refl
Tm-ₛ∘ₑ σ δ (t , u)    = _,_ & Tm-ₛ∘ₑ σ δ t ⊗ Tm-ₛ∘ₑ σ δ u
Tm-ₛ∘ₑ σ δ (π₁ t)     = π₁ & Tm-ₛ∘ₑ σ δ t
Tm-ₛ∘ₑ σ δ (π₂ t)     = π₂ & Tm-ₛ∘ₑ σ δ t
Tm-ₛ∘ₑ σ δ (pack e t) = pack & Tm-ₛ∘ₑ σ δ e ⊗ Tm-ₛ∘ₑ σ δ t
Tm-ₛ∘ₑ σ δ (app⁺ t u) = app⁺ & Tm-ₛ∘ₑ σ δ t ⊗ Tm-ₛ∘ₑ σ δ u
Tm-ₛ∘ₑ σ δ (if t u v) = if & Tm-ₛ∘ₑ σ δ t ⊗ Tm-ₛ∘ₑ σ δ u ⊗ Tm-ₛ∘ₑ σ δ v
Tm-ₛ∘ₑ σ δ false      = refl
Tm-ₛ∘ₑ σ δ true       = refl
Tm-ₛ∘ₑ σ δ (var v)    = ∈-ₛ∘ₑ σ δ v
Tm-ₛ∘ₑ σ δ (lam t)    = refl
Tm-ₛ∘ₑ σ δ (app f a)  = app & Tm-ₛ∘ₑ σ δ f ⊗ Tm-ₛ∘ₑ σ δ a

assₛₑₛ :
  ∀ {Γ Δ Σ Ξ}(σ : Sub Σ Ξ)(δ : OPE Δ Σ)(ν : Sub Γ Δ)
  → (σ ₛ∘ₑ δ) ∘ₛ ν ≡ σ ∘ₛ (δ ₑ∘ₛ ν)
assₛₑₛ ∙       δ ν = refl
assₛₑₛ (σ , t) δ ν = _,_ & assₛₑₛ σ δ ν ⊗ (Tm-ₑ∘ₛ δ ν t ⁻¹)

assₛₛₑ :
  ∀ {Γ Δ Σ Ξ}(σ : Sub Σ Ξ)(δ : Sub Δ Σ)(ν : OPE Γ Δ)
  → (σ ∘ₛ δ) ₛ∘ₑ ν ≡ σ ∘ₛ (δ ₛ∘ₑ ν)
assₛₛₑ ∙       δ ν = refl
assₛₛₑ (σ , t) δ ν = _,_ & assₛₛₑ σ δ ν ⊗ (Tm-ₛ∘ₑ δ ν t ⁻¹)

∈-idₛ : ∀ {A Γ}(v : A ∈ Γ) → ∈ₛ idₛ v ≡ var v
∈-idₛ vz     = refl
∈-idₛ (vs v) = ∈-ₛ∘ₑ idₛ wk v ◾ Tmₑ wk & ∈-idₛ v ◾ (var ∘ vs) & ∈-idₑ v

∈-∘ₛ : ∀ {A Γ Δ Σ}(σ : Sub Δ Σ)(δ : Sub Γ Δ)(v : A ∈ Σ) → ∈ₛ (σ ∘ₛ δ) v ≡ Tmₛ δ (∈ₛ σ v)
∈-∘ₛ (σ , _) δ vz     = refl
∈-∘ₛ (σ , _) δ (vs v) = ∈-∘ₛ σ δ v

Tm-idₛ : ∀ {A Γ}(t : Tm Γ A) → Tmₛ idₛ t ≡ t
Tm-idₛ tt         = refl
Tm-idₛ (t , u)    = _,_ & Tm-idₛ t ⊗ Tm-idₛ u
Tm-idₛ (π₁ t)     = π₁ & Tm-idₛ t
Tm-idₛ (π₂ t)     = π₂ & Tm-idₛ t
Tm-idₛ (pack e t) = pack & Tm-idₛ e ⊗ Tm-idₛ t
Tm-idₛ (app⁺ t u) = app⁺ & Tm-idₛ t ⊗ Tm-idₛ u
Tm-idₛ (if t u v) = if & Tm-idₛ t ⊗ Tm-idₛ u ⊗ Tm-idₛ v
Tm-idₛ false      = refl
Tm-idₛ true       = refl
Tm-idₛ (var v)    = ∈-idₛ v
Tm-idₛ (lam t)    = refl
Tm-idₛ (app f a)  = app & Tm-idₛ f ⊗ Tm-idₛ a

Tm-∘ₛ : ∀ {A Γ Δ Σ}(σ : Sub Δ Σ)(δ : Sub Γ Δ)(t : Tm Σ A) → Tmₛ (σ ∘ₛ δ) t ≡ Tmₛ δ (Tmₛ σ t)
Tm-∘ₛ σ δ tt         = refl
Tm-∘ₛ σ δ (t , u)    = _,_ & Tm-∘ₛ σ δ t ⊗ Tm-∘ₛ σ δ u
Tm-∘ₛ σ δ (π₁ t)     = π₁ & Tm-∘ₛ σ δ t
Tm-∘ₛ σ δ (π₂ t)     = π₂ & Tm-∘ₛ σ δ t
Tm-∘ₛ σ δ (pack e t) = pack & Tm-∘ₛ σ δ e ⊗ Tm-∘ₛ σ δ t
Tm-∘ₛ σ δ (app⁺ t u) = app⁺ & Tm-∘ₛ σ δ t ⊗ Tm-∘ₛ σ δ u
Tm-∘ₛ σ δ (if t u v) = if & Tm-∘ₛ σ δ t ⊗ Tm-∘ₛ σ δ u ⊗ Tm-∘ₛ σ δ v
Tm-∘ₛ σ δ false      = refl
Tm-∘ₛ σ δ true       = refl
Tm-∘ₛ σ δ (var v)    = ∈-∘ₛ σ δ v
Tm-∘ₛ σ δ (lam t)    = refl
Tm-∘ₛ σ δ (app f a)  = app & Tm-∘ₛ σ δ f ⊗ Tm-∘ₛ σ δ a

idrₛ : ∀ {Γ Δ}(σ : Sub Γ Δ) → σ ∘ₛ idₛ ≡ σ
idrₛ ∙       = refl
idrₛ (σ , t) = _,_ & idrₛ σ ⊗ Tm-idₛ t

idlₛ : ∀ {Γ Δ}(σ : Sub Γ Δ) → idₛ ∘ₛ σ ≡ σ
idlₛ ∙       = refl
idlₛ (σ , t) = (_, t) & (assₛₑₛ idₛ wk (σ , t) ◾ (idₛ ∘ₛ_) & idlₑₛ σ ◾ idlₛ σ)

assₛ :
  ∀ {Γ Δ Σ Ξ}(σ : Sub Σ Ξ)(δ : Sub Δ Σ)(ν : Sub Γ Δ)
  → (σ ∘ₛ δ) ∘ₛ ν ≡ σ ∘ₛ (δ ∘ₛ ν)
assₛ ∙       δ ν = refl
assₛ (σ , t) δ ν = _,_ & assₛ σ δ ν ⊗ (Tm-∘ₛ δ ν t ⁻¹)

⌜idₑ⌝ : ∀ {Γ} → ⌜ idₑ {Γ} ⌝ᵒᵖᵉ ≡ idₛ
⌜idₑ⌝ {∙}     = refl
⌜idₑ⌝ {Γ ▶ A} = (λ x → (x ₛ∘ₑ wk) , var vz) & ⌜idₑ⌝

⌜∈ₑ⌝ : ∀ {Γ Δ A}(σ : OPE Γ Δ)(x : A ∈ Δ) → var (∈ₑ σ x) ≡ ∈ₛ ⌜ σ ⌝ᵒᵖᵉ x
⌜∈ₑ⌝ ∙ ()
⌜∈ₑ⌝ (drop σ) x      = (var ∘ vs) & (∈-idₑ _ ⁻¹) ◾ Tmₑ wk & ⌜∈ₑ⌝ σ x ◾ ∈-ₛ∘ₑ ⌜ σ ⌝ᵒᵖᵉ wk x ⁻¹
⌜∈ₑ⌝ (keep σ) vz     = refl
⌜∈ₑ⌝ (keep σ) (vs x) = (var ∘ vs) & (∈-idₑ _ ⁻¹) ◾ Tmₑ wk & ⌜∈ₑ⌝ σ x ◾ ∈-ₛ∘ₑ ⌜ σ ⌝ᵒᵖᵉ wk x ⁻¹

⌜Tmₑ⌝ : ∀ {Γ Δ A}(σ : OPE Γ Δ)(t : Tm Δ A) → Tmₑ σ t ≡ Tmₛ ⌜ σ ⌝ᵒᵖᵉ t
⌜Tmₑ⌝ σ (var x) = ⌜∈ₑ⌝ σ x
⌜Tmₑ⌝ σ tt = refl
⌜Tmₑ⌝ σ true = refl
⌜Tmₑ⌝ σ false = refl
⌜Tmₑ⌝ σ (if t t₁ t₂) = if & ⌜Tmₑ⌝ σ t ⊗ ⌜Tmₑ⌝ σ t₁ ⊗ ⌜Tmₑ⌝ σ t₂
⌜Tmₑ⌝ σ (π₁ t) = π₁ & ⌜Tmₑ⌝ σ t
⌜Tmₑ⌝ σ (π₂ t) = π₂ & ⌜Tmₑ⌝ σ t
⌜Tmₑ⌝ σ (t , t₁) = _,_ & ⌜Tmₑ⌝ σ t ⊗ ⌜Tmₑ⌝ σ t₁
⌜Tmₑ⌝ σ (pack t t₁) = pack & ⌜Tmₑ⌝ σ t ⊗ ⌜Tmₑ⌝ σ t₁
⌜Tmₑ⌝ σ (app⁺ t t₁) = app⁺ & ⌜Tmₑ⌝ σ t ⊗ ⌜Tmₑ⌝ σ t₁
⌜Tmₑ⌝ σ (lam t) = refl
⌜Tmₑ⌝ σ (app t t₁) = app & ⌜Tmₑ⌝ σ t ⊗ ⌜Tmₑ⌝ σ t₁


-- Conversion
--------------------------------------------------------------------------------

data _~_ {Γ} : ∀ {A} → Tm Γ A → Tm Γ A → Set where
  β     : ∀ {A B}(t : Tm (∙ ▶ A) B) (t' : Tm Γ A) → app (lam t) t' ~ Tmₛ (∙ , t') t
  η     : ∀ {A B}{t t' : Tm Γ (A ⇒ B)} → app (Tmₑ wk t) (var vz) ~ app (Tmₑ wk t') (var vz) → t ~ t'
  lam   : ∀ {A B}{t t' : Tm (∙ ▶ A) B}  → t ~ t' →  lam {Γ} t ~ lam t'
  app   : ∀ {A B}{t t' : Tm Γ (A ⇒ B)}{u u'} → t ~ t' → u ~ u' → app t u ~ app t' u'
  true  : ∀ {A}{t u : Tm Γ A} → if true  t u ~ t
  false : ∀ {A}{t u : Tm Γ A} → if false t u ~ u
  if    : ∀ {A}{t t' : Tm Γ 𝔹}{u u' v v' : Tm Γ A} → t ~ t' → u ~ u' → v ~ v' → if t u v ~ if t' u' v'

  π₁    : ∀ {A B}{t t' : Tm Γ (A * B)} → t ~ t' → π₁ t ~ π₁ t'
  π₂    : ∀ {A B}{t t' : Tm Γ (A * B)} → t ~ t' → π₂ t ~ π₂ t'
  _,_   : ∀ {A B}{t t' : Tm Γ A}{u u' : Tm Γ B} → t ~ t' → u ~ u' → (t , u) ~ (t' , u')
  π₁β   : ∀ {A B} t u → π₁ {Γ}{A}{B} (t , u) ~ t
  π₂β   : ∀ {A B} t u → π₂ {Γ}{A}{B} (t , u) ~ u
  ,η    : ∀ {A B}(t : Tm Γ (A * B)) → (π₁ t , π₂ t) ~ t

  ttη   : ∀ {t} → t ~ tt

  pack  : ∀ {E A B}{e e' : Tm Γ E}{t t' : Tm Γ (E * A ⇒ B)} → e ~ e' → t ~ t' → pack e t ~ pack e' t'
  app⁺  : ∀ {A B}{t t' : Tm Γ (A ⇒⁺ B)}{u u'} → t ~ t' → u ~ u' → app⁺ t u ~ app⁺ t' u'
  βᶜ    : ∀ {A B E} e t t' → app⁺ (pack {Γ}{A}{B}{E} e t) t' ~ app t (e , t')
  ηᶜ    : ∀ {A B}{t t' : Tm Γ (A ⇒⁺ B)} → app⁺ (Tmₑ wk t) (var vz) ~ app⁺ (Tmₑ wk t') (var vz) → t ~ t'

  ~refl : ∀ {A}{t : Tm Γ A} → t ~ t
  _~⁻¹  : ∀ {A}{t t' : Tm Γ A} → t ~ t' → t' ~ t
  _~◾_  : ∀ {A}{t t' t'' : Tm Γ A} → t ~ t' → t' ~ t'' → t ~ t''

infixr 4 _~◾_
infix 6 _~⁻¹

≡~ : ∀ {Γ A}{t t' : Tm Γ A} → t ≡ t' → t ~ t'
≡~ refl = ~refl

~ₑ : ∀ {Γ Δ A}{t t' : Tm Γ A}(σ : OPE Δ Γ) → t ~ t' → Tmₑ σ t ~ Tmₑ σ t'
~ₑ σ (π₁β t u) = π₁β (Tmₑ σ t) (Tmₑ σ u)
~ₑ σ (π₂β t u) = π₂β (Tmₑ σ t) (Tmₑ σ u)
~ₑ σ (,η t) = ,η (Tmₑ σ t)
~ₑ σ ttη = ttη
~ₑ σ (βᶜ e t u) = βᶜ (Tmₑ σ e) (Tmₑ σ t) (Tmₑ σ u)
~ₑ {t = t} {t'} σ (ηᶜ {A} {B} p) with ~ₑ (keep σ) p
... | hyp rewrite
      Tm-∘ₑ (wk{A}) (keep σ) t ⁻¹
    | Tm-∘ₑ (wk{A}) (keep σ) t' ⁻¹
    | idlₑ σ | idrₑ σ ⁻¹ | Tm-∘ₑ σ (wk{A}) t
    | Tm-∘ₑ σ (wk{A}) t' = coe ((λ x → Tmₑ x t ~ Tmₑ x t') & (idrₑ σ ⁻¹)) (ηᶜ hyp)
~ₑ σ (π₁ t)     = π₁ (~ₑ σ t)
~ₑ σ (π₂ t)     = π₂ (~ₑ σ t)
~ₑ σ (t , u)    = ~ₑ σ t , ~ₑ σ u
~ₑ σ (pack e t) = pack (~ₑ σ e) (~ₑ σ t)
~ₑ σ (app⁺ t u) = app⁺ (~ₑ σ t) (~ₑ σ u)
~ₑ {t = t} {t'} σ (η {A} {B} p) with ~ₑ (keep σ) p
... | hyp rewrite
      Tm-∘ₑ (wk{A}) (keep σ) t ⁻¹
    | Tm-∘ₑ (wk{A}) (keep σ) t' ⁻¹
    | idlₑ σ | idrₑ σ ⁻¹ | Tm-∘ₑ σ (wk{A}) t
    | Tm-∘ₑ σ (wk{A}) t' = coe ((λ x → Tmₑ x t ~ Tmₑ x t') & (idrₑ σ ⁻¹)) (η hyp)
~ₑ σ (β t t') rewrite Tm-ₛ∘ₑ (∙ , t') σ t ⁻¹ = β t (Tmₑ σ t')

~ₑ σ (lam t~t')       = lam t~t'
~ₑ σ (app t~t' x~x')  = app (~ₑ σ t~t') (~ₑ σ x~x')
~ₑ σ ~refl            = ~refl
~ₑ σ (t~t' ~⁻¹)       = ~ₑ σ t~t' ~⁻¹
~ₑ σ (t~t' ~◾ t'~t'') = ~ₑ σ t~t' ~◾ ~ₑ σ t'~t''
~ₑ σ true             = true
~ₑ σ false            = false
~ₑ σ (if t u v)       = if (~ₑ σ t) (~ₑ σ u) (~ₑ σ v)

infix 3 _~ₛ_
data _~ₛ_ {Γ} : ∀ {Δ} → Sub Γ Δ → Sub Γ Δ → Set where
  ∙   : ∙ ~ₛ ∙
  _,_ : ∀ {Δ A}{σ σ' : Sub Γ Δ}{t t' : Tm Γ A} → σ ~ₛ σ' → t ~ t' → (σ , t) ~ₛ (σ' , t')

infixr 4 _~ₛ◾_
_~ₛ◾_ : ∀ {Γ Δ}{σ δ ν : Sub Γ Δ} → σ ~ₛ δ → δ ~ₛ ν → σ ~ₛ ν
∙       ~ₛ◾ ∙        = ∙
(p , t) ~ₛ◾ (q , t') = (p ~ₛ◾ q) , (t ~◾ t')

_~ₛ⁻¹ : ∀ {Γ Δ}{σ δ : Sub Γ Δ} → σ ~ₛ δ → δ ~ₛ σ
∙       ~ₛ⁻¹ = ∙
(p , x) ~ₛ⁻¹ = (p ~ₛ⁻¹) , (x ~⁻¹)

~ₛ∘ₑ : ∀ {Γ Δ Σ}{σ σ' : Sub Δ Σ} → σ ~ₛ σ' → (δ : OPE Γ Δ) → (σ ₛ∘ₑ δ) ~ₛ (σ' ₛ∘ₑ δ)
~ₛ∘ₑ ∙       δ = ∙
~ₛ∘ₑ (p , t) δ = ~ₛ∘ₑ p δ , ~ₑ δ t

∈ₛ~x : ∀ {Γ Δ A}{σ σ' : Sub Γ Δ} → σ ~ₛ σ' → (x : A ∈ Δ) → ∈ₛ σ x ~ ∈ₛ σ' x
∈ₛ~x (p , t) vz = t
∈ₛ~x (p , t) (vs x) = ∈ₛ~x p x

Tmₛ~t : ∀ {Γ Δ A}{σ σ' : Sub Γ Δ} → σ ~ₛ σ' → (t : Tm Δ A) → Tmₛ σ t ~ Tmₛ σ' t
Tmₛ~t p (var x) = ∈ₛ~x p x
Tmₛ~t p tt = ~refl
Tmₛ~t p true = ~refl
Tmₛ~t p false = ~refl
Tmₛ~t p (if t t₁ t₂) = if (Tmₛ~t p t) (Tmₛ~t p t₁) (Tmₛ~t p t₂)
Tmₛ~t p (π₁ t) = π₁ (Tmₛ~t p t)
Tmₛ~t p (π₂ t) = π₂ (Tmₛ~t p t)
Tmₛ~t p (t , t₁) = Tmₛ~t p t , Tmₛ~t p t₁
Tmₛ~t p (pack t t₁) = pack (Tmₛ~t p t) (Tmₛ~t p t₁)
Tmₛ~t p (app⁺ t t₁) = app⁺ (Tmₛ~t p t) (Tmₛ~t p t₁)
Tmₛ~t p (lam t) = ~refl
Tmₛ~t p (app t t₁) = app (Tmₛ~t p t) (Tmₛ~t p t₁)

Tmₛσ~ : ∀ {Γ Δ A}(σ : Sub Γ Δ){t t' : Tm Δ A}  → t ~ t' → Tmₛ σ t ~ Tmₛ σ t'
Tmₛσ~ σ (β t t') = β t (Tmₛ σ t') ~◾ ≡~ (Tm-∘ₛ (∙ , t') σ t)
Tmₛσ~ σ {t} {t'} (η {A} {B} p) with Tmₛσ~ (keepₛ σ) p
... | hyp rewrite Tm-ₑ∘ₛ (wk{A}) (keepₛ σ) t ⁻¹ | Tm-ₑ∘ₛ (wk{A}) (keepₛ σ) t' ⁻¹
          | idlₑₛ (σ ₛ∘ₑ (wk{A})) | Tm-ₛ∘ₑ σ (wk{A}) t | Tm-ₛ∘ₑ σ (wk{A}) t'
          = η hyp
Tmₛσ~ σ (lam p) = lam p
Tmₛσ~ σ (app p p₁) = app (Tmₛσ~ σ p) (Tmₛσ~ σ p₁)
Tmₛσ~ σ true = true
Tmₛσ~ σ false = false
Tmₛσ~ σ (if p p₁ p₂) = if (Tmₛσ~ σ p) (Tmₛσ~ σ p₁) (Tmₛσ~ σ p₂)
Tmₛσ~ σ (π₁ p) = π₁ (Tmₛσ~ σ p)
Tmₛσ~ σ (π₂ p) = π₂ (Tmₛσ~ σ p)
Tmₛσ~ σ (p , p₁) = Tmₛσ~ σ p , Tmₛσ~ σ p₁
Tmₛσ~ σ (π₁β t u) = π₁β (Tmₛ σ t) (Tmₛ σ u)
Tmₛσ~ σ (π₂β t u) = π₂β (Tmₛ σ t) (Tmₛ σ u)
Tmₛσ~ σ (,η t) = ,η (Tmₛ σ t)
Tmₛσ~ σ ttη = ttη
Tmₛσ~ σ (pack p p₁) = pack (Tmₛσ~ σ p) (Tmₛσ~ σ p₁)
Tmₛσ~ σ (app⁺ p p₁) = app⁺ (Tmₛσ~ σ p) (Tmₛσ~ σ p₁)
Tmₛσ~ σ (βᶜ e t t') = βᶜ (Tmₛ σ e) (Tmₛ σ t) (Tmₛ σ t')
Tmₛσ~ σ {t} {t'} (ηᶜ {A} {B} p) with Tmₛσ~ (keepₛ σ) p
... | hyp rewrite Tm-ₑ∘ₛ (wk{A}) (keepₛ σ) t ⁻¹ | Tm-ₑ∘ₛ (wk{A}) (keepₛ σ) t' ⁻¹
          | idlₑₛ (σ ₛ∘ₑ (wk{A})) | Tm-ₛ∘ₑ σ (wk{A}) t | Tm-ₛ∘ₑ σ (wk{A}) t'
          = ηᶜ hyp
Tmₛσ~ σ ~refl = ~refl
Tmₛσ~ σ (p ~⁻¹) = Tmₛσ~ σ p ~⁻¹
Tmₛσ~ σ (p ~◾ p₁) = Tmₛσ~ σ p ~◾ Tmₛσ~ σ p₁

Tmₛ~~ : ∀ {Γ Δ A}{t t' : Tm Δ A}{σ σ' : Sub Γ Δ} → σ ~ₛ σ' → t ~ t' → Tmₛ σ t ~ Tmₛ σ' t'
Tmₛ~~ {t = t} {σ' = σ'} p q = Tmₛ~t p t ~◾ Tmₛσ~ σ' q

~∘ₛ~ : ∀ {Γ Δ Σ}{σ σ' : Sub Δ Σ} → σ ~ₛ σ' → {δ δ' : Sub Γ Δ} → δ ~ₛ δ' → (σ ∘ₛ δ) ~ₛ (σ' ∘ₛ δ')
~∘ₛ~ ∙       q = ∙
~∘ₛ~ (p , t) q = ~∘ₛ~ p q , Tmₛ~~ q t

~ₛrefl : ∀ {Γ Δ}(σ : Sub Γ Δ) → σ ~ₛ σ
~ₛrefl ∙       = ∙
~ₛrefl (σ , _) = ~ₛrefl _ , ~refl

≡~ₛ : ∀ {Γ Δ}{σ δ : Sub Γ Δ} → σ ≡ δ → σ ~ₛ δ
≡~ₛ refl = ~ₛrefl _

head : ∀ {Γ Δ A} → Sub Γ (Δ ▶ A) → Tm Γ A
head (σ , t) = t

tail : ∀ {Γ Δ A} → Sub Γ (Δ ▶ A) → Sub Γ Δ
tail (σ , _) = σ

dropₛ~ : ∀ {Γ Δ A}{σ σ' : Sub Γ Δ} → σ ~ₛ σ' → dropₛ {A} σ ~ₛ dropₛ σ'
dropₛ~ p = ~ₛ∘ₑ p wk

keepₛ~ : ∀ {Γ Δ A}{σ σ' : Sub Γ Δ} → σ ~ₛ σ' → keepₛ {A} σ ~ₛ keepₛ σ'
keepₛ~ p = dropₛ~ p , ~refl

Tmₑhead : ∀ {Γ Δ Σ A}(δ : OPE Σ Γ)(σ : Sub Γ (Δ ▶ A)) → Tmₑ δ (head σ) ≡ head (σ ₛ∘ₑ δ)
Tmₑhead δ (σ , x) = refl

∙ₛη : ∀ {Γ}(σ : Sub Γ ∙) → σ ≡ ∙
∙ₛη ∙ = refl

,ₛη : ∀ {Γ Δ A}(t : Sub Γ (Δ ▶ A)) → (tail t , head t) ≡ t
,ₛη (σ , t) = refl

-- -- Standard model
-- --------------------------------------------------------------------------------

-- ⟦_⟧Ty : Ty → Set
-- ⟦ Top    ⟧Ty = ⊤
-- ⟦ A * B  ⟧Ty = ⟦ A ⟧Ty × ⟦ B ⟧Ty
-- ⟦ A ⇒⁺ B ⟧Ty = ⟦ A ⟧Ty → ⟦ B ⟧Ty
-- ⟦ 𝔹      ⟧Ty = Bool
-- ⟦ A ⇒ B  ⟧Ty = ⟦ A ⟧Ty → ⟦ B ⟧Ty

-- ⟦_⟧Con : Con → Set
-- ⟦ ∙     ⟧Con = ⊤
-- ⟦ Γ ▶ A ⟧Con = ⟦ Γ ⟧Con × ⟦ A ⟧Ty

-- ⟦_⟧Tm : ∀ {Γ A} → Tm Γ A → ⟦ Γ ⟧Con → ⟦ A ⟧Ty
-- ⟦ tt         ⟧Tm γ = tt
-- ⟦ π₁ t       ⟧Tm γ = ₁ (⟦ t ⟧Tm γ)
-- ⟦ π₂ t       ⟧Tm γ = ₂ (⟦ t ⟧Tm γ)
-- ⟦ t , u      ⟧Tm γ = ⟦ t ⟧Tm γ , ⟦ u ⟧Tm γ
-- ⟦ pack e t   ⟧Tm γ = λ α → ⟦ t ⟧Tm γ (⟦ e ⟧Tm γ , α)
-- ⟦ app⁺ t u   ⟧Tm γ = ⟦ t ⟧Tm γ (⟦ u ⟧Tm γ)
-- ⟦ var vz     ⟧Tm γ = ₂ γ
-- ⟦ var (vs x) ⟧Tm γ = ⟦ var x ⟧Tm (₁ γ)
-- ⟦ lam t      ⟧Tm γ = λ α → ⟦ t ⟧Tm (tt , α)
-- ⟦ app t u    ⟧Tm γ = ⟦ t ⟧Tm γ (⟦ u ⟧Tm γ)
-- ⟦ true       ⟧Tm γ = true
-- ⟦ false      ⟧Tm γ = false
-- ⟦ if t u v   ⟧Tm γ = if ⟦ t ⟧Tm γ then ⟦ u ⟧Tm γ else ⟦ v ⟧Tm γ

-- ⟦_⟧OPE : ∀ {Γ Δ} → OPE Γ Δ → ⟦ Γ ⟧Con → ⟦ Δ ⟧Con
-- ⟦ ∙      ⟧OPE γ = tt
-- ⟦ drop σ ⟧OPE γ = ⟦ σ ⟧OPE (₁ γ)
-- ⟦ keep σ ⟧OPE γ = ⟦ σ ⟧OPE (₁ γ) , ₂ γ

-- ⟦_⟧Sub : ∀ {Γ Δ} → Sub Γ Δ → ⟦ Γ ⟧Con → ⟦ Δ ⟧Con
-- ⟦ ∙     ⟧Sub γ = tt
-- ⟦ σ , t ⟧Sub γ = ⟦ σ ⟧Sub γ , ⟦ t ⟧Tm γ

-- ⟦idₑ⟧ : ∀ {Γ} → ⟦ idₑ {Γ} ⟧OPE ≡ id
-- ⟦idₑ⟧ {∙}     = refl
-- ⟦idₑ⟧ {Γ ▶ A} rewrite ⟦idₑ⟧ {Γ} = refl

-- ⟦∈ₑ⟧ : ∀ {Γ Δ A}(σ : OPE Γ Δ)(x : A ∈ Δ) → ⟦ var (∈ₑ σ x) ⟧Tm ≡ ⟦ var x ⟧Tm ∘ ⟦ σ ⟧OPE
-- ⟦∈ₑ⟧ ∙ ()
-- ⟦∈ₑ⟧ (drop σ) x rewrite ⟦∈ₑ⟧ σ x = refl
-- ⟦∈ₑ⟧ (keep σ) vz = refl
-- ⟦∈ₑ⟧ (keep σ) (vs x) rewrite ⟦∈ₑ⟧ σ x = refl

-- ⟦Tmₑ⟧ : ∀ {Γ Δ A}(σ : OPE Γ Δ)(t : Tm Δ A) → ⟦ Tmₑ σ t ⟧Tm ≡ ⟦ t ⟧Tm ∘ ⟦ σ ⟧OPE
-- ⟦Tmₑ⟧ σ tt       = refl
-- ⟦Tmₑ⟧ σ (π₁ t)     rewrite ⟦Tmₑ⟧ σ t = refl
-- ⟦Tmₑ⟧ σ (π₂ t)     rewrite ⟦Tmₑ⟧ σ t = refl
-- ⟦Tmₑ⟧ σ (t , u)    rewrite ⟦Tmₑ⟧ σ t | ⟦Tmₑ⟧ σ u = refl
-- ⟦Tmₑ⟧ σ (pack e t) rewrite ⟦Tmₑ⟧ σ e | ⟦Tmₑ⟧ σ t = refl
-- ⟦Tmₑ⟧ σ (app⁺ t u) rewrite ⟦Tmₑ⟧ σ t | ⟦Tmₑ⟧ σ u = refl
-- ⟦Tmₑ⟧ σ (var x) = ⟦∈ₑ⟧ σ x
-- ⟦Tmₑ⟧ σ (lam t) = refl
-- ⟦Tmₑ⟧ σ (app t u) rewrite ⟦Tmₑ⟧ σ t | ⟦Tmₑ⟧ σ u = refl
-- ⟦Tmₑ⟧ σ true = refl
-- ⟦Tmₑ⟧ σ false = refl
-- ⟦Tmₑ⟧ σ (if t u v) rewrite ⟦Tmₑ⟧ σ t | ⟦Tmₑ⟧ σ u | ⟦Tmₑ⟧ σ v = refl

-- ⟦ₛ∘ₑ⟧ : ∀ {Γ Δ Σ} (σ : Sub Δ Σ)(δ : OPE Γ Δ) → ⟦ σ ₛ∘ₑ δ ⟧Sub ≡ ⟦ σ ⟧Sub ∘ ⟦ δ ⟧OPE
-- ⟦ₛ∘ₑ⟧ ∙       δ = refl
-- ⟦ₛ∘ₑ⟧ (σ , t) δ rewrite ⟦ₛ∘ₑ⟧ σ δ | ⟦Tmₑ⟧ δ t = refl

-- ⟦∈ₛ⟧ : ∀ {Γ Δ A}(σ : Sub Γ Δ)(x : A ∈ Δ) → ⟦ ∈ₛ σ x ⟧Tm ≡ ⟦ var x ⟧Tm ∘ ⟦ σ ⟧Sub
-- ⟦∈ₛ⟧ (σ , x) vz     = refl
-- ⟦∈ₛ⟧ (σ , _) (vs x) = ⟦∈ₛ⟧ σ x

-- ⟦Tmₛ⟧ : ∀ {Γ Δ A}(σ : Sub Γ Δ)(t : Tm Δ A) → ⟦ Tmₛ σ t ⟧Tm ≡ ⟦ t ⟧Tm ∘ ⟦ σ ⟧Sub
-- ⟦Tmₛ⟧ σ tt = refl
-- ⟦Tmₛ⟧ σ (π₁ t)     rewrite ⟦Tmₛ⟧ σ t = refl
-- ⟦Tmₛ⟧ σ (π₂ t)     rewrite ⟦Tmₛ⟧ σ t = refl
-- ⟦Tmₛ⟧ σ (t , u)    rewrite ⟦Tmₛ⟧ σ t | ⟦Tmₛ⟧ σ u = refl
-- ⟦Tmₛ⟧ σ (pack e t) rewrite ⟦Tmₛ⟧ σ e | ⟦Tmₛ⟧ σ t = refl
-- ⟦Tmₛ⟧ σ (app⁺ t u) rewrite ⟦Tmₛ⟧ σ t | ⟦Tmₛ⟧ σ u = refl
-- ⟦Tmₛ⟧ σ (var x) = ⟦∈ₛ⟧ σ x
-- ⟦Tmₛ⟧ {Γ} σ (lam {A} t) = refl
-- ⟦Tmₛ⟧ σ (app t u) rewrite ⟦Tmₛ⟧ σ t | ⟦Tmₛ⟧ σ u = refl
-- ⟦Tmₛ⟧ σ true = refl
-- ⟦Tmₛ⟧ σ false = refl
-- ⟦Tmₛ⟧ σ (if t u v) rewrite ⟦Tmₛ⟧ σ t | ⟦Tmₛ⟧ σ u | ⟦Tmₛ⟧ σ v = refl

-- ⟦idₛ⟧ : ∀ {Γ} → ⟦ idₛ {Γ} ⟧Sub ≡ id
-- ⟦idₛ⟧ {∙}     = refl
-- ⟦idₛ⟧ {Γ ▶ A} rewrite ⟦ₛ∘ₑ⟧ (idₛ{Γ}) (wk{A}) | ⟦idₛ⟧ {Γ} | ⟦idₑ⟧{Γ} = refl

-- ⟦~⟧ : ∀ {Γ A}{t t' : Tm Γ A} → t ~ t' → ⟦ t ⟧Tm ≡ ⟦ t' ⟧Tm
-- ⟦~⟧ (π₁β t u) = refl
-- ⟦~⟧ (π₂β t u) = refl
-- ⟦~⟧ (,η t) = refl
-- ⟦~⟧ ttη = refl
-- ⟦~⟧ (βᶜ e t u) = refl
-- ⟦~⟧ {Γ}{t = t} {t'} (ηᶜ {A}{B} p) with ⟦~⟧ p
-- ... | foo rewrite ⟦Tmₑ⟧ (wk{A}) t | ⟦Tmₑ⟧ (wk{A}) t' | ⟦idₑ⟧{Γ} = curry & foo
-- ⟦~⟧ (π₁ t) rewrite ⟦~⟧ t = refl
-- ⟦~⟧ (π₂ t) rewrite ⟦~⟧ t = refl
-- ⟦~⟧ (t , u) rewrite ⟦~⟧ t | ⟦~⟧ u = refl
-- ⟦~⟧ (pack e t) rewrite ⟦~⟧ e | ⟦~⟧ t = refl
-- ⟦~⟧ (app⁺ t u) rewrite ⟦~⟧ t | ⟦~⟧ u = refl
-- ⟦~⟧ {Γ} {B} (β {A} t u) rewrite ⟦Tmₛ⟧ (∙ , u) t = refl
-- ⟦~⟧ {Γ} {t = t₁} {t'} (η {A} {B} t) with ⟦~⟧ t
-- ... | foo rewrite ⟦Tmₑ⟧ (wk{A}) t₁ | ⟦Tmₑ⟧ (wk{A}) t' | ⟦idₑ⟧{Γ} = curry & foo
-- ⟦~⟧ (lam p)   rewrite ⟦~⟧ p = refl
-- ⟦~⟧ (app t u) rewrite ⟦~⟧ t | ⟦~⟧ u = refl
-- ⟦~⟧ ~refl      = refl
-- ⟦~⟧ (p ~⁻¹)    = ⟦~⟧ p ⁻¹
-- ⟦~⟧ (p ~◾ q)   = ⟦~⟧ p ◾ ⟦~⟧ q
-- ⟦~⟧ true       = refl
-- ⟦~⟧ false      = refl
-- ⟦~⟧ (if t u v) rewrite ⟦~⟧ t | ⟦~⟧ u | ⟦~⟧ v = refl
