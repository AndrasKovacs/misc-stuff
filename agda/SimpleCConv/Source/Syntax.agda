{-# OPTIONS --without-K #-}

module Source.Syntax where

open import Lib

infixr 4 _⇒_
infixr 4 _▶_

data Ty : Set where
  𝔹   : Ty
  _⇒_ : Ty → Ty → Ty

data Con : Set where
  ∙   : Con
  _▶_ : Con → Ty → Con

data _∈_ (A : Ty) : Con → Set where
  vz : ∀ {Γ} → A ∈ (Γ ▶ A)
  vs : ∀ {B Γ} → A ∈ Γ → A ∈ (Γ ▶ B)

data Tm Γ : Ty → Set where
  true false : Tm Γ 𝔹
  if   : ∀ {A} → Tm Γ 𝔹 → Tm Γ A → Tm Γ A → Tm Γ A
  var  : ∀ {A} → A ∈ Γ → Tm Γ A
  lam  : ∀ {A B} → Tm (Γ ▶ A) B → Tm Γ (A ⇒ B)
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
Tmₑ σ (if t u v) = if (Tmₑ σ t) (Tmₑ σ u) (Tmₑ σ v)
Tmₑ σ false      = false
Tmₑ σ true       = true
Tmₑ σ (var v)    = var (∈ₑ σ v)
Tmₑ σ (lam t)    = lam (Tmₑ (keep σ) t)
Tmₑ σ (app f a)  = app (Tmₑ σ f) (Tmₑ σ a)

Tm-idₑ : ∀ {A Γ}(t : Tm Γ A) → Tmₑ idₑ t ≡ t
Tm-idₑ (if t u v) = if & Tm-idₑ t ⊗ Tm-idₑ u ⊗ Tm-idₑ v
Tm-idₑ false      = refl
Tm-idₑ true       = refl
Tm-idₑ (var v)    = var & ∈-idₑ v
Tm-idₑ (lam t)    = lam & Tm-idₑ t
Tm-idₑ (app f a)  = app & Tm-idₑ f ⊗ Tm-idₑ a

Tm-∘ₑ : ∀ {A Γ Δ Σ}(σ : OPE Δ Σ)(δ : OPE Γ Δ)(t : Tm Σ A) → Tmₑ (σ ∘ₑ δ) t ≡ Tmₑ δ (Tmₑ σ t)
Tm-∘ₑ Σ δ (if t u v) = if & Tm-∘ₑ Σ δ t ⊗ Tm-∘ₑ Σ δ u ⊗ Tm-∘ₑ Σ δ v
Tm-∘ₑ Σ δ false      = refl
Tm-∘ₑ Σ δ true       = refl
Tm-∘ₑ σ δ (var v)    = var & ∈-∘ₑ σ δ v
Tm-∘ₑ σ δ (lam t)    = lam & Tm-∘ₑ (keep σ) (keep δ) t
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
Tmₛ σ (if t u v) = if (Tmₛ σ t) (Tmₛ σ u) (Tmₛ σ v)
Tmₛ σ false      = false
Tmₛ σ true       = true
Tmₛ σ (var v)    = ∈ₛ σ v
Tmₛ σ (lam t)    = lam (Tmₛ (keepₛ σ) t)
Tmₛ σ (app f a)  = app (Tmₛ σ f) (Tmₛ σ a)

idₛ : ∀ {Γ} → Sub Γ Γ
idₛ {∙}     = ∙
idₛ {Γ ▶ A} = keepₛ idₛ

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
Tm-ₑ∘ₛ σ δ (if t u v) = if & Tm-ₑ∘ₛ σ δ t ⊗ Tm-ₑ∘ₛ σ δ u ⊗ Tm-ₑ∘ₛ σ δ v
Tm-ₑ∘ₛ σ δ false      = refl
Tm-ₑ∘ₛ σ δ true       = refl
Tm-ₑ∘ₛ σ δ (var v) = ∈-ₑ∘ₛ σ δ v
Tm-ₑ∘ₛ σ δ (lam t) =
  lam & ((λ x → Tmₛ (x , var vz) t) & assₑₛₑ σ δ wk ◾ Tm-ₑ∘ₛ (keep σ) (keepₛ δ) t)
Tm-ₑ∘ₛ σ δ (app f a) = app & Tm-ₑ∘ₛ σ δ f ⊗ Tm-ₑ∘ₛ σ δ a

∈-ₛ∘ₑ : ∀ {A Γ Δ Σ}(σ : Sub Δ Σ)(δ : OPE Γ Δ)(v : A ∈ Σ) → ∈ₛ (σ ₛ∘ₑ δ) v ≡ Tmₑ δ (∈ₛ σ v)
∈-ₛ∘ₑ (σ , _) δ vz     = refl
∈-ₛ∘ₑ (σ , _) δ (vs v) = ∈-ₛ∘ₑ σ δ v

Tm-ₛ∘ₑ : ∀ {A Γ Δ Σ}(σ : Sub Δ Σ)(δ : OPE Γ Δ)(t : Tm Σ A) → Tmₛ (σ ₛ∘ₑ δ) t ≡ Tmₑ δ (Tmₛ σ t)
Tm-ₛ∘ₑ σ δ (if t u v) = if & Tm-ₛ∘ₑ σ δ t ⊗ Tm-ₛ∘ₑ σ δ u ⊗ Tm-ₛ∘ₑ σ δ v
Tm-ₛ∘ₑ σ δ false      = refl
Tm-ₛ∘ₑ σ δ true       = refl
Tm-ₛ∘ₑ σ δ (var v)   = ∈-ₛ∘ₑ σ δ v
Tm-ₛ∘ₑ σ δ (lam t)   =
  lam &
      ((λ x → Tmₛ (x , var vz) t) &
          (assₛₑₑ σ δ wk
        ◾ (σ ₛ∘ₑ_) & (drop & (idrₑ δ ◾ idlₑ δ ⁻¹))
        ◾ assₛₑₑ σ wk (keep δ) ⁻¹)
    ◾ Tm-ₛ∘ₑ (keepₛ σ) (keep δ) t)
Tm-ₛ∘ₑ σ δ (app f a) = app & Tm-ₛ∘ₑ σ δ f ⊗ Tm-ₛ∘ₑ σ δ a

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
Tm-idₛ (if t u v) = if & Tm-idₛ t ⊗ Tm-idₛ u ⊗ Tm-idₛ v
Tm-idₛ false      = refl
Tm-idₛ true       = refl
Tm-idₛ (var v)   = ∈-idₛ v
Tm-idₛ (lam t)   = lam & Tm-idₛ t
Tm-idₛ (app f a) = app & Tm-idₛ f ⊗ Tm-idₛ a

Tm-∘ₛ : ∀ {A Γ Δ Σ}(σ : Sub Δ Σ)(δ : Sub Γ Δ)(t : Tm Σ A) → Tmₛ (σ ∘ₛ δ) t ≡ Tmₛ δ (Tmₛ σ t)
Tm-∘ₛ σ δ (if t u v) = if & Tm-∘ₛ σ δ t ⊗ Tm-∘ₛ σ δ u ⊗ Tm-∘ₛ σ δ v
Tm-∘ₛ σ δ false      = refl
Tm-∘ₛ σ δ true       = refl
Tm-∘ₛ σ δ (var v)   = ∈-∘ₛ σ δ v
Tm-∘ₛ σ δ (lam t)   =
  lam &
      ((λ x → Tmₛ (x , var vz) t) &
          (assₛₛₑ σ δ wk
        ◾ (σ ∘ₛ_) & (idlₑₛ  (dropₛ δ) ⁻¹) ◾ assₛₑₛ σ wk (keepₛ δ) ⁻¹)
    ◾ Tm-∘ₛ (keepₛ σ) (keepₛ δ) t)
Tm-∘ₛ σ δ (app f a) = app & Tm-∘ₛ σ δ f ⊗ Tm-∘ₛ σ δ a

idrₛ : ∀ {Γ Δ}(σ : Sub Γ Δ) → σ ∘ₛ idₛ ≡ σ
idrₛ ∙       = refl
idrₛ (σ , t) = _,_ & idrₛ σ ⊗ Tm-idₛ t

idlₛ : ∀ {Γ Δ}(σ : Sub Γ Δ) → idₛ ∘ₛ σ ≡ σ
idlₛ ∙       = refl
idlₛ (σ , t) = (_, t) & (assₛₑₛ idₛ wk (σ , t) ◾ (idₛ ∘ₛ_) & idlₑₛ σ ◾ idlₛ σ)

-- Conversion
--------------------------------------------------------------------------------

data _~_ {Γ} : ∀ {A} → Tm Γ A → Tm Γ A → Set where
  β     : ∀ {A B}(t : Tm (Γ ▶ A) B) t'  → app (lam t) t' ~ Tmₛ (idₛ , t') t
  η     : ∀ {A B}(t : Tm Γ (A ⇒ B))     → t ~ lam (app (Tmₑ wk t) (var vz))
  lam   : ∀ {A B}{t t' : Tm (Γ ▶ A) B}  → t ~ t' →  lam t ~ lam t'
  app   : ∀ {A B}{t t' : Tm Γ (A ⇒ B)}{u u'} → t ~ t' → u ~ u' → app t u ~ app t' u'
  true  : ∀ {A}{t u : Tm Γ A} → if true  t u ~ t
  false : ∀ {A}{t u : Tm Γ A} → if false t u ~ u
  if    : ∀ {A}{t t' : Tm Γ 𝔹}{u u' v v' : Tm Γ A} → t ~ t' → u ~ u' → v ~ v' → if t u v ~ if t' u' v'
  ~refl : ∀ {A}{t : Tm Γ A} → t ~ t
  _~⁻¹  : ∀ {A}{t t' : Tm Γ A} → t ~ t' → t' ~ t
  _~◾_  : ∀ {A}{t t' t'' : Tm Γ A} → t ~ t' → t' ~ t'' → t ~ t''

~ₑ : ∀ {Γ Δ A}{t t' : Tm Γ A}(σ : OPE Δ Γ) → t ~ t' → Tmₑ σ t ~ Tmₑ σ t'
~ₑ σ (η t) =
  coe ((λ t' → Tmₑ σ t ~ lam (app t' (var vz)))
    & (Tm-∘ₑ σ wk t ⁻¹
    ◾ (λ x → Tmₑ (drop x) t) & (idrₑ σ ◾ idlₑ σ ⁻¹)
    ◾ Tm-∘ₑ wk  (keep σ) t))
  (η (Tmₑ σ t))

~ₑ σ (β t t') =
  coe ((app (lam (Tmₑ (keep σ) t)) (Tmₑ σ t') ~_) &
    (Tm-ₑ∘ₛ (keep σ) (idₛ , Tmₑ σ t') t ⁻¹
    ◾ (λ x → Tmₛ (x , Tmₑ σ t') t) & (idrₑₛ σ ◾ idlₛₑ σ ⁻¹)
    ◾ Tm-ₛ∘ₑ (idₛ , t') σ t))
  (β (Tmₑ (keep σ) t) (Tmₑ σ t'))

~ₑ σ (lam t~t')       = lam (~ₑ (keep σ) t~t')
~ₑ σ (app t~t' x~x')  = app (~ₑ σ t~t') (~ₑ σ x~x')
~ₑ σ ~refl            = ~refl
~ₑ σ (t~t' ~⁻¹)       = ~ₑ σ t~t' ~⁻¹
~ₑ σ (t~t' ~◾ t'~t'') = ~ₑ σ t~t' ~◾ ~ₑ σ t'~t''
~ₑ σ true             = true
~ₑ σ false            = false
~ₑ σ (if t u v)       = if (~ₑ σ t) (~ₑ σ u) (~ₑ σ v)
