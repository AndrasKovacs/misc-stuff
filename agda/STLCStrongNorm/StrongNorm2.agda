{-# OPTIONS --without-K #-}

-- strong normalization for STLC, adapted from
--   https://www.ps.uni-saarland.de/~schaefer/thesis/html/semantics.f.strongnorm.html
-- checked with Agda 2.6.0.1

open import Relation.Binary.PropositionalEquality
open import Data.Product
open import Data.Unit
open import Data.Empty
open import Function

_&_ = cong; infixl 9 _&_
_⁻¹ = sym; infix 6 _⁻¹
_◾_ = trans; infixr 4 _◾_

coe : {A B : Set} → A ≡ B → A → B
coe refl a = a

infixl 8 _⊗_
_⊗_ : ∀ {A B : Set}{f g : A → B}{a a'} → f ≡ g → a ≡ a' → f a ≡ g a'
refl ⊗ refl = refl

-- Syntax
--------------------------------------------------------------------------------

infixr 4 _⇒_
infixr 4 _,_

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

-- Order-preserving embedding
--------------------------------------------------------------------------------

data OPE : Con → Con → Set where
  ∙    : OPE ∙ ∙
  drop : ∀ {A Γ Δ} → OPE Γ Δ → OPE (Γ , A) Δ
  keep : ∀ {A Γ Δ} → OPE Γ Δ → OPE (Γ , A) (Δ , A)

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

Tmₑ : ∀ {A Γ Δ} → OPE Γ Δ → Tm Δ A → Tm Γ A
Tmₑ σ (var v)   = var (∈ₑ σ v)
Tmₑ σ (lam t)   = lam (Tmₑ (keep σ) t)
Tmₑ σ (app f a) = app (Tmₑ σ f) (Tmₑ σ a)

Tm-idₑ : ∀ {A Γ}(t : Tm Γ A) → Tmₑ idₑ t ≡ t
Tm-idₑ (var v)   = var & ∈-idₑ v
Tm-idₑ (lam t)   = lam & Tm-idₑ t
Tm-idₑ (app f a) = app & Tm-idₑ f ⊗ Tm-idₑ a

Tm-∘ₑ : ∀ {A Γ Δ Σ}(σ : OPE Δ Σ)(δ : OPE Γ Δ)(t : Tm Σ A) → Tmₑ (σ ∘ₑ δ) t ≡ Tmₑ δ (Tmₑ σ t)
Tm-∘ₑ σ δ (var v)   = var & ∈-∘ₑ σ δ v
Tm-∘ₑ σ δ (lam t)   = lam & Tm-∘ₑ (keep σ) (keep δ) t
Tm-∘ₑ σ δ (app f a) = app & Tm-∘ₑ σ δ f ⊗ Tm-∘ₑ σ δ a

-- Substitution
--------------------------------------------------------------------------------

infixr 6 _ₑ∘ₛ_ _ₛ∘ₑ_ _∘ₛ_

data Sub (Γ : Con) : Con → Set where
  ∙   : Sub Γ ∙
  _,_ : ∀ {A : Ty}{Δ : Con} → Sub Γ Δ → Tm Γ A → Sub Γ (Δ , A)

_ₛ∘ₑ_ : ∀ {Γ Δ Σ} → Sub Δ Σ → OPE Γ Δ → Sub Γ Σ
∙       ₛ∘ₑ δ = ∙
(σ , t) ₛ∘ₑ δ = σ ₛ∘ₑ δ , Tmₑ δ t

_ₑ∘ₛ_ : ∀ {Γ Δ Σ} → OPE Δ Σ → Sub Γ Δ → Sub Γ Σ
∙      ₑ∘ₛ δ       = δ
drop σ ₑ∘ₛ (δ , t) = σ ₑ∘ₛ δ
keep σ ₑ∘ₛ (δ , t) = σ ₑ∘ₛ δ , t

dropₛ : ∀ {A Γ Δ} → Sub Γ Δ → Sub (Γ , A) Δ
dropₛ σ = σ ₛ∘ₑ wk

keepₛ : ∀ {A Γ Δ} → Sub Γ Δ → Sub (Γ , A) (Δ , A)
keepₛ σ = dropₛ σ , var vz

∈ₛ : ∀ {A Γ Δ} → Sub Γ Δ → A ∈ Δ → Tm Γ A
∈ₛ (σ , t) vz     = t
∈ₛ (σ  , t)(vs v) = ∈ₛ σ v

Tmₛ : ∀ {A Γ Δ} → Sub Γ Δ → Tm Δ A → Tm Γ A
Tmₛ σ (var v)   = ∈ₛ σ v
Tmₛ σ (lam t)   = lam (Tmₛ (keepₛ σ) t)
Tmₛ σ (app f a) = app (Tmₛ σ f) (Tmₛ σ a)

idₛ : ∀ {Γ} → Sub Γ Γ
idₛ {∙}     = ∙
idₛ {Γ , A} = (idₛ {Γ} ₛ∘ₑ drop idₑ) , var vz

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

idrₑₛ : ∀ {Γ Δ}(σ : OPE Γ Δ) → σ ₑ∘ₛ idₛ ≡ idₛ ₛ∘ₑ σ
idrₑₛ ∙        = refl
idrₑₛ (drop σ) =
  assₑₛₑ σ idₛ wk ⁻¹ ◾ dropₛ & idrₑₛ σ ◾ assₛₑₑ idₛ σ wk ◾ (idₛ ₛ∘ₑ_) & (drop & idrₑ σ)
idrₑₛ (keep σ) =
  (_, var vz) & (assₑₛₑ σ idₛ wk ⁻¹ ◾ (_ₛ∘ₑ wk) & idrₑₛ σ
  ◾ assₛₑₑ idₛ σ wk ◾ (idₛ ₛ∘ₑ_) & (drop & (idrₑ σ ◾ idlₑ σ ⁻¹))
  ◾ assₛₑₑ idₛ wk (keep σ) ⁻¹)

∈-ₑ∘ₛ : ∀ {A Γ Δ Σ}(σ : OPE Δ Σ)(δ : Sub Γ Δ)(v : A ∈ Σ) → ∈ₛ (σ ₑ∘ₛ δ) v ≡ ∈ₛ δ (∈ₑ σ v)
∈-ₑ∘ₛ ∙        δ       v      = refl
∈-ₑ∘ₛ (drop σ) (δ , t) v      = ∈-ₑ∘ₛ σ δ v
∈-ₑ∘ₛ (keep σ) (δ , t) vz     = refl
∈-ₑ∘ₛ (keep σ) (δ , t) (vs v) = ∈-ₑ∘ₛ σ δ v

Tm-ₑ∘ₛ : ∀ {A Γ Δ Σ}(σ : OPE Δ Σ)(δ : Sub Γ Δ)(t : Tm Σ A) → Tmₛ (σ ₑ∘ₛ δ) t ≡ Tmₛ δ (Tmₑ σ t)
Tm-ₑ∘ₛ σ δ (var v) = ∈-ₑ∘ₛ σ δ v
Tm-ₑ∘ₛ σ δ (lam t) =
  lam & ((λ x → Tmₛ (x , var vz) t) & assₑₛₑ σ δ wk ◾ Tm-ₑ∘ₛ (keep σ) (keepₛ δ) t)
Tm-ₑ∘ₛ σ δ (app f a) = app & Tm-ₑ∘ₛ σ δ f ⊗ Tm-ₑ∘ₛ σ δ a

∈-ₛ∘ₑ : ∀ {A Γ Δ Σ}(σ : Sub Δ Σ)(δ : OPE Γ Δ)(v : A ∈ Σ) → ∈ₛ (σ ₛ∘ₑ δ) v ≡ Tmₑ δ (∈ₛ σ v)
∈-ₛ∘ₑ (σ , _) δ vz     = refl
∈-ₛ∘ₑ (σ , _) δ (vs v) = ∈-ₛ∘ₑ σ δ v

Tm-ₛ∘ₑ : ∀ {A Γ Δ Σ}(σ : Sub Δ Σ)(δ : OPE Γ Δ)(t : Tm Σ A) → Tmₛ (σ ₛ∘ₑ δ) t ≡ Tmₑ δ (Tmₛ σ t)
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
Tm-idₛ (var v)   = ∈-idₛ v
Tm-idₛ (lam t)   = lam & Tm-idₛ t
Tm-idₛ (app f a) = app & Tm-idₛ f ⊗ Tm-idₛ a

Tm-∘ₛ : ∀ {A Γ Δ Σ}(σ : Sub Δ Σ)(δ : Sub Γ Δ)(t : Tm Σ A) → Tmₛ (σ ∘ₛ δ) t ≡ Tmₛ δ (Tmₛ σ t)
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

-- Reduction
--------------------------------------------------------------------------------

data _~>_ {Γ} : ∀ {A} → Tm Γ A → Tm Γ A → Set where
  β    : ∀ {A B}(t : Tm (Γ , A) B) t'  → app (lam t) t' ~> Tmₛ (idₛ , t') t
  lam  : ∀ {A B}{t t' : Tm (Γ , A) B}     → t ~> t' →  lam t   ~> lam t'
  app₁ : ∀ {A B}{f}{f' : Tm Γ (A ⇒ B)}{a} → f ~> f' →  app f a ~> app f' a
  app₂ : ∀ {A B}{f : Tm Γ (A ⇒ B)} {a a'} → a ~> a' →  app f a ~> app f  a'
infix 3 _~>_

~>ₛ : ∀ {Γ Δ A}{t t' : Tm Γ A}(σ : Sub Δ Γ) → t ~> t' → Tmₛ σ t ~> Tmₛ σ t'
~>ₛ σ (β t t') =
  coe ((app (lam (Tmₛ (keepₛ σ) t)) (Tmₛ σ t') ~>_) &
      (Tm-∘ₛ (keepₛ σ) (idₛ , Tmₛ σ t') t ⁻¹
    ◾ (λ x → Tmₛ (x , Tmₛ σ t') t) &
        (assₛₑₛ σ wk (idₛ , Tmₛ σ t')
      ◾ ((σ ∘ₛ_) & idlₑₛ idₛ ◾ idrₛ σ) ◾ idlₛ σ ⁻¹)
    ◾ Tm-∘ₛ (idₛ , t') σ t))
  (β (Tmₛ (keepₛ σ) t) (Tmₛ σ t'))
~>ₛ σ (lam  step) = lam  (~>ₛ (keepₛ σ) step)
~>ₛ σ (app₁ step) = app₁ (~>ₛ σ step)
~>ₛ σ (app₂ step) = app₂ (~>ₛ σ step)

Tmₑ~> :
  ∀ {Γ Δ A}{t : Tm Γ A}{σ : OPE Δ Γ}{t'}
  → Tmₑ σ t ~> t' → ∃ λ t'' → (t ~> t'') × (Tmₑ σ t'' ≡ t')
Tmₑ~> {t = var x} ()
Tmₑ~> {t = lam t} (lam step) with Tmₑ~> step
... | t'' , (p , refl) = lam t'' , lam p , refl
Tmₑ~> {t = app (var v) a} (app₁ ())
Tmₑ~> {t = app (var v) a} (app₂ step) with Tmₑ~> step
... | t'' , (p , refl) = app (var v) t'' , app₂ p , refl
Tmₑ~> {t = app (lam f) a} {σ} (β _ _) =
  Tmₛ (idₛ , a) f , β _ _ ,
      Tm-ₛ∘ₑ (idₛ , a) σ f ⁻¹
    ◾ (λ x →  Tmₛ (x , Tmₑ σ a) f) & (idrₑₛ σ ⁻¹)
    ◾ Tm-ₑ∘ₛ (keep σ) (idₛ , Tmₑ σ a) f
Tmₑ~> {t = app (lam f) a}     (app₁ (lam step)) with Tmₑ~> step
... | t'' , (p , refl) = app (lam t'') a , app₁ (lam p) , refl
Tmₑ~> {t = app (lam f) a}     (app₂ step) with Tmₑ~> step
... | t'' , (p , refl) = app (lam f) t'' , app₂ p , refl
Tmₑ~> {t = app (app f a) a'}  (app₁ step) with Tmₑ~> step
... | t'' , (p , refl) = app t'' a' , app₁ p , refl
Tmₑ~> {t = app (app f a) a''} (app₂ step) with Tmₑ~> step
... | t'' , (p , refl) = app (app f a) t'' , app₂ p , refl

-- Strong normalization
--------------------------------------------------------------------------------

-- strong normalization predicate
data SN {Γ A} (t : Tm Γ A) : Set where
  sn : (∀ {t'} → t ~> t' → SN t') → SN t

-- SN annotated all the way down with a predicate on terms
data SN* {A} (P : ∀ {Γ} → Tm Γ A → Set) {Γ}(t : Tm Γ A) : Set where
  sn* : P t → (∀ {t'} → t ~> t' → SN* P t') → SN* P t

SN*-SN : ∀ {Γ A}{P : ∀ {Γ} → Tm Γ A → Set}{t : Tm Γ A} → SN* P t → SN t
SN*-SN (sn* p q) = sn (λ st → SN*-SN (q st))


Tmᴾ : ∀ {A Γ} → Tm Γ A → Set
Tmᴾ {Γ = Γ} (lam t) =
  ∀ {Δ}(σ : OPE Δ Γ){u} → SN* Tmᴾ u → SN* Tmᴾ (Tmₛ (idₛ ₛ∘ₑ σ , u) t)
Tmᴾ _ = ⊤

-- the actual induction predicate used in the "fundamental theorem"
P : ∀ {A Γ} → Tm Γ A → Set
P = SN* Tmᴾ

Tmᴾₑ : ∀ {Γ Δ A}(σ : OPE Γ Δ){t : Tm Δ A} → Tmᴾ t → Tmᴾ (Tmₑ σ t)
Tmᴾₑ σ {lam t} tᴾ =
  λ δ {u} uᴾ → coe (P & ((λ x → Tmₛ (x , u) t) &
                   ((assₛₑₑ idₛ σ δ ⁻¹ ◾ (_ₛ∘ₑ δ) & idrₑₛ σ ⁻¹) ◾ assₑₛₑ σ idₛ δ)
                     ◾ Tm-ₑ∘ₛ _ _ t))
                   (tᴾ (σ ∘ₑ δ) uᴾ)
Tmᴾₑ σ {var _} tᴾ = tt
Tmᴾₑ σ {app _ _} tᴾ = tt

P~> : ∀ {Γ A}{t t' : Tm Γ A} → t ~> t' → P t → P t'
P~> st (sn* p q) = q st

Pₑ : ∀ {Γ Δ A}(σ : OPE Γ Δ){t : Tm Δ A} → P t → P (Tmₑ σ t)
Pₑ σ (sn* p q) =
  sn* (Tmᴾₑ σ p) λ st → case Tmₑ~> st of λ {(t'' , st' , refl) → Pₑ σ (q st')}

P-lam : ∀ {Γ A B}{t : Tm (Γ , A) B} → Tmᴾ (lam t) → P t → P (lam t)
P-lam lamtᴾ (sn* p q) =
  sn* lamtᴾ (λ {(lam st) → P-lam (λ σ uᴾ → P~> (~>ₛ _ st) (lamtᴾ σ uᴾ) ) (q st)})

P-app : ∀ {Γ A B}{t : Tm Γ (A ⇒ B)}{u : Tm Γ A} → P t → P u → P (app t u)
P-app =
  ind-help
    (λ t u → P (app t u))
    (λ { {t} {u} (sn* tp tq) uᴾ f g →
      sn* tt (λ {(β t t')  → coe ((λ x → P (Tmₛ (x , u) t)) & (idrₑₛ _ ⁻¹ ◾ idlₑₛ _))
                                (tp idₑ uᴾ) ;
                (app₁ st) → f st ;
                (app₂ st) → g st})})
  where
    ind-help : ∀ {Γ A B}(R : Tm Γ A → Tm Γ B → Set)
             → (∀ {t u} → P t → P u
                 → (∀ {t'} → t ~> t' → R t' u)
                 → (∀ {u'} → u ~> u' → R t u')
                → R t u)
             → ∀ {t u} → P t → P u → R t u
    ind-help R f (sn* tp tq) (sn* up uq) =
      f (sn* tp tq) (sn* up uq)
        (λ st → ind-help R f (tq st) (sn* up uq))
        (λ st → ind-help R f (sn* tp tq) (uq st))

data Subᴾ {Γ} : ∀ {Δ} → Sub Γ Δ → Set where
  ∙   : Subᴾ ∙
  _,_ : ∀ {A Δ}{σ : Sub Γ Δ}{t : Tm Γ A}(σᴾ : Subᴾ σ)(tᴾ : P t) → Subᴾ (σ , t)

Subᴾₑ : ∀ {Γ Δ Σ}{σ : Sub Δ Σ}(δ : OPE Γ Δ) → Subᴾ σ → Subᴾ (σ ₛ∘ₑ δ)
Subᴾₑ σ ∙        = ∙
Subᴾₑ σ (δ , tᴾ) = Subᴾₑ σ δ , Pₑ σ tᴾ

-- "fundamental theorem"
fth : ∀ {Γ A}(t : Tm Γ A) → ∀ {Δ}{σ : Sub Δ Γ} → Subᴾ σ → P (Tmₛ σ t)
fth (var vz) (σᴾ , tᴾ) = tᴾ
fth (var (vs x)) (σᴾ , tᴾ) = fth (var x) σᴾ
fth (lam t) {Δ}{σ} σᴾ =
  P-lam (λ δ {u} uᴾ →
          coe (P & ((λ x → Tmₛ (x , u) t)&
                       ((((_ₛ∘ₑ δ) & (idrₛ σ ⁻¹) ◾ assₛₛₑ σ idₛ δ)
                       ◾ (σ ∘ₛ_) & idlₑₛ (idₛ ₛ∘ₑ δ) ⁻¹)
                       ◾ assₛₑₛ σ wk (idₛ ₛ∘ₑ δ , u) ⁻¹) ◾ Tm-∘ₛ _ _ t))
              (fth t (Subᴾₑ δ σᴾ , uᴾ)))
        (fth t (Subᴾₑ wk σᴾ , sn* tt (λ ())))
fth (app t u) σᴾ = P-app (fth t σᴾ) (fth u σᴾ)

idₛᴾ : ∀ {Γ} → Subᴾ (idₛ {Γ})
idₛᴾ {∙}     = ∙
idₛᴾ {Γ , A} = Subᴾₑ wk idₛᴾ , sn* tt (λ ())

strongNorm : ∀ {Γ A}(t : Tm Γ A) → SN t
strongNorm t = coe (SN & Tm-idₛ t) (SN*-SN (fth t idₛᴾ))
