{-# OPTIONS --without-K #-}

-- NbE for simple type theory with categories-with-families syntax

open import Function
open import Data.Product
open import Data.Unit

-- Syntax
--------------------------------------------------------------------------------

infixr 4 _⇒_
infix  6 _∘ₛ_
infixl 8 _[_]

data Ty : Set where
  ι   : Ty
  _⇒_ : Ty → Ty → Ty

data Con : Set where
  ∙   : Con
  _,_ : Con → Ty → Con

mutual
  data Sub : Con → Con → Set where
    idₛ  : ∀ {Γ} → Sub Γ Γ
    _∘ₛ_ : ∀{Γ Δ Σ} → Sub Δ Σ → Sub Γ Δ → Sub Γ Σ
    _,_  : ∀{Γ Δ}(δ : Sub Γ Δ){A : Ty} → Tm Γ A → Sub Γ (Δ , A)
    π₁   : ∀{Γ Δ}{A : Ty} → Sub Γ (Δ , A) →  Sub Γ Δ

  data Tm : Con → Ty → Set where
    _[_] : ∀{Γ Δ}{A : Ty} → Tm Δ A → Sub Γ Δ → Tm Γ A
    π₂   : ∀{Γ Δ}{A : Ty} → Sub Γ (Δ , A) → Tm Γ A
    app  : ∀{Γ A B} → Tm Γ (A ⇒ B) → Tm (Γ , A) B
    lam  : ∀{Γ A B} → Tm (Γ , A) B → Tm Γ (A ⇒ B)

-- Embedding
--------------------------------------------------------------------------------

infixr 9 _∘ₑ_

data OPE : Con → Con → Set where
  idₑ  : ∀ {Γ} → OPE Γ Γ
  drop : ∀ {Γ Δ A} → OPE Γ Δ → OPE (Γ , A) Δ
  keep : ∀ {Γ Δ A} → OPE Γ Δ → OPE (Γ , A) (Δ , A)

_∘ₑ_ : ∀ {Γ Δ Σ} → OPE Δ Σ → OPE Γ Δ → OPE Γ Σ
σ      ∘ₑ idₑ    = σ
σ      ∘ₑ drop δ = drop (σ ∘ₑ δ)
idₑ    ∘ₑ keep δ = keep δ
drop σ ∘ₑ keep δ = drop (σ ∘ₑ δ)
keep σ ∘ₑ keep δ = keep (σ ∘ₑ δ)

-- Normal forms
--------------------------------------------------------------------------------

infix 3 _∈_
infixl 7 _$ₙ_

data _∈_ (A : Ty) : Con → Set where
  vz : ∀ {Γ} → A ∈ (Γ , A)
  vs : ∀ {B Γ} → A ∈ Γ → A ∈ (Γ , B)

mutual
  data Nf (Γ : Con) : Ty → Set where
    ne   : ∀ {A} → Ne Γ A → Nf Γ A
    lamₙ : ∀ {A B} → Nf (Γ , A) B → Nf Γ (A ⇒ B)

  data Ne (Γ : Con) : Ty → Set where
    var  : ∀ {A} → A ∈ Γ → Ne Γ A
    _$ₙ_ : ∀ {A B} → Ne Γ (A ⇒ B) → Nf Γ A → Ne Γ B

∈ₑ : ∀ {Γ Δ} → OPE Γ Δ → ∀ {A} → A ∈ Δ → A ∈ Γ
∈ₑ idₑ      v      = v
∈ₑ (drop r) v      = vs (∈ₑ r v)
∈ₑ (keep r) vz     = vz
∈ₑ (keep r) (vs v) = vs (∈ₑ r v)

mutual
  Nfₑ : ∀ {Γ Δ} → OPE Γ Δ → ∀ {A} → Nf Δ A → Nf Γ A
  Nfₑ r (ne n)   = ne (Neₑ r n)
  Nfₑ r (lamₙ t) = lamₙ (Nfₑ (keep r) t)

  Neₑ : ∀ {Γ Δ} → OPE Γ Δ → ∀ {A} → Ne Δ A → Ne Γ A
  Neₑ r (var v)  = var (∈ₑ r v)
  Neₑ r (n $ₙ t) = Neₑ r n $ₙ Nfₑ r t

-- Normalization
--------------------------------------------------------------------------------

Tyᴹ : Ty → Con → Set
Tyᴹ ι       Γ = Nf Γ ι
Tyᴹ (A ⇒ B) Γ = ∀ Δ → OPE Δ Γ → Tyᴹ A Δ → Tyᴹ B Δ

Conᴹ : Con → Con → Set
Conᴹ ∙       Δ = ⊤
Conᴹ (Γ , A) Δ = Conᴹ Γ Δ × Tyᴹ A Δ

Tyᴹₑ : ∀ {A Γ Δ} → OPE Γ Δ → Tyᴹ A Δ → Tyᴹ A Γ
Tyᴹₑ {ι}     σ Aᴹ   = Nfₑ σ Aᴹ
Tyᴹₑ {A ⇒ B} σ A⇒Bᴹ = λ Σ δ → A⇒Bᴹ Σ (σ ∘ₑ δ)

Conᴹₑ : ∀ {Σ Γ Δ} → OPE Γ Δ → Conᴹ Σ Δ → Conᴹ Σ Γ
Conᴹₑ {∙}     σ Σᴹ        = tt
Conᴹₑ {Σ , A} σ (Σᴹ , Aᴹ) = Conᴹₑ σ Σᴹ , Tyᴹₑ {A} σ Aᴹ

mutual
  Subᴹ : ∀ {Γ Δ} → Sub Γ Δ → ∀ {Σ} → Conᴹ Γ Σ → Conᴹ Δ Σ
  Subᴹ idₛ      Γᴹ = Γᴹ
  Subᴹ (σ ∘ₛ δ) Γᴹ = Subᴹ σ (Subᴹ δ Γᴹ)
  Subᴹ (σ , t)  Γᴹ = Subᴹ σ Γᴹ , Tmᴹ t Γᴹ
  Subᴹ (π₁ σ)   Γᴹ = proj₁ (Subᴹ σ Γᴹ)

  Tmᴹ : ∀ {Γ A} → Tm Γ A → ∀ {Σ} → Conᴹ Γ Σ → Tyᴹ A Σ
  Tmᴹ (t [ σ ]) Γᴹ = Tmᴹ t (Subᴹ σ Γᴹ)
  Tmᴹ (π₂ σ)    Γᴹ = proj₂ (Subᴹ σ Γᴹ)
  Tmᴹ (app t)   Γᴹ = Tmᴹ t (proj₁ Γᴹ) _ idₑ (proj₂ Γᴹ)
  Tmᴹ (lam t)   Γᴹ = λ Δ σ Aᴹ → Tmᴹ t (Conᴹₑ σ Γᴹ , Aᴹ)

mutual
  q : ∀ A {Γ} → Tyᴹ A Γ → Nf Γ A
  q ι       Aᴹ = Aᴹ
  q (A ⇒ B) Aᴹ = lamₙ (q B (Aᴹ _ (drop idₑ) (u A (var vz))))

  u : ∀ A {Γ} → Ne Γ A → Tyᴹ A Γ
  u ι       n = ne n
  u (A ⇒ B) n = λ Δ r aᴹ → u B (Neₑ r n $ₙ q A aᴹ)

u-Con : ∀ Γ → Conᴹ Γ Γ
u-Con ∙       = tt
u-Con (Γ , A) = Conᴹₑ (drop idₑ) (u-Con Γ) , u A (var vz)

nf : ∀ {Γ A} → Tm Γ A → Nf Γ A
nf {Γ}{A} t = q A (Tmᴹ t (u-Con Γ))
