{-# OPTIONS --without-K #-}

-- NbE for simple type theory with Categories-with-families syntax

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
  data Tms : Con → Con → Set where
    idₛ  : ∀ {Γ} → Tms Γ Γ
    _∘ₛ_ : ∀{Γ Δ Σ} → Tms Δ Σ → Tms Γ Δ → Tms Γ Σ
    _,_  : ∀{Γ Δ}(δ : Tms Γ Δ){A : Ty} → Tm Γ A → Tms Γ (Δ , A)
    π₁   : ∀{Γ Δ}{A : Ty} → Tms Γ (Δ , A) →  Tms Γ Δ
  
  data Tm : Con → Ty → Set where
    _[_] : ∀{Γ Δ}{A : Ty} → Tm Δ A → Tms Γ Δ → Tm Γ A
    π₂   : ∀{Γ Δ}{A : Ty} → Tms Γ (Δ , A) → Tm Γ A
    app  : ∀{Γ A B} → Tm Γ (A ⇒ B) → Tm (Γ , A) B
    lam  : ∀{Γ A B} → Tm (Γ , A) B → Tm Γ (A ⇒ B)

-- Renaming
--------------------------------------------------------------------------------

infix 3 _⊆_
infixr 9 _∘ᵣ_

data _⊆_ : Con → Con → Set where
  idᵣ : ∀ {Γ} → Γ ⊆ Γ
  add  : ∀ {Γ Δ A} → Γ ⊆ Δ → Γ     ⊆ Δ , A
  keep : ∀ {Γ Δ A} → Γ ⊆ Δ → Γ , A ⊆ Δ , A

_∘ᵣ_ : ∀ {Γ Δ Ξ} → Δ ⊆ Ξ → Γ ⊆ Δ → Γ ⊆ Ξ
idᵣ    ∘ᵣ o'      = o'
add o  ∘ᵣ o'      = add (o ∘ᵣ o')
keep o ∘ᵣ idᵣ     = keep o
keep o ∘ᵣ add o'  = add (o ∘ᵣ o')
keep o ∘ᵣ keep o' = keep (o ∘ᵣ o')

-- Normal forms
--------------------------------------------------------------------------------

infix 3 _∈_
infixl 7 _$ₙ_

data _∈_ (A : Ty) : Con → Set where
  vz : ∀ {Γ} → A ∈ (Γ , A)
  vs : ∀ {B Γ} → A ∈ Γ → A ∈ (Γ , B)

mutual
  data Nf (Γ : Con) : Ty → Set where
    ne   : Ne Γ ι → Nf Γ ι
    lamₙ : ∀ {A B} → Nf (Γ , A) B → Nf Γ (A ⇒ B)

  data Ne (Γ : Con) : Ty → Set where
    var  : ∀ {A} → A ∈ Γ → Ne Γ A
    _$ₙ_ : ∀ {A B} → Ne Γ (A ⇒ B) → Nf Γ A → Ne Γ B

∈↑ : ∀ {Γ Δ A} → Γ ⊆ Δ → A ∈ Γ → A ∈ Δ
∈↑ idᵣ      v      = v
∈↑ (add r)  v      = vs (∈↑ r v)
∈↑ (keep r) vz     = vz
∈↑ (keep r) (vs v) = vs (∈↑ r v)

mutual
  Nf↑ : ∀ {Γ Δ A} → Γ ⊆ Δ → Nf Γ A → Nf Δ A
  Nf↑ r (ne n)   = ne (Ne↑ r n)
  Nf↑ r (lamₙ t) = lamₙ (Nf↑ (keep r) t)
  
  Ne↑ : ∀ {Γ Δ A} → Γ ⊆ Δ → Ne Γ A → Ne Δ A
  Ne↑ r (var v)  = var (∈↑ r v)
  Ne↑ r (n $ₙ t) = Ne↑ r n $ₙ Nf↑ r t

-- Normalization
--------------------------------------------------------------------------------

PSh : Set → Set₁
PSh S = S → Set

_∸>_ : ∀ {α β γ}{I : Set α} → (I → Set β) → (I → Set γ) → Set _
A ∸> B = ∀ {i} → A i → B i

⟦_⟧Ty : Ty → PSh Con
⟦ ι     ⟧Ty Γ = Nf Γ ι
⟦ A ⇒ B ⟧Ty Γ = ∀ Δ → Γ ⊆ Δ → ⟦ A ⟧Ty Δ → ⟦ B ⟧Ty Δ

⟦_⟧Con : Con → PSh Con
⟦ ∙     ⟧Con Δ = ⊤
⟦ Γ , A ⟧Con Δ = ⟦ Γ ⟧Con Δ × ⟦ A ⟧Ty Δ

⟦Ty⟧↑ : ∀ {A Γ Δ} → Γ ⊆ Δ → ⟦ A ⟧Ty Γ → ⟦ A ⟧Ty Δ
⟦Ty⟧↑ {ι}     r ⟦A⟧   = Nf↑ r ⟦A⟧
⟦Ty⟧↑ {A ⇒ B} r ⟦A⇒B⟧ = λ Σ r' → ⟦A⇒B⟧ Σ (r' ∘ᵣ r)

⟦Con⟧↑ : ∀ {Σ Γ Δ} → Γ ⊆ Δ → ⟦ Σ ⟧Con Γ → ⟦ Σ ⟧Con Δ
⟦Con⟧↑ {∙}     r ⟦Σ⟧         = tt
⟦Con⟧↑ {Σ , A} r (⟦Σ⟧ , ⟦A⟧) = ⟦Con⟧↑ r ⟦Σ⟧ , ⟦Ty⟧↑ r ⟦A⟧

mutual
  ⟦_⟧Tms : ∀ {Γ Δ} → Tms Γ Δ → ⟦ Γ ⟧Con ∸> ⟦ Δ ⟧Con
  ⟦ idₛ    ⟧Tms = id
  ⟦ σ ∘ₛ δ ⟧Tms = ⟦ σ ⟧Tms ∘ ⟦ δ ⟧Tms
  ⟦ σ , t  ⟧Tms = _,_ ∘ ⟦ σ ⟧Tms ˢ ⟦ t ⟧Tm
  ⟦ π₁ σ   ⟧Tms = proj₁ ∘ ⟦ σ ⟧Tms

  ⟦_⟧Tm : ∀ {Γ A} → Tm Γ A → ⟦ Γ ⟧Con ∸> ⟦ A ⟧Ty
  ⟦ t [ σ ] ⟧Tm Γᴹ        = ⟦ t ⟧Tm (⟦ σ ⟧Tms Γᴹ)
  ⟦ π₂ σ    ⟧Tm Γᴹ        = proj₂ (⟦ σ ⟧Tms Γᴹ)
  ⟦ app t   ⟧Tm (Γᴹ , Aᴹ) = ⟦ t ⟧Tm Γᴹ _ idᵣ Aᴹ
  ⟦ lam t   ⟧Tm Γᴹ Δ r aᴹ = ⟦ t ⟧Tm (⟦Con⟧↑ r Γᴹ , aᴹ)

mutual
  q : ∀ A {Γ} → ⟦ A ⟧Ty Γ → Nf Γ A
  q ι       Aᴹ = Aᴹ
  q (A ⇒ B) Aᴹ = lamₙ (q B (Aᴹ _ (add idᵣ) (u A (var vz))))

  u : ∀ A {Γ} → Ne Γ A → ⟦ A ⟧Ty Γ
  u ι       n = ne n
  u (A ⇒ B) n = λ Δ r aᴹ → u B (Ne↑ r n $ₙ q A aᴹ)

u-Con : ∀ Γ → ⟦ Γ ⟧Con Γ
u-Con ∙       = tt
u-Con (Γ , A) = ⟦Con⟧↑ (add idᵣ) (u-Con Γ) , u A (var vz)

nf : ∀ {Γ A} → Tm Γ A → Nf Γ A
nf {Γ}{A} t = q A (⟦ t ⟧Tm (u-Con Γ))
