
-- Beta-eta normalization for Gödel's System T.
-- Of course there is no eta for naturals, only for functions
-- and products.

{-# OPTIONS --without-K #-}

open import Function
open import Data.Product

-- Syntax
--------------------------------------------------------------------------------

infixr 4 _⇒_

data Ty : Set where
  _⇒_ : Ty → Ty → Ty
  _*_ : Ty → Ty → Ty
  ℕ   : Ty

data Con : Set where
  ∙   : Con
  _,_ : Con → Ty → Con

infix 3 _∈_
data _∈_ (A : Ty) : Con → Set where
  vz : ∀ {Γ} → A ∈ (Γ , A)
  vs : ∀ {B Γ} → A ∈ Γ → A ∈ (Γ , B)

data Tm Γ : Ty → Set where
  var   : ∀ {A} → A ∈ Γ → Tm Γ A

  lam   : ∀ {A B} → Tm (Γ , A) B → Tm Γ (A ⇒ B)
  app   : ∀ {A B} → Tm Γ (A ⇒ B) → Tm Γ A → Tm Γ B

  π₁    : ∀ {A B} → Tm Γ (A * B) → Tm Γ A
  π₂    : ∀ {A B} → Tm Γ (A * B) → Tm Γ B
  _,_   : ∀ {A B} → Tm Γ A → Tm Γ B → Tm Γ (A * B)

  zero  : Tm Γ ℕ
  suc   : Tm Γ ℕ → Tm Γ ℕ
  ℕ-rec : ∀ {R} → Tm Γ ℕ → Tm Γ R → Tm (Γ , ℕ) R → Tm Γ R


-- Renaming
--------------------------------------------------------------------------------

data Ren : Con → Con → Set where
  ∙    : Ren ∙ ∙
  drop : ∀ {A Γ Δ} → Ren Γ Δ → Ren (Γ , A) Δ
  keep : ∀ {A Γ Δ} → Ren Γ Δ → Ren (Γ , A) (Δ , A)

infixr 9 _∘ᵣ_
_∘ᵣ_ : ∀ {Γ Δ Σ} → Ren Δ Σ → Ren Γ Δ → Ren Γ Σ
σ      ∘ᵣ ∙      = σ
σ      ∘ᵣ drop δ = drop (σ ∘ᵣ δ)
drop σ ∘ᵣ keep δ = drop (σ ∘ᵣ δ)
keep σ ∘ᵣ keep δ = keep (σ ∘ᵣ δ)

idᵣ : ∀ {Γ} → Ren Γ Γ
idᵣ {∙}     = ∙
idᵣ {Γ , A} = keep idᵣ

wk : ∀ {A Γ} → Ren (Γ , A) Γ
wk = drop idᵣ

-- Normal forms
--------------------------------------------------------------------------------

mutual
  data Nf (Γ : Con) : Ty → Set where
    _,_  : ∀ {A B} → Nf Γ A → Nf Γ B → Nf Γ (A * B)
    lam  : ∀ {A B} → Nf (Γ , A) B → Nf Γ (A ⇒ B)
    ne   : Ne Γ ℕ → Nf Γ ℕ
    zero : Nf Γ ℕ
    suc  : Nf Γ ℕ → Nf Γ ℕ

  data Ne (Γ : Con) : Ty → Set where
    var   : ∀ {A} → A ∈ Γ → Ne Γ A
    app   : ∀ {A B} → Ne Γ (A ⇒ B) → Nf Γ A → Ne Γ B
    π₁    : ∀ {A B} → Ne Γ (A * B) → Ne Γ A
    π₂    : ∀ {A B} → Ne Γ (A * B) → Ne Γ B
    ℕ-rec : ∀ {R} → Ne Γ ℕ → Nf Γ R → Nf (Γ , ℕ) R → Ne Γ R

_[_]∈ᵣ : ∀ {Γ Δ A} → A ∈ Δ → Ren Γ Δ → A ∈ Γ
v    [ ∙      ]∈ᵣ = v
v    [ drop σ ]∈ᵣ = vs (v [ σ ]∈ᵣ)
vz   [ keep σ ]∈ᵣ = vz
vs v [ keep σ ]∈ᵣ = vs (v [ σ ]∈ᵣ)

infixl 8 _[_]ₙᵣ _[_]ₙₑᵣ
mutual
  _[_]ₙᵣ : ∀ {Γ Δ A} → Nf Δ A → Ren Γ Δ → Nf Γ A
  (a , b) [ σ ]ₙᵣ = (a [ σ ]ₙᵣ) , (b [ σ ]ₙᵣ)
  lam t   [ σ ]ₙᵣ = lam (t [ keep σ ]ₙᵣ)
  ne  n   [ σ ]ₙᵣ = ne (n [ σ ]ₙₑᵣ)
  zero    [ σ ]ₙᵣ = zero
  suc n   [ σ ]ₙᵣ = suc (n [ σ ]ₙᵣ)

  _[_]ₙₑᵣ : ∀ {Γ Δ A} → Ne Δ A → Ren Γ Δ → Ne Γ A
  var v       [ σ ]ₙₑᵣ = var (v [ σ ]∈ᵣ)
  app f a     [ σ ]ₙₑᵣ = app (f [ σ ]ₙₑᵣ) (a [ σ ]ₙᵣ)
  π₁ p        [ σ ]ₙₑᵣ = π₁ (p [ σ ]ₙₑᵣ)
  π₂ p        [ σ ]ₙₑᵣ = π₂ (p [ σ ]ₙₑᵣ)
  ℕ-rec n z s [ σ ]ₙₑᵣ = ℕ-rec (n [ σ ]ₙₑᵣ) (z [ σ ]ₙᵣ) (s [ keep σ ]ₙᵣ)

-- Normalization
--------------------------------------------------------------------------------

Tmᴺ : Con → Ty → Set
Tmᴺ Γ (A ⇒ B) = ∀ {Δ} → Ren Δ Γ → Tmᴺ Δ A → Tmᴺ Δ B
Tmᴺ Γ ℕ       = Nf Γ ℕ
Tmᴺ Γ (A * B) = Tmᴺ Γ A × Tmᴺ Γ B

infixl 6 _ᴺ[_]ᵣ
_ᴺ[_]ᵣ : ∀ {A Γ Δ} → Tmᴺ Γ A → Ren Δ Γ → Tmᴺ Δ A
_ᴺ[_]ᵣ {A ⇒ B} tᴺ        σ = λ δ → tᴺ (σ ∘ᵣ δ)
_ᴺ[_]ᵣ {A * B} (aᴺ , bᴺ) σ = aᴺ ᴺ[ σ ]ᵣ , bᴺ ᴺ[ σ ]ᵣ
_ᴺ[_]ᵣ {ℕ}     (ne n)    σ = ne (n [ σ ]ₙₑᵣ)
_ᴺ[_]ᵣ {ℕ}     zero      σ = zero
_ᴺ[_]ᵣ {ℕ}     (suc n)   σ = suc (n [ σ ]ₙᵣ)

data Tmsᴺ (Γ : Con) : Con → Set where
  ∙   : Tmsᴺ Γ ∙
  _,_ : ∀ {A Δ} (σ : Tmsᴺ Γ Δ)(t : Tmᴺ Γ A) → Tmsᴺ Γ (Δ , A)

infixr 6 _ᴺ∘ᵣ_
_ᴺ∘ᵣ_ : ∀ {Γ Δ Σ} → Tmsᴺ Δ Σ → Ren Γ Δ → Tmsᴺ Γ Σ
∙       ᴺ∘ᵣ δ = ∙
(σ , t) ᴺ∘ᵣ δ = (σ ᴺ∘ᵣ δ) , t ᴺ[ δ ]ᵣ

∈↑ᴺ : ∀ {Γ Δ A} → A ∈ Γ → Tmsᴺ Δ Γ → Tmᴺ Δ A
∈↑ᴺ vz     (σ , t) = t
∈↑ᴺ (vs v) (σ , t) = ∈↑ᴺ v σ

mutual
  qᴺ : ∀ {Γ A} → Tmᴺ Γ A → Nf Γ A
  qᴺ {A = A * B} (aᴺ , bᴺ) = qᴺ aᴺ , qᴺ bᴺ
  qᴺ {A = A ⇒ B} tᴺ        = lam (qᴺ (tᴺ wk (uᴺ (var vz))))
  qᴺ {A = ℕ}     n         = n

  uᴺ : ∀ {Γ A} → Ne Γ A → Tmᴺ Γ A
  uᴺ {A = A * B} n = uᴺ (π₁ n) , uᴺ (π₂ n)
  uᴺ {A = A ⇒ B} n = λ σ aᴺ → uᴺ (app (n [ σ ]ₙₑᵣ) (qᴺ aᴺ))
  uᴺ {A = ℕ}     n = ne n

Tm↑ᴺ : ∀ {Γ Δ A} → Tm Γ A → Tmsᴺ Δ Γ → Tmᴺ Δ A
Tm↑ᴺ (var v)   = ∈↑ᴺ v
Tm↑ᴺ (lam t)   = λ σ δ aᴺ → Tm↑ᴺ t (σ ᴺ∘ᵣ δ , aᴺ)
Tm↑ᴺ (app f a) = λ σ → Tm↑ᴺ f σ idᵣ (Tm↑ᴺ a σ)

Tm↑ᴺ (a , b) = λ σ → Tm↑ᴺ a σ , Tm↑ᴺ b σ
Tm↑ᴺ (π₁ p)  = proj₁ ∘ Tm↑ᴺ p
Tm↑ᴺ (π₂ p)  = proj₂ ∘ Tm↑ᴺ p

Tm↑ᴺ zero          = λ _ → zero
Tm↑ᴺ (suc n)       = suc ∘ Tm↑ᴺ n
Tm↑ᴺ (ℕ-rec n z s) σ with Tm↑ᴺ n σ
... | ne n'  = uᴺ (ℕ-rec n' (qᴺ (Tm↑ᴺ z σ)) (qᴺ (Tm↑ᴺ s (σ ᴺ∘ᵣ wk , uᴺ (var vz)))))
... | zero   = Tm↑ᴺ z σ
... | suc n' = Tm↑ᴺ s (σ , n')

idᴺₛ : ∀ {Γ} → Tmsᴺ Γ Γ
idᴺₛ {∙}     = ∙
idᴺₛ {Γ , A} = (idᴺₛ ᴺ∘ᵣ drop idᵣ) , uᴺ (var vz)

nf : ∀ {Γ A} → Tm Γ A → Nf Γ A
nf t = qᴺ (Tm↑ᴺ t idᴺₛ)
