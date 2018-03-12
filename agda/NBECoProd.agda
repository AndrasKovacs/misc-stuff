-- Lesson learned : if we have coproducts without eta, we can happily normalize,
-- and we can still have eta for the usual eta-ish types

{-# OPTIONS --without-K #-}

open import Function
open import Data.Product

--------------------------------------------------------------------------------

infixr 4 _⇒_

data Ty : Set where
  ⊤   : Ty
  ⊥   : Ty
  _⇒_ : Ty → Ty → Ty
  _*_ : Ty → Ty → Ty
  _+_ : Ty → Ty → Ty

data Con : Set where
  ∙   : Con
  _,_ : Con → Ty → Con

data _∈_ (A : Ty) : Con → Set where
  vz : ∀ {Γ} → A ∈ (Γ , A)
  vs : ∀ {B Γ} → A ∈ Γ → A ∈ (Γ , B)

data Tm Γ : Ty → Set where
  var   : ∀ {A} → A ∈ Γ → Tm Γ A
  lam   : ∀ {A B} → Tm (Γ , A) B → Tm Γ (A ⇒ B)
  tt    : Tm Γ ⊤
  π₁    : ∀ {A B} → Tm Γ (A * B) → Tm Γ A
  π₂    : ∀ {A B} → Tm Γ (A * B) → Tm Γ B
  _,*_  : ∀ {A B} → Tm Γ A → Tm Γ B → Tm Γ (A * B)
  inj₁  : ∀ {A B} → Tm Γ A → Tm Γ (A + B)
  inj₂  : ∀ {A B} → Tm Γ B → Tm Γ (A + B)
  case  : ∀ {A B C} → Tm (Γ , A) C → Tm (Γ , B) C → Tm Γ (A + B) → Tm Γ C
  app   : ∀ {A B} → Tm Γ (A ⇒ B) → Tm Γ A → Tm Γ B
  ⊥-rec : ∀ {A} → Tm Γ ⊥ → Tm Γ A

--------------------------------------------------------------------------------

infixr 9 _∘ₑ_

data OPE : Con → Con → Set where
  ∙    : OPE ∙ ∙
  drop : ∀ {A Γ Δ} → OPE Γ Δ → OPE (Γ , A) Δ
  keep : ∀ {A Γ Δ} → OPE Γ Δ → OPE (Γ , A) (Δ , A)

_∘ₑ_ : ∀ {Γ Δ Σ} → OPE Δ Σ → OPE Γ Δ → OPE Γ Σ
σ      ∘ₑ ∙      = σ
σ      ∘ₑ drop δ = drop (σ ∘ₑ δ)
drop σ ∘ₑ keep δ = drop (σ ∘ₑ δ)
keep σ ∘ₑ keep δ = keep (σ ∘ₑ δ)

idₑ : ∀ {Γ} → OPE Γ Γ
idₑ {∙}     = ∙
idₑ {Γ , A} = keep idₑ

wk : ∀ {A Γ} → OPE (Γ , A) Γ
wk = drop idₑ

-- Normal forms
--------------------------------------------------------------------------------

infix 3 _∈_

mutual
  data Nf (Γ : Con) : Ty → Set where
    tt   : Nf Γ ⊤
    _,_  : ∀ {A B} → Nf Γ A → Nf Γ B → Nf Γ (A * B)
    lam  : ∀ {A B} → Nf (Γ , A) B → Nf Γ (A ⇒ B)

    ne⊥  : Ne Γ ⊥ → Nf Γ ⊥
    ne+  : ∀ {A B} → Ne Γ (A + B) → Nf Γ (A + B)
    inj₁ : ∀ {A B} → Nf Γ A → Nf Γ (A + B)
    inj₂ : ∀ {A B} → Nf Γ B → Nf Γ (A + B)

  data Ne (Γ : Con) : Ty → Set where
    var   : ∀ {A} → A ∈ Γ → Ne Γ A
    app   : ∀ {A B} → Ne Γ (A ⇒ B) → Nf Γ A → Ne Γ B
    π₁    : ∀ {A B} → Ne Γ (A * B) → Ne Γ A
    π₂    : ∀ {A B} → Ne Γ (A * B) → Ne Γ B
    case  : ∀ {A B C} → Nf (Γ , A) C → Nf (Γ , B) C → Ne Γ (A + B) → Ne Γ C
    ⊥-rec : ∀ {A} → Ne Γ ⊥ → Ne Γ A

∈ₑ : ∀ {Γ Δ A} → OPE Γ Δ → A ∈ Δ → A ∈ Γ
∈ₑ ∙        x      = x
∈ₑ (drop σ) x      = vs (∈ₑ σ x)
∈ₑ (keep σ) vz     = vz
∈ₑ (keep σ) (vs x) = vs (∈ₑ σ x)

mutual
  Nfₑ : ∀ {Γ Δ A} → OPE Γ Δ → Nf Δ A → Nf Γ A
  Nfₑ σ tt       = tt
  Nfₑ σ (a , b)  = Nfₑ σ a , Nfₑ σ b
  Nfₑ σ (lam t)  = lam (Nfₑ (keep σ) t)
  Nfₑ σ (ne⊥ n)  = ne⊥ (Neₑ σ n)
  Nfₑ σ (ne+ n)  = ne+ (Neₑ σ n)
  Nfₑ σ (inj₁ a) = inj₁ (Nfₑ σ a)
  Nfₑ σ (inj₂ b) = inj₂ (Nfₑ σ b)

  Neₑ : ∀ {Γ Δ A} → OPE Γ Δ → Ne Δ A → Ne Γ A
  Neₑ σ (var x)      = var (∈ₑ σ x)
  Neₑ σ (app t u)    = app (Neₑ σ t) (Nfₑ σ u)
  Neₑ σ (π₁ p)       = π₁ (Neₑ σ p)
  Neₑ σ (π₂ p)       = π₂ (Neₑ σ p)
  Neₑ σ (case l r t) = case (Nfₑ (keep σ) l) (Nfₑ (keep σ) r) (Neₑ σ t)
  Neₑ σ (⊥-rec n)    = ⊥-rec (Neₑ σ n)

-- Normalization
--------------------------------------------------------------------------------

data +ᴺ (A B C : Set) : Set where
  ne+  : A → +ᴺ A B C
  inj₁ : B → +ᴺ A B C
  inj₂ : C → +ᴺ A B C

Tyᴺ : Ty → Con → Set
Tyᴺ ⊤       Γ = Nf Γ ⊤
Tyᴺ ⊥       Γ = Ne Γ ⊥
Tyᴺ (A ⇒ B) Γ = ∀ {Δ} → OPE Δ Γ → Tyᴺ A Δ → Tyᴺ B Δ
Tyᴺ (A + B) Γ = +ᴺ (Ne Γ (A + B)) (Tyᴺ A Γ) (Tyᴺ B Γ)
Tyᴺ (A * B) Γ = Tyᴺ A Γ × Tyᴺ B Γ

Tyᴺₑ : ∀ {A Γ Δ} → OPE Δ Γ → Tyᴺ A Γ → Tyᴺ A Δ
Tyᴺₑ {A = ⊤}     σ tᴺ        = Nfₑ σ tᴺ
Tyᴺₑ {A = ⊥}     σ tᴺ        = Neₑ σ tᴺ
Tyᴺₑ {A = A * B} σ (aᴺ , bᴺ) = Tyᴺₑ σ aᴺ , Tyᴺₑ σ bᴺ
Tyᴺₑ {A = A ⇒ B} σ tᴺ        = λ δ aᴺ → tᴺ (σ ∘ₑ δ) aᴺ
Tyᴺₑ {A + B}     σ (ne+ n)   = ne+ (Neₑ σ n)
Tyᴺₑ {A + B}     σ (inj₁ a)  = inj₁ (Tyᴺₑ σ a)
Tyᴺₑ {A + B}     σ (inj₂ b)  = inj₂ (Tyᴺₑ σ b)

data Conᴺ : Con → Con → Set where
  ∙   : ∀ {Δ} → Conᴺ ∙ Δ
  _,_ : ∀ {A Γ Δ} → Conᴺ Γ Δ → Tyᴺ A Δ → Conᴺ (Γ , A) Δ

Conᴺₑ : ∀ {Γ Δ Σ} → OPE Σ Δ → Conᴺ Γ Δ → Conᴺ Γ Σ
Conᴺₑ σ ∙         = ∙
Conᴺₑ σ (Γᴺ , tᴺ) = Conᴺₑ σ Γᴺ , Tyᴺₑ σ tᴺ

∈ᴺ : ∀ {Γ Δ A} → A ∈ Γ → Conᴺ Γ Δ → Tyᴺ A Δ
∈ᴺ vz     (σ , t) = t
∈ᴺ (vs v) (σ , t) = ∈ᴺ v σ

mutual
  qᴺ : ∀ {Γ A} → Tyᴺ A Γ → Nf Γ A
  qᴺ {A = ⊤}     tᴺ        = tt
  qᴺ {A = ⊥}     tᴺ        = ne⊥ tᴺ
  qᴺ {A = A * B} (aᴺ , bᴺ) = qᴺ aᴺ , qᴺ bᴺ
  qᴺ {A = A ⇒ B} tᴺ        = lam (qᴺ (tᴺ (drop idₑ) (uᴺ (var vz))))
  qᴺ {A = A + B} (ne+ n)   = ne+ n
  qᴺ {A = A + B} (inj₁ a)  = inj₁ (qᴺ a)
  qᴺ {A = A + B} (inj₂ b)  = inj₂ (qᴺ b)

  uᴺ : ∀ {Γ A} → Ne Γ A → Tyᴺ A Γ
  uᴺ {A = ⊤}     n = tt
  uᴺ {A = ⊥}     n = n
  uᴺ {A = A * B} n = uᴺ (π₁ n) , uᴺ (π₂ n)
  uᴺ {A = A ⇒ B} n = λ σ aᴺ → uᴺ (app (Neₑ σ n) (qᴺ aᴺ))
  uᴺ {A = A + B} n = ne+ n

Tmᴺ : ∀ {Γ Δ A} → Tm Γ A → Conᴺ Γ Δ → Tyᴺ A Δ
Tmᴺ (var v)      = ∈ᴺ v
Tmᴺ (lam t)      = λ Γᴺ σ aᴺ → Tmᴺ t (Conᴺₑ σ Γᴺ , aᴺ)
Tmᴺ (case l r t) Γᴺ with Tmᴺ t Γᴺ
... | ne+ n   =
  uᴺ (case (qᴺ (Tmᴺ l (Conᴺₑ wk Γᴺ , uᴺ (var vz)))) (qᴺ (Tmᴺ r (Conᴺₑ wk Γᴺ , uᴺ (var vz)))) n)
... | inj₁ aᴺ = Tmᴺ l (Γᴺ , aᴺ)
... | inj₂ bᴺ = Tmᴺ r (Γᴺ , bᴺ)
Tmᴺ tt           = λ _ → tt
Tmᴺ (a ,* b)     = λ Γᴺ → Tmᴺ a Γᴺ , Tmᴺ b Γᴺ
Tmᴺ (π₁ p)       = proj₁ ∘ Tmᴺ p
Tmᴺ (π₂ p)       = proj₂ ∘ Tmᴺ p
Tmᴺ (inj₁ a)     = inj₁ ∘ Tmᴺ a
Tmᴺ (inj₂ b)     = inj₂ ∘ Tmᴺ b
Tmᴺ (app f a)    = λ Γᴺ → Tmᴺ f Γᴺ idₑ (Tmᴺ a Γᴺ)
Tmᴺ (⊥-rec t) Γᴺ = uᴺ (⊥-rec (Tmᴺ t Γᴺ))

idᴺₛ : ∀ {Γ} → Conᴺ Γ Γ
idᴺₛ {∙}     = ∙
idᴺₛ {Γ , A} = Conᴺₑ wk idᴺₛ , uᴺ (var vz)

nf : ∀ {Γ A} → Tm Γ A → Nf Γ A
nf t = qᴺ (Tmᴺ t idᴺₛ)

-- Canonicity
------------------------------------------------------------

open import Relation.Binary.PropositionalEquality
open import Data.Sum
open import Data.Empty

no-Ne : ∀ {A} → Ne ∙ A → Data.Empty.⊥
no-Ne {A} (var ())
no-Ne {A} (app t x) = no-Ne t
no-Ne {A} (π₁ t) = no-Ne t
no-Ne {A} (π₂ t) = no-Ne t
no-Ne {A} (case x x₁ t) = no-Ne t
no-Ne {A} (⊥-rec t) = no-Ne t

+-canonical : ∀ {A B}(t : Nf ∙ (A + B)) → (∃ λ t' → t ≡ inj₁ t') ⊎ (∃ λ t' → t ≡ inj₂ t')
+-canonical (ne+  n) = ⊥-elim (no-Ne n)
+-canonical (inj₁ t) = inj₁ (t , refl)
+-canonical (inj₂ t) = inj₂ (t , refl)
