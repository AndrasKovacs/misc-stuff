
-- Lesson learned : if we have coproducts without eta, we can happily normalize,
-- and we can still have eta for the usual eta-ish types

{-# OPTIONS --without-K #-}

open import Function
open import Data.Product

-- Syntax
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

-- Renaming
--------------------------------------------------------------------------------

infixr 9 _∘ᵣ_

data Ren : Con → Con → Set where
  ∙    : Ren ∙ ∙
  drop : ∀ {A Γ Δ} → Ren Γ Δ → Ren (Γ , A) Δ
  keep : ∀ {A Γ Δ} → Ren Γ Δ → Ren (Γ , A) (Δ , A)

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

infix 3 _∈_
infixl 7 _$ₙ_
infixl 8 _[_]ₙᵣ _[_]ₙₑᵣ

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
    var  : ∀ {A} → A ∈ Γ → Ne Γ A
    _$ₙ_ : ∀ {A B} → Ne Γ (A ⇒ B) → Nf Γ A → Ne Γ B
    π₁   : ∀ {A B} → Ne Γ (A * B) → Ne Γ A
    π₂   : ∀ {A B} → Ne Γ (A * B) → Ne Γ B
    case : ∀ {A B C} → Nf (Γ , A) C → Nf (Γ , B) C → Ne Γ (A + B) → Ne Γ C

_[_]∈ᵣ : ∀ {Γ Δ A} → A ∈ Δ → Ren Γ Δ → A ∈ Γ
v    [ ∙      ]∈ᵣ = v
v    [ drop σ ]∈ᵣ = vs (v [ σ ]∈ᵣ)
vz   [ keep σ ]∈ᵣ = vz
vs v [ keep σ ]∈ᵣ = vs (v [ σ ]∈ᵣ)

mutual
  _[_]ₙᵣ : ∀ {Γ Δ A} → Nf Δ A → Ren Γ Δ → Nf Γ A
  tt      [ σ ]ₙᵣ = tt  
  (a , b) [ σ ]ₙᵣ = (a [ σ ]ₙᵣ) , (b [ σ ]ₙᵣ)
  lam t   [ σ ]ₙᵣ = lam (t [ keep σ ]ₙᵣ)
  ne⊥ n   [ σ ]ₙᵣ = ne⊥ (n [ σ ]ₙₑᵣ)
  ne+ n   [ σ ]ₙᵣ = ne+ (n [ σ ]ₙₑᵣ)
  inj₁ a  [ σ ]ₙᵣ = inj₁ (a [ σ ]ₙᵣ)
  inj₂ b  [ σ ]ₙᵣ = inj₂ (b [ σ ]ₙᵣ)

  _[_]ₙₑᵣ : ∀ {Γ Δ A} → Ne Δ A → Ren Γ Δ → Ne Γ A
  var v      [ σ ]ₙₑᵣ = var (v [ σ ]∈ᵣ)
  (f $ₙ a)   [ σ ]ₙₑᵣ = f [ σ ]ₙₑᵣ $ₙ a [ σ ]ₙᵣ
  (π₁ p)     [ σ ]ₙₑᵣ = π₁ (p [ σ ]ₙₑᵣ)
  (π₂ p)     [ σ ]ₙₑᵣ = π₂ (p [ σ ]ₙₑᵣ)
  case l r t [ σ ]ₙₑᵣ = case (l [ keep σ ]ₙᵣ) (r [ keep σ ]ₙᵣ) (t [ σ ]ₙₑᵣ)

-- Normalization
--------------------------------------------------------------------------------

data +ᴺ (A B C : Set) : Set where
  ne+  : A → +ᴺ A B C
  inj₁ : B → +ᴺ A B C
  inj₂ : C → +ᴺ A B C
  
Tmᴺ : Con → Ty → Set
Tmᴺ Γ ⊤       = Nf Γ ⊤
Tmᴺ Γ ⊥       = Ne Γ ⊥
Tmᴺ Γ (A ⇒ B) = ∀ {Δ} → Ren Δ Γ → Tmᴺ Δ A → Tmᴺ Δ B
Tmᴺ Γ (A + B) = +ᴺ (Ne Γ (A + B)) (Tmᴺ Γ A) (Tmᴺ Γ B)
Tmᴺ Γ (A * B) = Tmᴺ Γ A × Tmᴺ Γ B

infixl 6 _ᴺ[_]ᵣ
_ᴺ[_]ᵣ : ∀ {A Γ Δ} → Tmᴺ Γ A → Ren Δ Γ → Tmᴺ Δ A
_ᴺ[_]ᵣ {A = ⊤}     tᴺ        σ = tt
_ᴺ[_]ᵣ {A = ⊥}     tᴺ        σ = tᴺ [ σ ]ₙₑᵣ
_ᴺ[_]ᵣ {A = A * B} (aᴺ , bᴺ) σ = (aᴺ ᴺ[ σ ]ᵣ) , (bᴺ ᴺ[ σ ]ᵣ)
_ᴺ[_]ᵣ {A = A ⇒ B} tᴺ        σ = λ δ → tᴺ (σ ∘ᵣ δ)
_ᴺ[_]ᵣ {A + B}     (ne+ n)   σ = ne+ (n [ σ ]ₙₑᵣ)
_ᴺ[_]ᵣ {A + B}     (inj₁ a)  σ = inj₁ (a ᴺ[ σ ]ᵣ)
_ᴺ[_]ᵣ {A + B}     (inj₂ b)  σ = inj₂ (b ᴺ[ σ ]ᵣ)

data Tmsᴺ (Γ : Con) : Con → Set where
  ∙   : Tmsᴺ Γ ∙
  _,_ : ∀ {A Δ} (σ : Tmsᴺ Γ Δ)(t : Tmᴺ Γ A) → Tmsᴺ Γ (Δ , A)

infixr 6 _ᴺ∘ᵣ_
_ᴺ∘ᵣ_ : ∀ {Γ Δ Σ} → Tmsᴺ Δ Σ → Ren Γ Δ → Tmsᴺ Γ Σ
∙       ᴺ∘ᵣ δ = ∙
_,_ {A} σ t ᴺ∘ᵣ δ = (σ ᴺ∘ᵣ δ) , _ᴺ[_]ᵣ {A = A} t δ

∈↑ᴺ : ∀ {Γ Δ A} → A ∈ Γ → Tmsᴺ Δ Γ → Tmᴺ Δ A
∈↑ᴺ vz     (σ , t) = t
∈↑ᴺ (vs v) (σ , t) = ∈↑ᴺ v σ

mutual
  qᴺ : ∀ {Γ A} → Tmᴺ Γ A → Nf Γ A
  qᴺ {A = ⊤}     tᴺ        = tt
  qᴺ {A = ⊥}     tᴺ        = ne⊥ tᴺ
  qᴺ {A = A * B} (aᴺ , bᴺ) = qᴺ aᴺ , qᴺ bᴺ
  qᴺ {A = A ⇒ B} tᴺ        = lam (qᴺ (tᴺ (drop idᵣ) (uᴺ (var vz))))
  qᴺ {A = A + B} (ne+ n)   = ne+ n
  qᴺ {A = A + B} (inj₁ a)  = inj₁ (qᴺ a)
  qᴺ {A = A + B} (inj₂ b)  = inj₂ (qᴺ b)

  uᴺ : ∀ {Γ A} → Ne Γ A → Tmᴺ Γ A
  uᴺ {A = ⊤}     n = tt
  uᴺ {A = ⊥}     n = n
  uᴺ {A = A * B} n = uᴺ (π₁ n) , uᴺ (π₂ n)
  uᴺ {A = A ⇒ B} n = λ σ aᴺ → uᴺ (n [ σ ]ₙₑᵣ $ₙ qᴺ aᴺ)
  uᴺ {A = A + B} n = ne+ n

Tm↑ᴺ : ∀ {Γ Δ A} → Tm Γ A → Tmsᴺ Δ Γ → Tmᴺ Δ A
Tm↑ᴺ (var v)      = ∈↑ᴺ v
Tm↑ᴺ (lam t)      = λ σ δ aᴺ → Tm↑ᴺ t (σ ᴺ∘ᵣ δ , aᴺ)
Tm↑ᴺ (case l r t) σ with Tm↑ᴺ t σ
... | ne+ n   = uᴺ (case (qᴺ (Tm↑ᴺ l (σ ᴺ∘ᵣ wk , uᴺ (var vz)))) (qᴺ (Tm↑ᴺ r (σ ᴺ∘ᵣ wk , uᴺ (var vz)))) n)
... | inj₁ aᴺ = Tm↑ᴺ l (σ , aᴺ)
... | inj₂ bᴺ = Tm↑ᴺ r (σ , bᴺ)
Tm↑ᴺ tt           = λ _ → tt
Tm↑ᴺ (a ,* b)     = λ σ → Tm↑ᴺ a σ , Tm↑ᴺ b σ
Tm↑ᴺ (π₁ p)       = proj₁ ∘ Tm↑ᴺ p
Tm↑ᴺ (π₂ p)       = proj₂ ∘ Tm↑ᴺ p
Tm↑ᴺ (inj₁ a)     = inj₁ ∘ Tm↑ᴺ a
Tm↑ᴺ (inj₂ b)     = inj₂ ∘ Tm↑ᴺ b
Tm↑ᴺ (app f a)    = λ σ → Tm↑ᴺ f σ idᵣ (Tm↑ᴺ a σ)

idᴺₛ : ∀ {Γ} → Tmsᴺ Γ Γ
idᴺₛ {∙}     = ∙
idᴺₛ {Γ , A} = (idᴺₛ ᴺ∘ᵣ drop idᵣ) , uᴺ (var vz) 

nf : ∀ {Γ A} → Tm Γ A → Nf Γ A
nf t = qᴺ (Tm↑ᴺ t idᴺₛ)

