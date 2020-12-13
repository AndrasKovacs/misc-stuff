
{-# OPTIONS --postfix-projections --without-K #-}

module IndTyConSetModel where

open import Lib hiding (id; _∘_)

-- Theory of signatures
--------------------------------------------------------------------------------

data STy : Set where
  sort    : STy
  param⇒_ : STy → STy
  sort⇒_  : STy → STy

data SCon : Set where
  ∙   : SCon
  _▶_ : SCon → STy → SCon

data SVar : SCon → STy → Set where
  vz : ∀ {Γ A} → SVar (Γ ▶ A) A
  vs : ∀ {Γ A B} → SVar Γ A → SVar (Γ ▶ B) A

data STm (P : Set)(Γ : SCon) : STy → Set where
  var  : ∀ {A} → SVar Γ A → STm P Γ A
  appₛ : ∀ {A} → STm P Γ (sort⇒ A) → STm P Γ sort → STm P Γ A
  appₚ : ∀ {A} → STm P Γ (param⇒ A) → P → STm P Γ A

STyᴬ : STy → Set → Set → Set
STyᴬ sort       P S = S
STyᴬ (param⇒ A) P S = P → STyᴬ A P S
STyᴬ (sort⇒ A)  P S = S → STyᴬ A P S

SConᴬ : SCon → Set → Set → Set
SConᴬ ∙       P S = ⊤
SConᴬ (Γ ▶ A) P S = SConᴬ Γ P S × STyᴬ A P S

SVarᴬ : ∀ {P S Γ A} → SVar Γ A → SConᴬ Γ P S → STyᴬ A P S
SVarᴬ vz     γ = γ .₂
SVarᴬ (vs x) γ = SVarᴬ x (γ .₁)

STmᴬ : ∀ {P S Γ A} → STm P Γ A → SConᴬ Γ P S → STyᴬ A P S
STmᴬ (var x)    γ = SVarᴬ x γ
STmᴬ (appₛ t u) γ = STmᴬ t γ (STmᴬ u γ)
STmᴬ (appₚ t p) γ = STmᴬ t γ p

-- Model of TT with inductive types
--------------------------------------------------------------------------------

-- types
Ty : Set₁
Ty = Set

infixr 4 _⇒_
_⇒_ : Ty → Ty → Ty
A ⇒ B = A → B

ind : SCon → Ty → Ty
ind Ω P = STm P Ω sort

-- sCwF
Con : Set₁
Con = Set

○ : Con
○ = ⊤

infixl 3 _▷_
_▷_ : Con → Ty → Con
_▷_ = _×_

Sub : Con → Con → Set
Sub Γ Δ = Γ → Δ

Tm : Con → Ty → Set
Tm Γ A = Γ → A

ε : ∀ {Γ} → Sub Γ ○
ε = _

εη : ∀ {Γ σ} → σ ≡ ε {Γ}
εη = refl

id : ∀ {Γ} → Sub Γ Γ
id γ = γ

infixr 5 _∘_
_∘_ : ∀ {Γ Δ ξ} → Sub Δ ξ → Sub Γ Δ → Sub Γ ξ
σ ∘ δ = λ γ → σ (δ γ)

ass : ∀ {Γ Δ Θ Λ} {σ : Sub Θ Λ}{δ : Sub Δ Θ}{ν : Sub Γ Δ} → (σ ∘ δ) ∘ ν ≡ σ ∘ (δ ∘ ν)
ass = refl

idl : ∀ {Γ Δ} {σ : Sub Γ Δ} → id ∘ σ ≡ σ
idl = refl

idr : ∀ {Γ Δ} {σ : Sub Γ Δ} → σ ∘ id ≡ σ
idr = refl

infixl 4 _,ₛ_
_,ₛ_ : ∀ {Γ Δ A} → Sub Γ Δ → Tm Γ A → Sub Γ (Δ ▷ A)
σ ,ₛ t = λ γ → σ γ , t γ

p : ∀ {Γ A} → Sub (Γ ▷ A) Γ
p = ₁

q : ∀ {Γ A} → Tm (Γ ▷ A) A
q = ₂

infix 5 _[_]
_[_] : ∀ {Γ Δ A} → Tm Δ A → Sub Γ Δ → Tm Γ A
t [ σ ] = λ γ → t (σ γ)

▷β₁ : ∀ {Γ Δ A} {σ : Sub Γ Δ}{t : Tm Γ A} → p ∘ (σ ,ₛ t) ≡ σ
▷β₁ = refl

▷β₂ : ∀ {Γ Δ A} {σ : Sub Γ Δ}{t : Tm Γ A} → q [ σ ,ₛ t ] ≡ t
▷β₂ = refl

▷η : ∀ {Γ A} → (p {Γ}{A} ,ₛ q) ≡ id
▷η = refl

[id] : ∀ {Γ A} {t : Tm Γ A} → t [ id ] ≡ t
[id] = refl

[∘] : ∀ {Γ Δ Θ A} {t : Tm Θ A}{σ : Sub Δ Θ}{δ : Sub Γ Δ} → t [ σ ] [ δ ] ≡ t [ σ ∘ δ ]
[∘] = refl

-- _⇒_

lam : ∀ {Γ A B} → Tm (Γ ▷ A) B → Tm Γ (A ⇒ B)
lam t γ α = t (γ , α)

lam[] : ∀ {Γ Δ A B} {t : Tm (Δ ▷ A) B}{σ : Sub Γ Δ} → (lam t) [ σ ] ≡ lam (t [ σ ∘ p ,ₛ q ])
lam[] = refl

app : ∀ {Γ A B} → Tm Γ (A ⇒ B) → Tm Γ A → Tm Γ B
app t u γ = t γ (u γ)

⇒β : ∀ {Γ A B t u} → app (lam {Γ}{A}{B} t) u ≡ t [ id ,ₛ u ]
⇒β = refl

⇒η : ∀ {Γ A B t} → lam {Γ}{A}{B} (app (t [ p ]) q) ≡ t
⇒η = refl


-- inductive types
--------------------------------------------------------------------------------

-- internal algebras

STyᴵᴬ : STy → Ty → Ty → Ty
STyᴵᴬ = STyᴬ

SConᴵᴬ : SCon → Ty → Ty → Con
SConᴵᴬ = SConᴬ

sortᴵᴬ : ∀ {P S} → STyᴵᴬ sort P S ≡ S
sortᴵᴬ = refl

param⇒ᴵᴬ : ∀ {A P S} → STyᴵᴬ (param⇒ A) P S ≡ (P ⇒ STyᴵᴬ A P S)
param⇒ᴵᴬ = refl

sort⇒ᴵᴬ : ∀ {A P S} → STyᴵᴬ (sort⇒ A) P S ≡ (S ⇒ STyᴵᴬ A P S)
sort⇒ᴵᴬ = refl

∙ᴵᴬ : ∀ {P S} → SConᴵᴬ ∙ P S ≡ ○
∙ᴵᴬ = refl

▶ᴵᴬ : ∀ {Ω A P S} → SConᴵᴬ (Ω ▶ A) P S ≡ (SConᴵᴬ Ω P S ▷ STyᴵᴬ A P S)
▶ᴵᴬ = refl

-- constructor terms
CTm : Con → SCon → Ty → STy → Set
CTm Γ Ω P A = Γ → STm P Ω A

cvar : ∀ {Ω Γ P A} → SVar Ω A → CTm Γ Ω P A
cvar x γ = var x

cappₛ : ∀ {Ω Γ P A} → CTm Γ Ω P (sort⇒ A) → Tm Γ (ind Ω P) → CTm Γ Ω P A
cappₛ t u γ = appₛ (t γ) (u γ)

cappₚ : ∀ {Ω Γ P A} → CTm Γ Ω P (param⇒ A) → Tm Γ P → CTm Γ Ω P A
cappₚ t u γ = appₚ (t γ) (u γ)

-- constructor substitution
infix 5 _[_]C
_[_]C : ∀ {Γ Δ Ω P A} → CTm Δ Ω P A → Sub Γ Δ → CTm Γ Ω P A
t [ σ ]C = λ γ → t (σ γ)

[id]C : ∀ {Γ Ω P A}{t : CTm Γ Ω P A} → t [ id ]C ≡ t
[id]C = refl

[∘]C : ∀ {Γ Δ ξ Ω P A}{t : CTm ξ Ω P A}{σ : Sub Δ ξ}{δ : Sub Γ Δ} → t [ σ ∘ δ ]C ≡ t [ σ ]C [ δ ]C
[∘]C = refl

cvar[] : ∀ {Ω Γ Δ P A x}{σ : Sub Γ Δ} → cvar {Ω}{Δ}{P}{A} x [ σ ]C ≡ cvar x
cvar[] = refl

cappₛ[] : ∀ {Ω Γ Δ P A t u}{σ : Sub Γ Δ}
          → cappₛ {Ω} {Δ} {P} {A} t u [ σ ]C ≡ cappₛ (t [ σ ]C) (u [ σ ])
cappₛ[] = refl

cappₚ[] : ∀ {Ω Γ Δ P A t u}{σ : Sub Γ Δ}
          → cappₚ {Ω} {Δ} {P} {A} t u [ σ ]C ≡ cappₚ (t [ σ ]C) (u [ σ ])
cappₚ[] = refl

-- constructor & recursor
con : ∀ {Γ Ω P} → CTm Γ Ω P sort → Tm Γ (ind Ω P)
con t = t

con[] : ∀ {Γ Δ Ω P t}{σ : Sub Γ Δ} → con {Δ}{Ω}{P} t [ σ ] ≡ con (t [ σ ]C)
con[] = refl

rec : ∀ {Γ Ω P} → Tm Γ (ind Ω P) → ∀ S → Sub Γ (SConᴵᴬ Ω P S) → Tm Γ S
rec t S ω γ = STmᴬ (t γ) (ω γ)

rec[] : ∀ {Γ Δ Ω P t S ω}{σ : Sub Γ Δ} → rec {Δ}{Ω}{P} t S ω [ σ ] ≡ rec (t [ σ ]) S (ω ∘ σ)
rec[] = refl

-- recβ
evalCTm : ∀ {Γ Ω P A S} → CTm Γ Ω P A → Sub Γ (SConᴵᴬ Ω P S) → Tm Γ (STyᴵᴬ A P S)
evalCTm t ω γ = STmᴬ (t γ) (ω γ)

evalSVar : ∀ {Γ Ω P A S} → SVar Ω A → Sub Γ (SConᴵᴬ Ω P S) → Tm Γ (STyᴵᴬ A P S)
evalSVar x ω γ = SVarᴬ x (ω γ)

evalcvar : ∀ {Γ Ω P A S x ω} → evalCTm {Γ}{Ω}{P}{A}{S} (cvar x) ω ≡ evalSVar x ω
evalcvar = refl

evalcappₛ : ∀ {Γ Ω P A S t u ω}
            → evalCTm {Γ}{Ω}{P}{A}{S} (cappₛ t u) ω ≡ app (evalCTm t ω) (rec u S ω)
evalcappₛ = refl

evalcappₚ : ∀ {Γ Ω P A S t u ω}
            → evalCTm {Γ}{Ω}{P}{A}{S} (cappₚ t u) ω ≡ app (evalCTm t ω) u
evalcappₚ = refl

recβ : ∀ {Γ Ω P S t ω} → rec {Γ}{Ω}{P} (con t) S ω ≡ evalCTm t ω
recβ = refl
