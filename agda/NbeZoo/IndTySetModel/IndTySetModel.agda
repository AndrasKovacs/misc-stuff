
{-# OPTIONS --postfix-projections --without-K #-}

module IndTySetModel where

open import Lib hiding (id; _∘_)

-- Theory of signatures: syntax & models
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

infixl 3 _,ₛₛ_
data SSub P (Γ : SCon) : SCon → Set where
  εₛ    : SSub P Γ ∙
  _,ₛₛ_ : ∀ {Δ A} → SSub P Γ Δ → STm P Γ A → SSub P Γ (Δ ▶ A)

wkSTm : ∀ {P Γ A B} → STm P Γ A → STm P (Γ ▶ B) A
wkSTm (var x)   = var (vs x)
wkSTm (appₛ t u) = appₛ (wkSTm t) (wkSTm u)
wkSTm (appₚ t x) = appₚ (wkSTm t) x

wkSSub : ∀ {P Γ Δ A} → SSub P Γ Δ → SSub P (Γ ▶ A) Δ
wkSSub εₛ         = εₛ
wkSSub (σ ,ₛₛ t) = wkSSub σ ,ₛₛ wkSTm t

Sid : ∀ {P Γ} → SSub P Γ Γ
Sid {P} {∙}     = εₛ
Sid {P} {Γ ▶ A} = wkSSub Sid ,ₛₛ var vz

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

SSubᴬ : ∀ {P S Γ Δ} → SSub P Γ Δ → SConᴬ Γ P S → SConᴬ Δ P S
SSubᴬ εₛ        γ = tt
SSubᴬ (σ ,ₛₛ t) γ = SSubᴬ σ γ , STmᴬ t γ

wkSTmᴬ : ∀ {P S Γ A B} t γ → STmᴬ {P}{S} (wkSTm {P}{Γ}{A}{B} t) γ ≡ STmᴬ t (γ .₁)
wkSTmᴬ (var x)    γ = refl
wkSTmᴬ (appₛ t u) γ = wkSTmᴬ t γ ⊗ wkSTmᴬ u γ
wkSTmᴬ (appₚ t p) γ = happly (wkSTmᴬ t γ) p

wkSSubᴬ : ∀ {P S Γ A Δ} σ γ → SSubᴬ {P}{S} (wkSSub {P}{Γ}{Δ}{A} σ) γ ≡ SSubᴬ σ (γ .₁)
wkSSubᴬ εₛ        γ = refl
wkSSubᴬ (σ ,ₛₛ t) γ = _,_ & wkSSubᴬ σ γ ⊗ wkSTmᴬ t γ

Sidᴬ : ∀ {P S Γ γ} → SSubᴬ {P}{S}{Γ} Sid γ ≡ γ
Sidᴬ {Γ = ∙}         = refl
Sidᴬ {Γ = Γ ▶ A} {γ} = (_, γ .₂) & (wkSSubᴬ Sid γ ◾ Sidᴬ)

STyᴹ : ∀(A : STy){P S₀ S₁} → (S₀ → S₁) → STyᴬ A P S₀ → STyᴬ A P S₁ → Set
STyᴹ sort       Sᴹ α₀ α₁ = Sᴹ α₀ ≡ α₁
STyᴹ (param⇒ A) Sᴹ α₀ α₁ = ∀ x → STyᴹ A Sᴹ (α₀ x) (α₁ x)
STyᴹ (sort⇒ A)  Sᴹ α₀ α₁ = ∀ x → STyᴹ A Sᴹ (α₀ x) (α₁ (Sᴹ x))

SConᴹ : ∀ (Γ : SCon){P S₀ S₁} → (S₀ → S₁) → SConᴬ Γ P S₀ → SConᴬ Γ P S₁ → Set
SConᴹ ∙       Sᴹ γ₀        γ₁        = ⊤
SConᴹ (Γ ▶ A) Sᴹ (γ₀ , α₀) (γ₁ , α₁) = SConᴹ Γ Sᴹ γ₀ γ₁ × STyᴹ A Sᴹ α₀ α₁

-- initial algebras
module _ (P : Set)(Γ : SCon) where

  sortᴵ : Set
  sortᴵ = STm P Γ sort

  STyᴵ : (A : STy) → STm P Γ A → STyᴬ A P sortᴵ
  STyᴵ sort       t = t
  STyᴵ (param⇒ A) t = λ p → STyᴵ A (appₚ t p)
  STyᴵ (sort⇒ A)  t = λ u → STyᴵ A (appₛ t u)

  SConᴵ : (Δ : SCon) → SSub P Γ Δ → SConᴬ Δ P sortᴵ
  SConᴵ ∙       ε         = tt
  SConᴵ (Δ ▶ A) (σ ,ₛₛ t) = SConᴵ Δ σ , STyᴵ A t

  -- recursors
  module _ (S : Set) (γ : SConᴬ Γ P S) where

    sortᴿ : ∀ {A} → STm P Γ A → STyᴬ A P S
    sortᴿ t = STmᴬ t γ

    STyᴿ : (A : STy)(t : STm P Γ A) → STyᴹ A sortᴿ (STyᴵ A t) (STmᴬ t γ)
    STyᴿ sort       t = refl
    STyᴿ (param⇒ A) t = λ p → STyᴿ A (appₚ t p)
    STyᴿ (sort⇒ A)  t = λ u → STyᴿ A (appₛ t u)

    SConᴿ : (Δ : SCon)(σ : SSub P Γ Δ) → SConᴹ Δ sortᴿ (SConᴵ Δ σ) (SSubᴬ σ γ)
    SConᴿ ∙       ε         = tt
    SConᴿ (Δ ▶ A) (σ ,ₛₛ t) = SConᴿ Δ σ , STyᴿ A t

constr : ∀ Γ P → SConᴬ Γ P (sortᴵ P Γ)
constr Γ P = SConᴵ P Γ Γ Sid

recurse : ∀ Γ P S (γ : SConᴬ Γ P S) → SConᴹ Γ (sortᴿ P Γ S γ) (constr Γ P) γ
recurse Γ P S γ =
  tr (SConᴹ Γ (sortᴿ P Γ S γ) (constr Γ P)) Sidᴬ (SConᴿ P Γ S γ Γ Sid)


-- Model of TT with postulated inductive types
--------------------------------------------------------------------------------

-- types

Ty : Set₁
Ty = Set

infixr 4 _⇒_
_⇒_ : Ty → Ty → Ty
A ⇒ B = A → B

infixr 4 _*_
_*_ : Ty → Ty → Ty
_*_ = _×_

Unit : Ty
Unit = ⊤

Con : Set₁
Con = Set

ind : SCon → Ty → Ty
ind Ω P = sortᴵ P Ω

-- sCwF

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

-- _*_

pair : ∀ {Γ A B} → Tm Γ A → Tm Γ B → Tm Γ (A * B)
pair t u γ = t γ , u γ

pair[] : ∀ {Γ Δ A B} {u : Tm Δ A}{v : Tm Δ B}{σ : Sub Γ Δ} → pair u v [ σ ] ≡ pair (u [ σ ]) (v [ σ ])
pair[] = refl

π₁ : ∀ {Γ A B} → Tm Γ (A × B) → Tm Γ A
π₁ t γ = ₁ (t γ)

π₁β : ∀ {Γ A B t u } → π₁ (pair {Γ}{A}{B} t u) ≡ t
π₁β = refl

π₂ : ∀ {Γ A B} → Tm Γ (A × B) → Tm Γ B
π₂ t γ = ₂ (t γ)

π₂β : ∀ {Γ A B t u } → π₂ (pair {Γ}{A}{B} t u) ≡ u
π₂β = refl

*η : ∀ {Γ A B t} → pair {Γ}{A}{B} (π₁ t) (π₂ t) ≡ t
*η = refl

-- Unit

Tt : ∀ {Γ} → Tm Γ Unit
Tt = _

Unitη : ∀ {Γ t} → Tt {Γ} ≡ t
Unitη = refl

Tt[] : ∀ {Γ Δ}{σ : Sub Γ Δ} → Tt [ σ ] ≡ Tt
Tt[] = refl

-- inductive types

STyᴵᴬ : STy → Ty → Ty → Ty
STyᴵᴬ = STyᴬ

SConᴵᴬ : SCon → Ty → Ty → Ty   -- "internal" algebras
SConᴵᴬ = SConᴬ

sortᴵᴬ : ∀ {P S} → STyᴵᴬ sort P S ≡ S
sortᴵᴬ = refl

param⇒ᴵᴬ : ∀ {A P S} → STyᴵᴬ (param⇒ A) P S ≡ (P ⇒ STyᴵᴬ A P S)
param⇒ᴵᴬ = refl

sort⇒ᴵᴬ : ∀ {A P S} → STyᴵᴬ (sort⇒ A) P S ≡ (S ⇒ STyᴵᴬ A P S)
sort⇒ᴵᴬ = refl

∙ᴵᴬ : ∀ {P S} → SConᴵᴬ ∙ P S ≡ Unit
∙ᴵᴬ = refl

▶ᴵᴬ : ∀ {Ω A P S} → SConᴵᴬ (Ω ▶ A) P S ≡ (SConᴵᴬ Ω P S * STyᴵᴬ A P S)
▶ᴵᴬ = refl

con : ∀ {Γ} Ω P → Tm Γ (SConᴵᴬ Ω P (ind Ω P))
con {Γ} Ω P γ = constr Ω P

con[] : ∀ {Γ Δ}{σ : Sub Γ Δ}{Ω P} → con Ω P [ σ ] ≡ con Ω P
con[] = refl

-- Internal homomorphisms (the equations are part of the syntax) Unlike with
-- internal algebras, this is not strictly the same as the external Tyᴹ, because
-- of the Γ dependency.
STyᴵᴹ : ∀ A {Γ P S₀ S₁} → Tm Γ (S₀ ⇒ S₁) → Tm Γ (STyᴵᴬ A P S₀) → Tm Γ (STyᴵᴬ A P S₁) → Set
STyᴵᴹ sort       Sᴹ t₀ t₁ = app Sᴹ t₀ ≡ t₁
STyᴵᴹ (param⇒ A) Sᴹ t₀ t₁ = ∀ x → STyᴵᴹ A Sᴹ (app t₀ x) (app t₁ x)
STyᴵᴹ (sort⇒ A)  Sᴹ t₀ t₁ = ∀ x → STyᴵᴹ A Sᴹ (app t₀ x) (app t₁ (app Sᴹ x))

SConᴵᴹ : ∀ (Ω : SCon){Γ P S₀ S₁} → Tm Γ (S₀ ⇒ S₁) → Tm Γ (SConᴵᴬ Ω P S₀) → Tm Γ (SConᴵᴬ Ω P S₁) → Set
SConᴵᴹ ∙       Sᴹ t₀ t₁ = ⊤
SConᴵᴹ (Ω ▶ A) Sᴹ t₀ t₁ = SConᴵᴹ Ω Sᴹ (π₁ t₀) (π₁ t₁) × STyᴵᴹ A Sᴹ (π₂ t₀) (π₂ t₁)

rec : ∀ {Γ} Ω P S → Tm Γ (SConᴵᴬ Ω P S) → Tm Γ (ind Ω P ⇒ S)
rec Ω P S t γ u = sortᴿ P Ω S (t γ) u

rec[] : ∀ {Γ Δ}{σ : Sub Γ Δ}{Ω P S t} → rec {Δ} Ω P S t [ σ ] ≡ rec Ω P S (t [ σ ])
rec[] = refl

--------------------------------------------------------------------------------
-- lemmas for generalizing homomorphisms over Γ (not part of syntax)

genSTyᴹ :
  ∀ A {Γ P S₀ S₁}(Sᴹ : Tm Γ (S₀ ⇒ S₁))
   → (t₀ : Tm Γ (STyᴬ A P S₀))
   → (t₁ : Tm Γ (STyᴬ A P S₁))
   → (∀ γ → STyᴹ A {P} (Sᴹ γ) (t₀ γ) (t₁ γ))
   → STyᴵᴹ A Sᴹ t₀ t₁
genSTyᴹ sort       Sᴹ t₀ t₁ p   = ext p
genSTyᴹ (param⇒ A) Sᴹ t₀ t₁ p x = genSTyᴹ A Sᴹ (app t₀ x) (app t₁ x)          (λ γ → p γ (x γ))
genSTyᴹ (sort⇒ A)  Sᴹ t₀ t₁ p x = genSTyᴹ A Sᴹ (app t₀ x) (app t₁ (app Sᴹ x)) (λ γ → p γ (x γ))

genSConᴹ :
  ∀ Ω {Γ P S₀ S₁}(Sᴹ : Tm Γ (S₀ ⇒ S₁))
   → (t₀ : Tm Γ (SConᴬ Ω P S₀))
   → (t₁ : Tm Γ (SConᴬ Ω P S₁))
   → (∀ γ → SConᴹ Ω {P} (Sᴹ γ) (t₀ γ) (t₁ γ))
   → SConᴵᴹ Ω Sᴹ t₀ t₁
genSConᴹ ∙       Sᴹ t₀ t₁ p = tt
genSConᴹ (Ω ▶ A) Sᴹ t₀ t₁ p = genSConᴹ Ω Sᴹ (π₁ t₀) (π₁ t₁) (λ γ → p γ .₁)
                            , genSTyᴹ  A Sᴹ (π₂ t₀) (π₂ t₁) (λ γ → p γ .₂)
--------------------------------------------------------------------------------

recβ : ∀ {Γ Ω P S ω} → SConᴵᴹ Ω (rec {Γ} Ω P S ω) (con Ω P) ω
recβ {Γ} {Ω} {P} {S} {ω} = genSConᴹ Ω (rec Ω P S ω) (con Ω P) ω (λ γ → recurse Ω P S (ω γ))
