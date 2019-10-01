
open import Lib

data List {i}(A : Set i) : Set i where
  ∙   : List A
  _▶_ : List A → A → List A

data Var {i A} : List {i} A → A → Set where
  vz : ∀ {xs x} → Var (xs ▶ x) x
  vs : ∀ {xs x y} → Var xs x → Var (xs ▶ y) x

data OPE {i A} : List {i} A → List A → Set where
  ∙    : OPE ∙ ∙
  drop : ∀ {xs ys x} → OPE xs ys → OPE (xs ▶ x) ys
  keep : ∀ {xs ys x} → OPE xs ys → OPE (xs ▶ x) (ys ▶ x)

--------------------------------------------------------------------------------

data Ty : Set
Con = List Ty
data Tm (Γ : Con) : Ty → Set

data STy : Set
SCon = List STy

data Sub : Con → Con → Set where
  ε    : ∀ {Γ} → Sub Γ ∙
  _,ₛ_ : ∀ {Γ Δ A} → Sub Γ Δ → Tm Γ A → Sub Γ (Δ ▶ A)
infixl 3 _,ₛ_

-- Note: embedding from CTy to Ty is trivial.
data CTm (Γ : Con)(Δ : SCon) : STy → Set

data STy where
  ι   : STy
  ι⇒_ : STy → STy
  _⇒_ : Ty → STy → STy
infix 3 ι⇒_
infixr 3 _⇒_

data Ty where
  con : SCon → Ty
  _⇒_ : Ty → Ty → Ty

data CTm Γ Δ where
  var : ∀ {A} → Var Δ A → CTm Γ Δ A
  app : ∀ {B} → CTm Γ Δ (ι⇒ B) → Tm Γ (con Δ) → CTm Γ Δ B
  app̂ : ∀ {A B} → CTm Γ Δ (A ⇒ B) → Tm Γ A → CTm Γ Δ B

STyᴬ : Ty → STy → Ty
STyᴬ B ι       = B
STyᴬ B (ι⇒ A)  = B ⇒ STyᴬ B A
STyᴬ B (A ⇒ C) = A ⇒ STyᴬ B C

SConᴬ : Ty → SCon → Con
SConᴬ B ∙       = ∙
SConᴬ B (Γ ▶ A) = SConᴬ B Γ ▶ STyᴬ B A

data Tm Γ where
  var : ∀ {A} → Var Γ A → Tm Γ A
  lam : ∀ {A B} → Tm (Γ ▶ A) B → Tm Γ (A ⇒ B)
  app : ∀ {A B} → Tm Γ (A ⇒ B) → Tm Γ A → Tm Γ B
  con : ∀ {Δ} → CTm Γ Δ ι → Tm Γ (con Δ)
  rec : ∀ {Δ B} → Sub Γ (SConᴬ B Δ) → Tm Γ (con Δ) → Tm Γ B

-- std model
--------------------------------------------------------------------------------

open import Data.Nat
open import Data.Fin

data STy' (ps : ℕ) : Set where
  ι   : STy' ps
  ι⇒_ : STy' ps → STy' ps
  _⇒_ : Fin ps → STy' ps → STy' ps

STyps : STy → List Ty
STyps ι       = ∙
STyps (ι⇒ A)  = STyps A
STyps (A ⇒ B) = STyps B ▶ A

SConps : SCon → List Ty
SConps ∙ = ∙
SConps (Γ ▶ A) = {!!}








-- data STyᴹ : Set₁ where
--   ι   : STyᴹ
--   ι⇒_ : STyᴹ → STyᴹ
--   _⇒_ : Set → STyᴹ → STyᴹ

-- data STm (Δ : List STyᴹ) (A : STyᴹ) : Set₁ where
--   var : Var Δ A → STm Δ A
--   app : STm Δ (ι⇒ A) → STm Δ ι → STm Δ A
--   app̂ : ∀ {B} → STm Δ (B ⇒ A) → B → STm Δ A

-- data STm (Δ : SCon) : STy → Set where
--   var : ∀ {A} → Var Δ A → STm Δ A
--   app : ∀ {B} → STm Δ (ι⇒ B) → STm Δ ι → STm Δ B
--   app̂ : ∀ {A B} → STm Δ (A ⇒ B) → Tyᴹ A → STm Δ B

-- Tyᴹ : Ty → Set₁
-- Tyᴹ (con Δ) = STm {!!} ι
-- Tyᴹ (A ⇒ B) = Tyᴹ A → Tyᴹ B

-- Conᴹ : Con → Set
-- Conᴹ ∙       = ⊤
-- Conᴹ (Γ ▶ A) = Conᴹ Γ × Tyᴹ A

-- CTmᴹ : ∀ {Γ Δ A} → CTm Γ Δ A → Conᴹ Γ → STm Δ A
-- Tmᴹ : ∀ {Γ A} → Tm Γ A → Conᴹ Γ → Tyᴹ A
-- Subᴹ : ∀ {Γ Δ} → Sub Γ Δ → Conᴹ Γ → Conᴹ Δ

-- recᴹ : ∀ {B A Δ} → Conᴹ (SConᴬ B Δ) → STm Δ A → Tyᴹ (STyᴬ B A)
-- recᴹ σ (var vz)     = ₂ σ
-- recᴹ σ (var (vs x)) = recᴹ (₁ σ) (var x)
-- recᴹ σ (app t u)    = recᴹ σ t (recᴹ σ u)
-- recᴹ σ (app̂ t u)    = recᴹ σ t u

-- Subᴹ ε        γ = tt
-- Subᴹ (σ ,ₛ t) γ = (Subᴹ σ γ) , Tmᴹ t γ

-- Tmᴹ (var vz)     γ   = ₂ γ
-- Tmᴹ (var (vs x)) γ   = Tmᴹ (var x) (₁ γ)
-- Tmᴹ (lam t)      γ α = Tmᴹ t (γ , α)
-- Tmᴹ (app t u)    γ   = Tmᴹ t γ (Tmᴹ u γ)
-- Tmᴹ (con t)      γ   = CTmᴹ t γ
-- Tmᴹ (rec σ t)    γ   = recᴹ (Subᴹ σ γ) (Tmᴹ t γ)

-- CTmᴹ (var x)   γ = var x
-- CTmᴹ (app t u) γ = app (CTmᴹ t γ) (Tmᴹ u γ)
-- CTmᴹ (app̂ t u) γ = app̂ (CTmᴹ t γ) (Tmᴹ u γ)

-- --------------------------------------------------------------------------------

-- -- List : Ty → Ty
-- -- List A = conTy (∙ ▶ ι ▶ (A ⇒ ι⇒ ι))

-- -- nil : ∀ {Γ A} → Tm Γ (List A)
-- -- nil = con (var (vs vz))

-- -- cons : ∀ {Γ A} → Tm Γ (A ⇒ List A ⇒ List A)
-- -- cons = lam (lam (con {!!}))
