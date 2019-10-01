
open import Lib

data STy : Set where
  ι   : STy
  ι⇒_ : STy → STy

infixl 4 _▶_
data SCon : Set where
  ∙   : SCon
  _▶_ : SCon → STy → SCon

data Ty : Set where
  conTy : SCon → Ty
  _⇒_ : Ty → Ty → Ty
infixr 3 _⇒_

data Con : Set where
  ∙   : Con
  _▶_ : Con → Ty → Con

data SVar : SCon → STy → Set where
  vz : ∀ {Δ A} → SVar (Δ ▶ A) A
  vs : ∀ {Δ A B} → SVar Δ A → SVar (Δ ▶ B) A

data Var : Con → Ty → Set where
  vz : ∀ {Γ A} → Var (Γ ▶ A) A
  vs : ∀ {Γ A B} → Var Γ A → Var (Γ ▶ B) A

data Tm (Γ : Con) : Ty → Set
data CTm (Γ : Con)(Δ : SCon) : STy → Set

data CTm Γ Δ where
  var : ∀ {A} → SVar Δ A → CTm Γ Δ A
  app : ∀ {B} → CTm Γ Δ (ι⇒ B) → Tm Γ (conTy Δ) → CTm Γ Δ B

data Sub : Con → Con → Set where
  ε    : ∀ {Γ} → Sub Γ ∙
  _,ₛ_ : ∀ {Γ Δ A} → Sub Γ Δ → Tm Γ A → Sub Γ (Δ ▶ A)
infixl 3 _,ₛ_

STyᴬ : Ty → STy → Ty
STyᴬ B ι      = B
STyᴬ B (ι⇒ A) = B ⇒ STyᴬ B A

SConᴬ : Ty → SCon → Con
SConᴬ B ∙       = ∙
SConᴬ B (Γ ▶ A) = SConᴬ B Γ ▶ STyᴬ B A

data Tm Γ where
  var : ∀ {A} → Var Γ A → Tm Γ A
  lam : ∀ {A B} → Tm (Γ ▶ A) B → Tm Γ (A ⇒ B)
  app : ∀ {A B} → Tm Γ (A ⇒ B) → Tm Γ A → Tm Γ B
  con : ∀ {Δ} → CTm Γ Δ ι → Tm Γ (conTy Δ)
  rec : ∀ Δ {B} → Sub Γ (SConᴬ B Δ ) → Tm Γ (conTy Δ) → Tm Γ B

--------------------------------------------------------------------------------

-- conversion rules
--------------------------------------------------------------------------------

data OPE : Con → Con → Set where
  ∙    : OPE ∙ ∙
  drop : ∀ {Γ Δ A} → OPE Γ Δ → OPE (Γ ▶ A) Δ
  keep : ∀ {Γ Δ A} → OPE Γ Δ → OPE (Γ ▶ A) (Δ ▶ A)

postulate
  Varₑ  : ∀ {Γ Δ A} → OPE Γ Δ → Var Δ A → Var Γ A
  Tmₑ   : ∀ {Γ Δ A} → OPE Γ Δ → Tm Δ A → Tm Γ A
  _ₛ∘ₑ_ : ∀ {Γ Δ Σ} → Sub Δ Σ → OPE Γ Δ → Sub Γ Σ
  idₑ   : ∀ {Γ} → OPE Γ Γ
  idₛ   : ∀ {Γ} → Sub Γ Γ
  Tmₛ   : ∀ {Γ Δ A} → Sub Γ Δ → Tm Δ A → Tm Γ A
infixr 4 _ₛ∘ₑ_

wk : ∀ {Γ A} → OPE (Γ ▶ A) Γ
wk = drop idₑ

STmᴬ : ∀ {Γ Δ B A} → Sub Γ (SConᴬ B Δ) → CTm Γ Δ A → Tm Γ (STyᴬ B A)
STmᴬ (σ ,ₛ t) (var vz)     = t
STmᴬ (σ ,ₛ _) (var (vs x)) = STmᴬ σ (var x)
STmᴬ σ (app t u)           = app (STmᴬ σ t) (rec _ σ u)

infix 3 _~_
data _~_ {Γ} : ∀ {A} → Tm Γ A → Tm Γ A → Set where
  λβ : ∀ {A B}{t : Tm (Γ ▶ A) B}{u} → app (lam t) u ~ Tmₛ (idₛ ,ₛ u) t
  λη : ∀ {A B}{t : Tm Γ (A ⇒ B)} → lam (app (Tmₑ wk t) (var vz)) ~ t
  conβ : ∀ {Δ B}{σ : Sub Γ (SConᴬ B Δ)}{t} → rec _ σ (con t) ~ STmᴬ σ t
  -- + congruence closure

-- std model
--------------------------------------------------------------------------------

data STm (Δ : SCon) : STy → Set where
  var : ∀ {A} → SVar Δ A → STm Δ A
  app : ∀ {B} → STm Δ (ι⇒ B) → STm Δ ι → STm Δ B

Tyᴹ : Ty → Set
Tyᴹ (conTy Δ) = STm Δ ι
Tyᴹ (A ⇒ B) = Tyᴹ A → Tyᴹ B

Conᴹ : Con → Set
Conᴹ ∙       = ⊤
Conᴹ (Γ ▶ A) = Conᴹ Γ × Tyᴹ A

CTmᴹ : ∀ {Γ Δ A} → CTm Γ Δ A → Conᴹ Γ → STm Δ A
Tmᴹ  : ∀ {Γ A} → Tm Γ A → Conᴹ Γ → Tyᴹ A
Subᴹ : ∀ {Γ Δ} → Sub Γ Δ → Conᴹ Γ → Conᴹ Δ

recᴹ : ∀ {B A Δ} → Conᴹ (SConᴬ B Δ) → STm Δ A → Tyᴹ (STyᴬ B A)
recᴹ σ (var vz)     = ₂ σ
recᴹ σ (var (vs x)) = recᴹ (₁ σ) (var x)
recᴹ σ (app t u)    = recᴹ σ t (recᴹ σ u)

Subᴹ ε        γ = tt
Subᴹ (σ ,ₛ t) γ = (Subᴹ σ γ) , Tmᴹ t γ

Tmᴹ (var vz)     γ   = ₂ γ
Tmᴹ (var (vs x)) γ   = Tmᴹ (var x) (₁ γ)
Tmᴹ (lam t)      γ α = Tmᴹ t (γ , α)
Tmᴹ (app t u)    γ   = Tmᴹ t γ (Tmᴹ u γ)
Tmᴹ (con t)      γ   = CTmᴹ t γ
Tmᴹ (rec _ σ t)  γ   = recᴹ (Subᴹ σ γ) (Tmᴹ t γ)

CTmᴹ (var x)   γ = var x
CTmᴹ (app t u) γ = app (CTmᴹ t γ) (Tmᴹ u γ)

emptySTm : ∀ {A} → STm ∙ A → ⊥
emptySTm (app t _) = emptySTm t

consistent : Tm ∙ (conTy ∙) → ⊥
consistent t = emptySTm (Tmᴹ t tt)

--------------------------------------------------------------------------------
natS : SCon
natS = ∙ ▶ ι ▶ (ι⇒ ι)

nat : Ty
nat = conTy natS

zero : ∀ {Γ} → Tm Γ nat
zero = con (var (vs vz))

suc : ∀ {Γ} → Tm Γ (nat ⇒ nat)
suc = lam (con (app (var vz) (var vz)))

plus : ∀ {Γ} → Tm Γ (nat ⇒ nat ⇒ nat)
plus = lam (rec natS (ε ,ₛ lam (var vz) ,ₛ lam (lam (app suc (app (var (vs vz)) (var vz))))) (var vz))
