{-# OPTIONS --postfix-projections #-}

{-
NbE for simple TT with single-sorted inductive types with external parameters.
-}

open import Lib
open import Data.Nat
open import Data.Fin
open import Data.Vec hiding (drop)
open import Level renaming (zero to lzero; suc to lsuc)

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

Varₑ : ∀ {i A Γ Δ x} → OPE Γ Δ → Var {i}{A} Δ x → Var Γ x
Varₑ (drop σ) x = vs (Varₑ σ x)
Varₑ (keep σ) vz = vz
Varₑ (keep σ) (vs x) = vs (Varₑ σ x)

idₑ : ∀ {i A}{Γ : List {i} A} → OPE Γ Γ
idₑ {Γ = ∙} = ∙
idₑ {Γ = Γ ▶ x} = keep idₑ

wk : ∀ {i A}{Γ : List {i} A}{x} → OPE (Γ ▶ x) Γ
wk = drop idₑ

infixr 4 _∘ₑ_
_∘ₑ_ : ∀ {i A xs ys zs} → OPE {i}{A} ys zs → OPE xs ys → OPE xs zs
σ      ∘ₑ ∙      = σ
σ      ∘ₑ drop δ = drop (σ ∘ₑ δ)
drop σ ∘ₑ keep δ = drop (σ ∘ₑ δ)
keep σ ∘ₑ keep δ = keep (σ ∘ₑ δ)

lookup-map :
   ∀ {i j}{A : Set i}{B : Set j}{n}(f : A → B) x (xs : Vec A n)
   → lookup (map f xs) x ≡ f (lookup xs x)
lookup-map f zero (_ ∷ xs) = refl
lookup-map f (suc x) (_ ∷ xs) = lookup-map f x xs

--------------------------------------------------------------------------------

data Ty : Set
data STy (n : ℕ) : Set
Con  = List Ty
SCon = λ n → List (STy n)

data Ty where
  con : ∀ {n} → SCon n → Vec Ty n → Ty
  _⇒_ : Ty → Ty → Ty

data STy n where
  ι   : STy n
  ι⇒_ : STy n → STy n
  _⇒̂_ : Fin n → STy n → STy n
infix 3 ι⇒_
infixr 3 _⇒̂_

STyᴬ : ∀ {n} (ps : Vec Ty n) → Ty → STy n → Ty
STyᴬ {n} ps B ι = B
STyᴬ {n} ps B (ι⇒ A) = B ⇒ STyᴬ ps B A
STyᴬ {n} ps B (p ⇒̂ A) = lookup ps p ⇒ STyᴬ ps B A

SConᴬ : ∀ {n} (ps : Vec Ty n) → Ty → SCon n → Con
SConᴬ ps B ∙       = ∙
SConᴬ ps B (Γ ▶ A) = SConᴬ ps B Γ ▶ STyᴬ ps B A

data Tm (Γ : Con) : Ty → Set
data CTm (Γ : Con){n}(Δ : SCon n)(ps : Vec Ty n)(A : STy n) : Set
data Sub : Con → Con → Set

data Sub where
  ε    : ∀ {Γ} → Sub Γ ∙
  _,ₛ_ : ∀ {Γ Δ A} → Sub Γ Δ → Tm Γ A → Sub Γ (Δ ▶ A)
infixl 3 _,ₛ_

data CTm Γ {n} Δ ps A where
  var : Var Δ A → CTm Γ Δ ps A
  app : CTm Γ Δ ps (ι⇒ A) → Tm Γ (con Δ ps) → CTm Γ Δ ps A
  app̂ : ∀ {p} → CTm Γ Δ ps (p ⇒̂ A) → Tm Γ (lookup ps p) → CTm Γ Δ ps A

data Tm Γ where
  var : ∀ {A} → Var Γ A → Tm Γ A
  lam : ∀ {A B} → Tm (Γ ▶ A) B → Tm Γ (A ⇒ B)
  app : ∀ {A B} → Tm Γ (A ⇒ B) → Tm Γ A → Tm Γ B
  con : ∀ {n Δ ps} → CTm Γ {n} Δ ps ι → Tm Γ (con Δ ps)
  rec : ∀ {n Δ ps B} → Tm Γ (con {n} Δ ps) → Sub Γ (SConᴬ ps B Δ) → Tm Γ B

module NbE where

  data Nf (Γ : Con) : Ty → Set
  data Ne (Γ : Con) : Ty → Set
  data CNf (Γ : Con){n}(Δ : SCon n)(ps : Vec Ty n)(A : STy n) : Set
  data Nfs (Γ : Con) : Con → Set

  data Nf Γ where
    lam : ∀ {A B} → Nf (Γ ▶ A) B → Nf Γ (A ⇒ B)
    con : ∀ {n Δ ps} → CNf Γ {n} Δ ps ι → Nf Γ (con Δ ps)
    ne  : ∀ {n Δ ps} → Ne Γ (con {n} Δ ps) → Nf Γ (con Δ ps)

  data Nfs Γ where
    ε    : Nfs Γ ∙
    _,ₛ_ : ∀ {Δ A} → Nfs Γ Δ → Nf Γ A → Nfs Γ (Δ ▶ A)

  data Ne Γ where
    var : ∀ {A} → Var Γ A → Ne Γ A
    app : ∀ {A B} → Ne Γ (A ⇒ B) → Nf Γ A → Ne Γ B
    rec : ∀ {n Δ ps B} → Ne Γ (con {n} Δ ps) → Nfs Γ (SConᴬ ps B Δ) → Ne Γ B

  data CNf Γ {n} Δ ps A where
    var : Var Δ A → CNf Γ Δ ps A
    app : CNf Γ Δ ps (ι⇒ A) → Nf Γ (con Δ ps) → CNf Γ Δ ps A
    app̂ : ∀ {p} → CNf Γ Δ ps (p ⇒̂ A) → Nf Γ (lookup ps p) → CNf Γ Δ ps A

  infixr 4 _Nfₛ∘ₑ_
  Nfₑ     : ∀ {Γ Δ A} → OPE Γ Δ → Nf Δ A → Nf Γ A
  Neₑ     : ∀ {Γ Δ A} → OPE Γ Δ → Ne Δ A → Ne Γ A
  CNfₑ    : ∀ {Γ Γ' n Δ ps A} → OPE Γ Γ' → CNf Γ' {n} Δ ps A → CNf Γ Δ ps A
  _Nfₛ∘ₑ_ : ∀ {Γ Δ Σ} → Nfs Δ Σ → OPE Γ Δ → Nfs Γ Σ
  Nfₑ  σ (lam t)   = lam (Nfₑ (keep σ) t)
  Nfₑ  σ (con t)   = con (CNfₑ σ t)
  Nfₑ  σ (ne t)    = ne (Neₑ σ t)
  Neₑ  σ (var x)   = var (Varₑ σ x)
  Neₑ  σ (app t u) = app (Neₑ σ t) (Nfₑ σ u)
  Neₑ  σ (rec t δ) = rec (Neₑ σ t) (δ Nfₛ∘ₑ σ)
  CNfₑ σ (var x)   = var x
  CNfₑ σ (app t u) = app (CNfₑ σ t) (Nfₑ σ u)
  CNfₑ σ (app̂ t u) = app̂ (CNfₑ σ t) (Nfₑ σ u)
  ε        Nfₛ∘ₑ δ = ε
  (σ ,ₛ x) Nfₛ∘ₑ δ = (σ Nfₛ∘ₑ δ) ,ₛ (Nfₑ δ x)

  --------------------------------------------------------------------------------

  record Kripke : Set₁ where
    field
      ! : Con → Set
      ₑ : ∀ {Γ Δ} → OPE Γ Δ → ! Δ → ! Γ
  open Kripke

  record KripkeQU (A : Ty) : Set₁ where
    field
      kr : Kripke
      q : ∀ {Γ} → kr .! Γ → Nf Γ A
      u : ∀ {Γ} → Ne Γ A → kr .! Γ
    open Kripke kr public
  open KripkeQU

  data VecKQU : ∀ {n} (As : Vec Ty n) → Set₁ where
    []  : VecKQU []
    _∷_ : ∀ {n A As} → KripkeQU A → VecKQU {n} As → VecKQU (A ∷ As)

  lookupKQU : ∀ {n ps} → VecKQU {n} ps → (p : Fin n) → KripkeQU (lookup ps p)
  lookupKQU (k ∷ ks) zero = k
  lookupKQU (k ∷ ks) (suc x) = lookupKQU ks x

  module _ {n}(Δ : SCon n){ps}(ks : VecKQU {n} ps) (Γ : Con) where
    mutual
      data conᴹ (A : STy n) : Set where
        var : Var Δ A → conᴹ A
        app : conᴹ (ι⇒ A) → conᴹ+Ne → conᴹ A
        app̂ : ∀ {p} → conᴹ (p ⇒̂ A) → lookupKQU ks p .! Γ → conᴹ A

      data conᴹ+Ne : Set where
        con : conᴹ ι          → conᴹ+Ne
        ne  : Ne Γ (con Δ ps) → conᴹ+Ne

  module _ {n}(Δ : SCon n){ps}(ks : VecKQU {n} ps) where
    conᴹₑ    : ∀ {Γ Σ A} → OPE Γ Σ → conᴹ Δ ks Σ A → conᴹ Δ ks Γ A
    conᴹ+Neₑ : ∀ {Γ Σ} → OPE Γ Σ → conᴹ+Ne Δ ks Σ → conᴹ+Ne Δ ks Γ
    conᴹₑ    σ (var x)       = var x
    conᴹₑ    σ (app t u)     = app (conᴹₑ σ t) (conᴹ+Neₑ σ u)
    conᴹₑ    σ (app̂ {p} t u) = app̂ (conᴹₑ σ t) (lookupKQU ks p .ₑ σ u)
    conᴹ+Neₑ σ (con x)       = con (conᴹₑ σ x)
    conᴹ+Neₑ σ (ne x)        = ne (Neₑ σ x)

    conᴹq : ∀ {Γ A} → conᴹ Δ ks Γ A → CNf Γ Δ ps A
    conᴹ+Neq : ∀ {Γ} → conᴹ+Ne Δ ks Γ → Nf Γ (con Δ ps)
    conᴹq    (var x)       = var x
    conᴹq    (app t u)     = app (conᴹq t) (conᴹ+Neq u)
    conᴹq    (app̂ {p} t u) = app̂ (conᴹq t) (lookupKQU ks p .q u)
    conᴹ+Neq (con x)       = con (conᴹq x)
    conᴹ+Neq (ne x)        = ne x

  Tyᴹ    : ∀ A → KripkeQU A
  VecTyᴹ : ∀ {n}(As : Vec Ty n) → VecKQU As

  Tyᴹ (con Δ ps) .kr .! Γ   = conᴹ+Ne Δ (VecTyᴹ ps) Γ
  Tyᴹ (con Δ ps) .kr .ₑ σ t = conᴹ+Neₑ _ _ σ t
  Tyᴹ (con Δ ps) .q t       = conᴹ+Neq _ _ t
  Tyᴹ (con Δ ps) .u         = ne
  Tyᴹ (A ⇒ B) .kr .! Γ      = ∀ {Δ} → OPE Δ Γ → Tyᴹ A .! Δ → Tyᴹ B .! Δ
  Tyᴹ (A ⇒ B) .kr .ₑ σ t δ  = t (σ ∘ₑ δ)
  Tyᴹ (A ⇒ B) .q t          = lam (Tyᴹ B .q (t wk (Tyᴹ A .u (var vz))))
  Tyᴹ (A ⇒ B) .u t σ α      = Tyᴹ B .u (app (Neₑ σ t) (Tyᴹ A .q α))
  VecTyᴹ []                 = []
  VecTyᴹ (A ∷ As)           = (Tyᴹ A) ∷ (VecTyᴹ As)

  Conᴹ  : Con → Kripke
  Conᴹ ∙ .! _               = ⊤
  Conᴹ ∙ .ₑ _ _             = tt
  Conᴹ (Γ ▶ A) .! Δ         = Conᴹ Γ .! Δ × Tyᴹ A .! Δ
  Conᴹ (Γ ▶ A) .ₑ σ (γ , α) = (Conᴹ Γ .ₑ σ γ) , (Tyᴹ A .ₑ σ α)

  Conᴹq : (Γ : Con) → ∀ {Δ} → Conᴹ Γ .! Δ → Nfs Δ Γ
  Conᴹq ∙       γ = ε
  Conᴹq (Γ ▶ A) γ = (Conᴹq Γ (₁ γ)) ,ₛ (Tyᴹ A .q (₂ γ))

  Varᴹ : ∀ {Γ A} → Var Γ A → ∀ {Δ} → Conᴹ Γ .! Δ → Tyᴹ A .! Δ
  Varᴹ vz     γ = ₂ γ
  Varᴹ (vs x) γ = Varᴹ x (₁ γ)

  lem : ∀ {n} ps p → lookupKQU {n} (VecTyᴹ ps) p ≡ Tyᴹ (lookup ps p)
  lem (_ ∷ ps) zero = refl
  lem (_ ∷ ps) (suc p) = lem ps p

  recᴹ :
    ∀ {n Δ ps Γ A B}
    → conᴹ {n} Δ {ps} (VecTyᴹ ps) Γ A → Conᴹ (SConᴬ ps B Δ) .! Γ → Tyᴹ (STyᴬ ps B A) .! Γ
  recᴹ (var vz)        γ = ₂ γ
  recᴹ (var (vs x))    γ = recᴹ (var x) (₁ γ)
  recᴹ (app t (con u)) γ = recᴹ t γ idₑ (recᴹ u γ)
  recᴹ {B = B} (app t (ne u)) γ = recᴹ t γ idₑ (Tyᴹ B .KripkeQU.u (rec u (Conᴹq _ γ)))
  recᴹ {ps = ps} {Γ} (app̂ {p} t u) γ = recᴹ t γ idₑ (coe ((λ x → kr x .! Γ) & lem ps p) u)

  Tmᴹ  : ∀ {Γ A} → Tm Γ A → ∀ {Δ} → Conᴹ Γ .! Δ → Tyᴹ A .! Δ
  CTmᴹ : ∀ {Γ n Δ ps A} → CTm Γ {n} Δ ps A
         → ∀ {Σ} → Conᴹ Γ .! Σ → conᴹ Δ (VecTyᴹ ps) Σ A
  Subᴹ : ∀ {Γ Δ} → Sub Γ Δ → ∀ {Σ} → Conᴹ Γ .! Σ → Conᴹ Δ .! Σ
  Tmᴹ (var x) γ    = Varᴹ x γ
  Tmᴹ (lam t) γ    = λ σ α → Tmᴹ t (Conᴹ _ .ₑ σ γ  , α)
  Tmᴹ (app t u) γ  = Tmᴹ t γ idₑ (Tmᴹ u γ)
  Tmᴹ (con t) γ    = con (CTmᴹ t γ)
  Tmᴹ (rec {B = B} t σ) γ with Tmᴹ t γ
  ... | con t' = recᴹ t' (Subᴹ σ γ)
  ... | ne  t' = Tyᴹ B .u (rec t' (Conᴹq _ (Subᴹ σ γ)))
  CTmᴹ (var x)   γ = var x
  CTmᴹ (app t u) γ = app (CTmᴹ t γ) (Tmᴹ u γ)
  CTmᴹ {ps = ps} (app̂ {p} t u) {Σ₁} γ =
    app̂ (CTmᴹ t γ) (coe ((λ x → kr x .! Σ₁) & lem ps p ⁻¹) (Tmᴹ u γ))
  Subᴹ ε        γ = tt
  Subᴹ (σ ,ₛ t) γ = (Subᴹ σ γ) , (Tmᴹ t γ)

  idᴹₛ : ∀ {Γ} → Conᴹ Γ .! Γ
  idᴹₛ {∙}     = tt
  idᴹₛ {Γ ▶ A} = (Conᴹ Γ .ₑ wk idᴹₛ) , Tyᴹ A .u (var vz)

  nf : ∀ {Γ A} → Tm Γ A → Nf Γ A
  nf {Γ}{A} t = Tyᴹ A .q (Tmᴹ t idᴹₛ)

module StdModel where

  data STm {n}(Δ : SCon n)(ps : Vec Set n) (A : STy n) : Set where
    var : Var Δ A → STm Δ ps A
    app : STm Δ ps (ι⇒ A) → STm Δ ps ι → STm Δ ps A
    app̂ : ∀ {p} → STm Δ ps (p ⇒̂ A) → lookup ps p → STm Δ ps A

  {-# TERMINATING #-}
  Tyᴹ : Ty → Set
  Tyᴹ (con Δ ps) = STm Δ (map Tyᴹ ps) ι
  Tyᴹ (A ⇒ B)    = Tyᴹ A → Tyᴹ B

  lem : ∀ {n} (ps : Vec Ty n) p → Tyᴹ (lookup ps p) ≡ lookup (map Tyᴹ ps) p
  lem (x ∷ ps) zero = refl
  lem (x ∷ ps) (suc p) = lem ps p

  Conᴹ : Con → Set
  Conᴹ ∙       = ⊤
  Conᴹ (Γ ▶ A) = Conᴹ Γ × Tyᴹ A

  recᴹ :
    ∀ {n ps Δ A B} → Conᴹ (SConᴬ ps B Δ) → STm Δ (map Tyᴹ ps) A → Tyᴹ (STyᴬ {n} ps B A)
  recᴹ γ (var vz) = ₂ γ
  recᴹ γ (var (vs x)) = recᴹ (₁ γ) (var x)
  recᴹ γ (app t u) = recᴹ γ t (recᴹ γ u)
  recᴹ {ps = ps} γ (app̂ {p} t u) = recᴹ γ t (coe (lem ps p ⁻¹) u)

  CTmᴹ : ∀ {Γ n ps Δ A} → CTm Γ {n} Δ ps A → Conᴹ Γ → STm Δ (map Tyᴹ ps) A
  Tmᴹ : ∀ {Γ A} → Tm Γ A → Conᴹ Γ → Tyᴹ A
  Subᴹ : ∀ {Γ Δ} → Sub Γ Δ → Conᴹ Γ → Conᴹ Δ

  Subᴹ ε        γ = tt
  Subᴹ (σ ,ₛ t) γ = (Subᴹ σ γ) , Tmᴹ t γ

  Tmᴹ (var vz)     γ   = ₂ γ
  Tmᴹ (var (vs x)) γ   = Tmᴹ (var x) (₁ γ)
  Tmᴹ (lam t)      γ α = Tmᴹ t (γ , α)
  Tmᴹ (app t u)    γ   = Tmᴹ t γ (Tmᴹ u γ)
  Tmᴹ (con t)      γ   = CTmᴹ t γ
  Tmᴹ (rec t σ)    γ   = recᴹ (Subᴹ σ γ) (Tmᴹ t γ)

  CTmᴹ (var x)   γ = var x
  CTmᴹ (app t u) γ = app (CTmᴹ t γ) (Tmᴹ u γ)
  CTmᴹ {ps = ps} (app̂ {p} t u) γ = app̂ (CTmᴹ t γ) (coe (lem ps p) (Tmᴹ u γ))

  emptySTm : ∀ {n ps A} → STm {n} ∙ ps A → ⊥
  emptySTm (app t _) = emptySTm t
  emptySTm (app̂ t _) = emptySTm t

  consistent : ∀ {n ps} → Tm ∙ (con {n} ∙ ps) → ⊥
  consistent t = emptySTm (Tmᴹ t tt)
