
{-# OPTIONS --postfix-projections #-}

{-
NbE for simple TT + parameterized infinitary inductive types
-}

open import Lib
open import Data.Nat
open import Data.Fin
open import Data.Vec hiding (drop)
open import Data.Vec.Properties
open import Level renaming (zero to lzero; suc to lsuc)

data List {i}(A : Set i) : Set i where
  ∙   : List A
  _▶_ : List A → A → List A
infixl 3 _▶_

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

--------------------------------------------------------------------------------

data Ty : Set
data STy (n : ℕ)(m : ℕ) : Set
Con  = List Ty
SCon = λ n m → List (STy n m)

data Ty where
  con : ∀ {n} m → SCon n m → Fin m → Vec Ty n → Ty
  _⇒_ : Ty → Ty → Ty

data SU (n : ℕ)(m : ℕ) : Set where
  ι   : Fin m → SU n m               -- inductive sort
  _⇒_ : Fin n → SU n m → SU n m      -- infinitary function
infixr 3 _⇒_

data STy n m where
  El  : SU n m → STy n m
  _⇒_ : SU n m → STy n m → STy n m     -- inductive function
  _⇒̂_ : Fin n → STy n m → STy n m    -- metatheoretic function
infixr 3 _⇒̂_

SUᴬ : ∀ {n m}(ps : Vec Ty n) (ss : Vec Ty m) → SU n m → Ty
SUᴬ {n} ps ss (ι x)   = lookup ss x
SUᴬ {n} ps ss (x ⇒ a) = lookup ps x ⇒ SUᴬ ps ss a

STyᴬ : ∀ {n m} (ps : Vec Ty n)(ss : Vec Ty m) → STy n m → Ty
STyᴬ ps ss (El a)  = SUᴬ ps ss a
STyᴬ ps ss (a ⇒ C) = SUᴬ ps ss a ⇒ STyᴬ ps ss C
STyᴬ ps ss (x ⇒̂ A) = lookup ps x ⇒ STyᴬ ps ss A

SConᴬ : ∀ {n m} (ps : Vec Ty n)(ss : Vec Ty m) → SCon n m → Con
SConᴬ ps ss ∙       = ∙
SConᴬ ps ss (Γ ▶ A) = SConᴬ ps ss Γ ▶ STyᴬ ps ss A

data Tm (Γ : Con) : Ty → Set
data CTm (Γ : Con){n m}(Δ : SCon n m)(ps : Vec Ty n)(A : STy n m) : Set
data Sub : Con → Con → Set

data Sub where
  ε    : ∀ {Γ} → Sub Γ ∙
  _,ₛ_ : ∀ {Γ Δ A} → Sub Γ Δ → Tm Γ A → Sub Γ (Δ ▶ A)
infixl 3 _,ₛ_

data ope : ℕ → ℕ → Set where
  ∙    : ope zero zero
  drop : ∀ {n m} → ope n m → ope (suc n) m
  keep : ∀ {n m} → ope n m → ope (suc n) (suc m)

Finₑ : ∀ {Γ Δ} → ope Γ Δ → Fin Δ → Fin Γ
Finₑ ∙        x       = x
Finₑ (drop σ) x       = suc (Finₑ σ x)
Finₑ (keep σ) zero    = zero
Finₑ (keep σ) (suc x) = suc (Finₑ σ x)

data CTm Γ {n}{m} Δ ps A where
  var : Var Δ A → CTm Γ Δ ps A
  app : ∀ {a} → CTm Γ Δ ps (a ⇒ A) → Tm Γ (SUᴬ ps (tabulate λ x → con _ Δ x ps) a) → CTm Γ Δ ps A
  app̂ : ∀ {p} → CTm Γ Δ ps (p ⇒̂ A) → Tm Γ (lookup ps p) → CTm Γ Δ ps A

data Tm Γ where
  var : ∀ {A} → Var Γ A → Tm Γ A
  lam : ∀ {A B} → Tm (Γ ▶ A) B → Tm Γ (A ⇒ B)
  app : ∀ {A B} → Tm Γ (A ⇒ B) → Tm Γ A → Tm Γ B
  con : ∀ {n m Δ ps x} → CTm Γ {n}{m} Δ ps (El (ι x)) → Tm Γ (con _ Δ x ps)
  rec : ∀ {n m Δ ps x ss} → Tm Γ (con {n} m Δ x ps) → Sub Γ (SConᴬ ps ss Δ)
        → Tm Γ (lookup ss x)

-- Normalization
--------------------------------------------------------------------------------

data Nf (Γ : Con) : Ty → Set
data Ne (Γ : Con) : Ty → Set
data CNf (Γ : Con){n m}(Δ : SCon n m)(ps : Vec Ty n)(A : STy n m) : Set
data Nfs (Γ : Con) : Con → Set

data Nf Γ where
  lam : ∀ {A B} → Nf (Γ ▶ A) B → Nf Γ (A ⇒ B)
  con : ∀ {n m Δ ps x} → CNf Γ {n}{m} Δ ps (El (ι x)) → Nf Γ (con _ Δ x ps)
  ne  : ∀ {n m Δ ps x} → Ne Γ (con {n} m Δ x ps) → Nf Γ (con _ Δ x ps)

data Nfs Γ where
  ε    : Nfs Γ ∙
  _,ₛ_ : ∀ {Δ A} → Nfs Γ Δ → Nf Γ A → Nfs Γ (Δ ▶ A)

data Ne Γ where
  var : ∀ {A} → Var Γ A → Ne Γ A
  app : ∀ {A B} → Ne Γ (A ⇒ B) → Nf Γ A → Ne Γ B
  rec : ∀ {n m Δ ps x ss} → Ne Γ (con {n} m Δ x ps) → Nfs Γ (SConᴬ ps ss Δ)
        → Ne Γ (lookup ss x)

data CNf Γ {n} Δ ps A where
  var : Var Δ A → CNf Γ Δ ps A
  app : ∀ {a} → CNf Γ Δ ps (a ⇒ A) → Nf Γ (SUᴬ ps (tabulate λ x → con _ Δ x ps) a) → CNf Γ Δ ps A
  app̂ : ∀ {p} → CNf Γ Δ ps (p ⇒̂ A) → Nf Γ (lookup ps p) → CNf Γ Δ ps A

infixr 4 _Nfₛ∘ₑ_
Nfₑ     : ∀ {Γ Δ A} → OPE Γ Δ → Nf Δ A → Nf Γ A
Neₑ     : ∀ {Γ Δ A} → OPE Γ Δ → Ne Δ A → Ne Γ A
CNfₑ    : ∀ {Γ Γ' n m Δ ps A} → OPE Γ Γ' → CNf Γ' {n}{m} Δ ps A → CNf Γ Δ ps A
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

module _ {n}{m}(Δ : SCon n m){ps}(ks : VecKQU {n} ps) where
  data STyᴹ (A : STy n m) (Γ : Con) : Set
  data SUᴹ : (a : SU n m) → Con → Set

  data STyᴹ A Γ where
    var : Var Δ A → STyᴹ A Γ
    app : ∀ {a} → STyᴹ (a ⇒ A) Γ → SUᴹ a Γ → STyᴹ A Γ
    app̂ : ∀ {p} → STyᴹ (p ⇒̂ A) Γ → lookupKQU ks p .! Γ → STyᴹ A Γ

  data SUᴹ where
    con : ∀ {Γ} x → STyᴹ (El (ι x)) Γ → SUᴹ (ι x) Γ
    ne  : ∀ {Γ} x → Ne Γ (con _ Δ x ps) → SUᴹ (ι x) Γ
    lam : ∀ {Γ x a} → (∀ {Δ} → OPE Δ Γ → lookupKQU ks x .! Δ → SUᴹ a Δ)
                      → SUᴹ (x ⇒ a) Γ

  STyᴹₑ : ∀ {Γ Σ A} → OPE Γ Σ → STyᴹ A Σ → STyᴹ A Γ
  SUᴹₑ  : ∀ {Γ Σ a} → OPE Γ Σ → SUᴹ  a Σ → SUᴹ  a Γ
  STyᴹₑ σ (var x)       = var x
  STyᴹₑ σ (app t u)     = app (STyᴹₑ σ t) (SUᴹₑ σ u)
  STyᴹₑ σ (app̂ {x} t u) = app̂ (STyᴹₑ σ t) (lookupKQU ks x .ₑ σ u)
  SUᴹₑ  σ (con x t)     = con x (STyᴹₑ σ t)
  SUᴹₑ  σ (ne x t)      = ne x (Neₑ σ t)
  SUᴹₑ  σ (lam t)       = lam (λ δ → t (σ ∘ₑ δ))

  STyᴹq : ∀ {A Γ} → STyᴹ A Γ → CNf Γ Δ ps A
  SUᴹq : ∀ {a Γ} → SUᴹ a Γ → Nf Γ (SUᴬ ps (tabulate λ x → con _ Δ x ps) a)
  STyᴹq (var x)            = var x
  STyᴹq (app t u)          = app (STyᴹq t) (SUᴹq u)
  STyᴹq (app̂ {x} t u)      = app̂ (STyᴹq t) (lookupKQU ks x .q u)
  SUᴹq  (con x t)          = tr (Nf _) (lookup∘tabulate _ x ⁻¹) (Nf.con (STyᴹq t))
  SUᴹq  (ne x t)           = tr (Nf _) (lookup∘tabulate _ x ⁻¹) (Nf.ne t)
  SUᴹq  (lam {_}{x} {a} t) = lam (SUᴹq {a} (t wk (lookupKQU ks x .u (var vz))))

Tyᴹ    : ∀ A → KripkeQU A
VecTyᴹ : ∀ {n}(As : Vec Ty n) → VecKQU As
Tyᴹ (con _ Δ x ps) .kr .!     = SUᴹ Δ (VecTyᴹ ps) (ι x)
Tyᴹ (con _ Δ x ps) .kr .ₑ     = SUᴹₑ _ _
Tyᴹ (con _ Δ x ps) .q         = tr (Nf _) (lookup∘tabulate _ x) ∘ (SUᴹq _ _)
Tyᴹ (con _ Δ x ps) .u         = SUᴹ.ne x
Tyᴹ (A ⇒ B) .kr .! Γ        = ∀ {Δ} → OPE Δ Γ → Tyᴹ A .! Δ → Tyᴹ B .! Δ
Tyᴹ (A ⇒ B) .kr .ₑ σ t δ    = t (σ ∘ₑ δ)
Tyᴹ (A ⇒ B) .q t            = lam (Tyᴹ B .q (t wk (Tyᴹ A .u (var vz))))
Tyᴹ (A ⇒ B) .u t σ α        = Tyᴹ B .u (app (Neₑ σ t) (Tyᴹ A .q α))
VecTyᴹ []                   = []
VecTyᴹ (A ∷ As)             = (Tyᴹ A) ∷ (VecTyᴹ As)

Conᴹ  : Con → Kripke
Conᴹ ∙ .! _               = ⊤
Conᴹ ∙ .ₑ _ _             = tt
Conᴹ (Γ ▶ A) .! Δ         = Conᴹ Γ .! Δ × Tyᴹ A .! Δ
Conᴹ (Γ ▶ A) .ₑ σ (γ , α) = (Conᴹ Γ .ₑ σ γ) , (Tyᴹ A .ₑ σ α)

Conᴹq : (Γ : Con) → ∀ {Δ} → Conᴹ Γ .! Δ → Nfs Δ Γ
Conᴹq ∙       γ = ε
Conᴹq (Γ ▶ A) γ = (Conᴹq Γ (₁ γ)) ,ₛ (Tyᴹ A .q (₂ γ))

lkup→ :
  ∀ {n}(ps : Vec Ty n){x Γ}
  → Tyᴹ (lookup ps x) .! Γ → lookupKQU (VecTyᴹ ps) x .! Γ
lkup→ (x ∷ ps) {zero}   t = t
lkup→ (x ∷ ps) {suc x₁} t = lkup→ ps t

lkup← :
  ∀ {n}(ps : Vec Ty n){x Γ}
  → lookupKQU (VecTyᴹ ps) x .! Γ → Tyᴹ (lookup ps x) .! Γ
lkup← (x ∷ ps) {zero} t = t
lkup← (x₁ ∷ ps) {suc x} t = lkup← ps t

recSTy :
  ∀ {n m Δ ps Γ A ss}
  → STyᴹ {n}{m} Δ {ps} (VecTyᴹ ps) A Γ → Conᴹ (SConᴬ ps ss Δ) .! Γ → Tyᴹ (STyᴬ ps ss A) .! Γ
recSU :
  ∀ {n m Δ ps Γ a ss}
  → SUᴹ {n}{m} Δ {ps} (VecTyᴹ ps) a Γ → Conᴹ (SConᴬ ps ss Δ) .! Γ → Tyᴹ (SUᴬ ps ss a) .! Γ
recSTy (var vz)     γ = ₂ γ
recSTy (var (vs x)) γ = recSTy (var x) (₁ γ)
recSTy (app t u)    γ = recSTy t γ idₑ (recSU u γ)
recSTy {ps = ps} {Γ} (app̂ {p} t u) γ = recSTy t γ idₑ (lkup← ps u)
recSU (con x t) γ = recSTy t γ
recSU {ss = ss} (ne x t) γ = Tyᴹ (lookup ss x) .u (rec t (Conᴹq _ γ))
recSU {Δ = Δ}{ps}{ss = ss} (lam t) γ =
  λ σ α → recSU (t σ (lkup→ ps α)) (Conᴹ (SConᴬ ps ss Δ) .ₑ σ γ)

unrecSU :
  ∀ {n m ps Δ a Γ}
  → Tyᴹ (SUᴬ {n}{m} ps (tabulate λ x → con _ Δ x ps) a) .! Γ → SUᴹ Δ (VecTyᴹ ps) a Γ
unrecSU {n} {m} {ps} {Δ} {ι x} {Γ} t =
  coe ((λ x → kr (Tyᴹ x) .! Γ) & lookup∘tabulate (λ x₁ → Ty.con _ Δ x₁ ps) x) t
unrecSU {_}{_}{ps}{a = x ⇒ a} t = lam (λ σ α → unrecSU (t σ (lkup← ps α)))

Tmᴹ  : ∀ {Γ A} → Tm Γ A → ∀ {Δ} → Conᴹ Γ .! Δ → Tyᴹ A .! Δ
CTmᴹ : ∀ {Γ n m Δ ps A} → CTm Γ {n}{m} Δ ps A
       → ∀ {Σ} → Conᴹ Γ .! Σ → STyᴹ Δ (VecTyᴹ ps) A Σ
Subᴹ : ∀ {Γ Δ} → Sub Γ Δ → ∀ {Σ} → Conᴹ Γ .! Σ → Conᴹ Δ .! Σ
Tmᴹ (var vz)     γ = ₂ γ
Tmᴹ (var (vs x)) γ = Tmᴹ (var x) (₁ γ)
Tmᴹ (lam t)      γ = λ σ α → Tmᴹ t (Conᴹ _ .ₑ σ γ  , α)
Tmᴹ (app t u)    γ = Tmᴹ t γ idₑ (Tmᴹ u γ)
Tmᴹ (con t)      γ = con _ (CTmᴹ t γ)
Tmᴹ (rec t σ)    γ = recSU (Tmᴹ t γ) (Subᴹ σ γ)
CTmᴹ (var x)   γ = var x
CTmᴹ (app t u) γ = app (CTmᴹ t γ) (unrecSU (Tmᴹ u γ))
CTmᴹ {ps = ps} (app̂ t u) γ = app̂ (CTmᴹ t γ) (lkup→ ps (Tmᴹ u γ))
Subᴹ ε        γ = tt
Subᴹ (σ ,ₛ t) γ = (Subᴹ σ γ) , (Tmᴹ t γ)

idᴹₛ : ∀ {Γ} → Conᴹ Γ .! Γ
idᴹₛ {∙}     = tt
idᴹₛ {Γ ▶ A} = (Conᴹ Γ .ₑ wk idᴹₛ) , Tyᴹ A .u (var vz)

nf : ∀ {Γ A} → Tm Γ A → Nf Γ A
nf {Γ}{A} t = Tyᴹ A .q (Tmᴹ t idᴹₛ)

-- examples
--------------------------------------------------------------------------------

v₀ : ∀ {i}{A : Set i}{As : List A}{x : A} → Var (As ▶ x) x
v₀ = vz

v₁ : ∀ {i}{A : Set i}{xs : List A}{x y : A} → Var (xs ▶ x ▶ y) x
v₁ = vs vz

v₃ : ∀ {i}{A : Set i}{xs : List A}{x y z : A} → Var (xs ▶ x ▶ y ▶ z) x
v₃ = vs (vs vz)

v₄ : ∀ {i}{A : Set i}{xs : List A}{a b c d} → Var (xs ▶ a ▶ b ▶ c ▶ d) a
v₄ = vs (vs (vs vz))

Nat : Ty
Nat = con 1 (∙ ▶ El (ι zero) ▶ (ι zero ⇒ El (ι zero))) zero []

z : ∀ {Γ} → Tm Γ Nat
z = con (var v₁)

s : ∀ {Γ} → Tm Γ Nat → Tm Γ Nat
s n = con (app (var v₀) n)

-- plus : ∀ {Γ} → Tm Γ Nat → Tm Γ Nat → Tm Γ Nat
-- plus a b = rec a (ε ,ₛ b ,ₛ lam (s (var v₀)))

-- mul : ∀ {Γ} → Tm Γ (Nat ⇒ Nat ⇒ Nat)
-- mul = lam (lam (rec (var v₁) (ε ,ₛ z ,ₛ lam (plus (var v₁) (var v₀)))))

-- five : ∀ {Γ} → Tm Γ Nat
-- five = s (s (s (s (s z))))

-- ten : ∀ {Γ} → Tm Γ Nat
-- ten = app (app mul five) (s (s z))

-- hundred : ∀ {Γ} → Tm Γ Nat
-- hundred = app (app mul ten) ten

-- list : Ty → Ty
-- list A = con (∙ ▶ El ι ▶ (zero ⇒̂ ι ⇒ El ι)) (A ∷ [])

-- nil : ∀ {Γ A} → Tm Γ (list A)
-- nil = con (var v₁)

-- cons : ∀ {Γ A} → Tm Γ A → Tm Γ (list A) → Tm Γ (list A)
-- cons x xs = con (app (app̂ (var v₀) x) xs)

-- -- Nat-branching tree
-- Tree : Ty
-- Tree = con (∙ ▶ El ι ▶ ((zero ⇒ ι) ⇒ El ι)) (Nat ∷ [])

-- leaf : ∀ {Γ} → Tm Γ Tree
-- leaf = con (var v₁)

-- node : ∀ {Γ} → Tm Γ (Nat ⇒ Tree) → Tm Γ Tree
-- node t = con (app (var v₀) t)
