{-# OPTIONS --rewriting #-}

open import StrictLib
open import Data.Nat
open import Data.Fin

{-# BUILTIN REWRITE _≡_ #-}

data ope : ℕ → ℕ → Set where
  ∙    : ope zero zero
  drop : ∀ {n m} → ope n m → ope (suc n) m
  keep : ∀ {n m} → ope n m → ope (suc n) (suc m)

idₑ : ∀ {n} → ope n n
idₑ {zero}  = ∙
idₑ {suc n} = keep idₑ

wk : ∀ {n} → ope (suc n) n
wk = drop idₑ

_∘ₑ_ : ∀ {m n k} → ope m k → ope n m → ope n k
σ      ∘ₑ ∙      = σ
σ      ∘ₑ drop δ = drop (σ ∘ₑ δ)
drop σ ∘ₑ keep δ = drop (σ ∘ₑ δ)
keep σ ∘ₑ keep δ = keep (σ ∘ₑ δ)

idlₑ : ∀ {Γ Δ}(σ : ope Γ Δ) → idₑ ∘ₑ σ ≡ σ
idlₑ ∙        = refl
idlₑ (drop σ) = drop & idlₑ σ
idlₑ (keep σ) = keep & idlₑ σ

idrₑ : ∀ {Γ Δ}(σ : ope Γ Δ) → σ ∘ₑ idₑ ≡ σ
idrₑ ∙        = refl
idrₑ (drop σ) = drop & idrₑ σ
idrₑ (keep σ) = keep & idrₑ σ

assₑ :
  ∀ {Γ Δ Σ Ξ}(σ : ope Σ Ξ)(δ : ope Δ Σ)(ν : ope Γ Δ)
  → (σ ∘ₑ δ) ∘ₑ ν ≡ σ ∘ₑ (δ ∘ₑ ν)
assₑ σ        δ        ∙        = refl
assₑ σ        δ        (drop ν) = drop & assₑ σ δ ν
assₑ σ        (drop δ) (keep ν) = drop & assₑ σ δ ν
assₑ (drop σ) (keep δ) (keep ν) = drop & assₑ σ δ ν
assₑ (keep σ) (keep δ) (keep ν) = keep & assₑ σ δ ν

Finₑ : ∀ {Γ Δ} → ope Γ Δ → Fin Δ → Fin Γ
Finₑ ∙        x       = x
Finₑ (drop σ) x       = suc (Finₑ σ x)
Finₑ (keep σ) zero    = zero
Finₑ (keep σ) (suc x) = suc (Finₑ σ x)

Fin-idₑ : ∀ {Γ}(x : Fin Γ) → Finₑ idₑ x ≡ x
Fin-idₑ zero    = refl
Fin-idₑ (suc x) = suc & Fin-idₑ x

Fin-∘ₑ : ∀ {Γ Δ Σ}(σ : ope Δ Σ)(δ : ope Γ Δ)(v : Fin Σ) → Finₑ (σ ∘ₑ δ) v ≡ Finₑ δ (Finₑ σ v)
Fin-∘ₑ ∙        ∙        v       = refl
Fin-∘ₑ σ        (drop δ) v       = suc & Fin-∘ₑ σ δ v
Fin-∘ₑ (drop σ) (keep δ) v       = suc & Fin-∘ₑ σ δ v
Fin-∘ₑ (keep σ) (keep δ) zero    = refl
Fin-∘ₑ (keep σ) (keep δ) (suc v) = suc & Fin-∘ₑ σ δ v

{-# REWRITE idlₑ idrₑ assₑ Fin-idₑ Fin-∘ₑ #-}

--------------------------------------------------------------------------------

infixr 2 _⇒_
data ty (n : ℕ) : Set where
  var : Fin n → ty n
  _⇒_ : ty n → ty n → ty n
  ι   : ty n

tyₑ : ∀ {n m} → ope n m → ty m → ty n
tyₑ σ (var x) = var (Finₑ σ x)
tyₑ σ (a ⇒ b) = tyₑ σ a ⇒ tyₑ σ b
tyₑ σ ι       = ι

ty-idₑ : ∀ {n} a → tyₑ {n} idₑ a ≡ a
ty-idₑ (var x) = refl
ty-idₑ (a ⇒ b) = _⇒_ & ty-idₑ a ⊗ ty-idₑ b
ty-idₑ ι       = refl

ty-∘ₑ : ∀ {n m k} σ δ a → tyₑ {k}{m} σ (tyₑ {m}{n} δ a) ≡ tyₑ (δ ∘ₑ σ) a
ty-∘ₑ σ δ (var x) = refl
ty-∘ₑ σ δ (a ⇒ b) = _⇒_ & ty-∘ₑ σ δ a ⊗ ty-∘ₑ σ δ b
ty-∘ₑ σ δ ι       = refl
{-# REWRITE ty-idₑ ty-∘ₑ #-}

--------------------------------------------------------------------------------

infixl 3 _,ₛ_
data sub (n : ℕ) : ℕ → Set where
  ε    : sub n 0
  _,ₛ_ : ∀ {m} → sub n m → ty n → sub n (suc m)

infixr 4 _ₛ∘ₑ_
_ₛ∘ₑ_ : ∀ {n m k} → sub m k → ope n m → sub n k
ε        ₛ∘ₑ δ = ε
(σ ,ₛ a) ₛ∘ₑ δ = (σ ₛ∘ₑ δ) ,ₛ tyₑ δ a

dropₛ : ∀ {n m} → sub n m → sub (suc n) m
dropₛ σ = σ ₛ∘ₑ wk

keepₛ : ∀ {n m} → sub n m → sub (suc n) (suc m)
keepₛ σ = (σ ₛ∘ₑ wk) ,ₛ (var zero)

idₛ : ∀ {n} → sub n n
idₛ {zero}  = ε
idₛ {suc n} = keepₛ idₛ

Finₛ : ∀ {n m} → sub n m → Fin m → ty n
Finₛ (σ ,ₛ t) zero    = t
Finₛ (σ ,ₛ _) (suc x) = Finₛ σ x

tyₛ : ∀ {n m} → sub n m → ty m → ty n
tyₛ σ (var x) = Finₛ σ x
tyₛ σ (a ⇒ b) = tyₛ σ a ⇒ tyₛ σ b
tyₛ σ ι       = ι

infixr 4 _ₑ∘ₛ_
_ₑ∘ₛ_ : ∀ {n m k} → ope m k → sub n m → sub n k
∙      ₑ∘ₛ δ        = δ
drop σ ₑ∘ₛ (δ ,ₛ _) = σ ₑ∘ₛ δ
keep σ ₑ∘ₛ (δ ,ₛ t) = σ ₑ∘ₛ δ ,ₛ t

⌜_⌝ᵒᵖᵉ : ∀ {Γ Δ} → ope Γ Δ → sub Γ Δ
⌜ ∙      ⌝ᵒᵖᵉ = ε
⌜ drop σ ⌝ᵒᵖᵉ = ⌜ σ ⌝ᵒᵖᵉ ₛ∘ₑ wk
⌜ keep σ ⌝ᵒᵖᵉ = keepₛ ⌜ σ ⌝ᵒᵖᵉ

assₛₑₑ :
  ∀ {Γ Δ Σ Ξ}(σ : sub Σ Ξ)(δ : ope Δ Σ)(ν : ope Γ Δ)
  → ((σ ₛ∘ₑ δ) ₛ∘ₑ ν) ≡ (σ ₛ∘ₑ (δ ∘ₑ ν))
assₛₑₑ ε        δ ν = refl
assₛₑₑ (σ ,ₛ t) δ ν = _,ₛ_ & assₛₑₑ σ δ ν ⊗ (ty-∘ₑ ν δ t ⁻¹)

assₑₛₑ :
  ∀ {Γ Δ Σ Ξ}(σ : ope Σ Ξ)(δ : sub Δ Σ)(ν : ope Γ Δ)
  → ((σ ₑ∘ₛ δ) ₛ∘ₑ ν) ≡ (σ ₑ∘ₛ (δ ₛ∘ₑ ν))
assₑₛₑ ∙        δ       ν = refl
assₑₛₑ (drop σ) (δ ,ₛ t) ν = assₑₛₑ σ δ ν
assₑₛₑ (keep σ) (δ ,ₛ t) ν = (_,ₛ tyₑ ν t) & assₑₛₑ σ δ ν

idlₑₛ : ∀ {Γ Δ}(σ : sub Γ Δ) → (idₑ ₑ∘ₛ σ) ≡ σ
idlₑₛ ε        = refl
idlₑₛ (σ ,ₛ t) = (_,ₛ t) & idlₑₛ σ

idlₛₑ : ∀ {Γ Δ}(σ : ope Γ Δ) → (idₛ ₛ∘ₑ σ) ≡ ⌜ σ ⌝ᵒᵖᵉ
idlₛₑ ∙        = refl
idlₛₑ (drop σ) =
      ((idₛ ₛ∘ₑ_) ∘ drop) & idrₑ σ ⁻¹
    ◾ assₛₑₑ idₛ σ wk ⁻¹
    ◾ dropₛ & idlₛₑ σ
idlₛₑ (keep σ) =
  (_,ₛ var zero) &
      (assₛₑₑ idₛ wk (keep σ)
    ◾ ((idₛ ₛ∘ₑ_) ∘ drop) & (idlₑ σ ◾ idrₑ σ ⁻¹)
    ◾ assₛₑₑ idₛ σ wk ⁻¹
    ◾ (_ₛ∘ₑ wk) & idlₛₑ σ )

idrₑₛ : ∀ {Γ Δ}(σ : ope Γ Δ) → (σ ₑ∘ₛ idₛ) ≡ ⌜ σ ⌝ᵒᵖᵉ
idrₑₛ ∙        = refl
idrₑₛ (drop σ) = assₑₛₑ σ idₛ wk ⁻¹ ◾ dropₛ & idrₑₛ σ
idrₑₛ (keep σ) = (_,ₛ var zero) & (assₑₛₑ σ idₛ wk ⁻¹ ◾ (_ₛ∘ₑ wk) & idrₑₛ σ)

Fin-ₑ∘ₛ : ∀ {Γ Δ Σ}(σ : ope Δ Σ)(δ : sub Γ Δ)(v : Fin Σ)
          → Finₛ δ (Finₑ σ v) ≡ Finₛ (σ ₑ∘ₛ δ) v
Fin-ₑ∘ₛ ∙        δ       v       = refl
Fin-ₑ∘ₛ (drop σ) (δ ,ₛ t) v       = Fin-ₑ∘ₛ σ δ v
Fin-ₑ∘ₛ (keep σ) (δ ,ₛ t) zero    = refl
Fin-ₑ∘ₛ (keep σ) (δ ,ₛ t) (suc v) = Fin-ₑ∘ₛ σ δ v

Fin-ₛ∘ₑ : ∀ {Γ Δ Σ}(σ : sub Δ Σ)(δ : ope Γ Δ)(v : Fin Σ)
          → Finₛ (σ ₛ∘ₑ δ) v ≡ tyₑ δ (Finₛ σ v)
Fin-ₛ∘ₑ (σ ,ₛ _) δ zero    = refl
Fin-ₛ∘ₑ (σ ,ₛ _) δ (suc v) = Fin-ₛ∘ₑ σ δ v
{-# REWRITE assₛₑₑ assₑₛₑ idlₑₛ idlₛₑ idrₑₛ Fin-ₑ∘ₛ Fin-ₛ∘ₑ #-}

ty-ₑ∘ₛ : ∀ {n m k} σ δ a → tyₛ {k}{m} σ (tyₑ {m}{n} δ a) ≡ tyₛ (δ ₑ∘ₛ σ) a
ty-ₑ∘ₛ σ δ (var x) = refl
ty-ₑ∘ₛ σ δ (a ⇒ b) = _⇒_ & ty-ₑ∘ₛ σ δ a ⊗ ty-ₑ∘ₛ σ δ b
ty-ₑ∘ₛ σ δ ι       = refl

ty-ₛ∘ₑ : ∀ {n m k} σ δ a → tyₑ {k}{m} σ (tyₛ {m}{n} δ a) ≡ tyₛ (δ ₛ∘ₑ σ) a
ty-ₛ∘ₑ σ δ (var x) = refl
ty-ₛ∘ₑ σ δ (a ⇒ b) = _⇒_ & ty-ₛ∘ₑ σ δ a ⊗ ty-ₛ∘ₑ σ δ b
ty-ₛ∘ₑ σ δ ι = refl
{-# REWRITE ty-ₑ∘ₛ ty-ₛ∘ₑ #-}

--------------------------------------------------------------------------------

data Ty (n : ℕ) : Set where
  all : Ty (suc n) → Ty n
  El  : ty n → Ty n

Tyₑ : ∀ {n m} → ope n m → Ty m → Ty n
Tyₑ σ (all A) = all (Tyₑ (keep σ) A)
Tyₑ σ (El a)  = El (tyₑ σ a)

Ty-idₑ : ∀ {n} A → Tyₑ {n} idₑ A ≡ A
Ty-idₑ (all A) = all & Ty-idₑ A
Ty-idₑ (El a)  = refl

Ty-∘ₑ : ∀ {n m k} σ δ A → Tyₑ {k}{m} σ (Tyₑ {m}{n} δ A) ≡ Tyₑ (δ ∘ₑ σ) A
Ty-∘ₑ σ δ (all A) = all & Ty-∘ₑ (keep σ) (keep δ) A
Ty-∘ₑ σ δ (El x) = refl
{-# REWRITE Ty-idₑ Ty-∘ₑ #-}

Tyₛ : ∀ {n m} → sub n m → Ty m → Ty n
Tyₛ σ (all A) = all (Tyₛ (keepₛ σ) A)
Tyₛ σ (El a)  = El (tyₛ σ a)

Ty-ₑ∘ₛ : ∀ {n m k} σ δ a → Tyₛ {k}{m} σ (Tyₑ {m}{n} δ a) ≡ Tyₛ (δ ₑ∘ₛ σ) a
Ty-ₑ∘ₛ σ δ (all A) = all & Ty-ₑ∘ₛ (keepₛ σ) (keep δ) A
Ty-ₑ∘ₛ σ δ (El x)  = refl

Ty-ₛ∘ₑ : ∀ {n m k} σ δ a → Tyₑ {k}{m} σ (Tyₛ {m}{n} δ a) ≡ Tyₛ (δ ₛ∘ₑ σ) a
Ty-ₛ∘ₑ σ δ (all A) = all & Ty-ₛ∘ₑ (keep σ) (keepₛ δ) A
Ty-ₛ∘ₑ σ δ (El x) = refl
{-# REWRITE Ty-ₑ∘ₛ Ty-ₛ∘ₑ #-}

--------------------------------------------------------------------------------

infixl 3 _▶_ _▶*
data Con : ℕ → Set where
  ∙    : Con 0
  _▶_  : ∀ {n} → Con n → Ty n → Con n
  _▶*  : ∀ {n} → Con n → Con (suc n)

data Var : ∀ {n} → Con n → Ty n → Set where
  vz  : ∀ {n Γ A} → Var {n} (Γ ▶ A) A
  vs  : ∀ {n Γ A B} → Var {n} Γ A → Var (Γ ▶ B) A
  vs* : ∀ {n Γ A} → Var {n} Γ A → Var (Γ ▶*) (Tyₑ wk A)

data Tm {n}(Γ : Con n) : Ty n → Set where
  var : ∀ {A} → Var Γ A → Tm Γ A
  lam : ∀ {a b} → Tm (Γ ▶ El a) (El b) → Tm Γ (El (a ⇒ b))
  app : ∀ {a b} → Tm Γ (El (a ⇒ b)) → Tm Γ (El a) → Tm Γ (El b)
  Lam : ∀ {A} → Tm (Γ ▶*) A → Tm Γ (all A)
  App : ∀ {A} → Tm Γ (all A) → (a : ty n) → Tm Γ (Tyₛ (idₛ ,ₛ a) A)
  Let : ∀ {A B} → Tm Γ A → Tm (Γ ▶ A) B → Tm Γ B

--------------------------------------------------------------------------------

data OPE : ∀ {n} → Con n → ∀ {m} → Con m → ope n m → Set where
  ∙     : OPE ∙ ∙ ∙
  drop  : ∀ {n m Γ Δ σ A} → OPE {n} Γ {m} Δ σ → OPE (Γ ▶ A) Δ σ
  drop* : ∀ {n m Γ Δ σ}   → OPE {n} Γ {m} Δ σ → OPE (Γ ▶*) Δ (drop σ)
  keep  : ∀ {n m Γ Δ σ A} → OPE {n} Γ {m} Δ σ → OPE (Γ ▶ Tyₑ σ A) (Δ ▶ A) σ
  keep* : ∀ {n m Γ Δ σ}   → OPE {n} Γ {m} Δ σ → OPE (Γ ▶*) (Δ ▶*) (keep σ)

opeOf : ∀ {n Γ m Δ σ} → OPE {n} Γ {m} Δ σ → ope n m
opeOf {σ = σ} _ = σ

Varₑ : ∀ {n Γ m Δ σ A} → OPE {n} Γ {m} Δ σ → Var Δ A → Var Γ (Tyₑ σ A)
Varₑ (drop σ)  x       = vs (Varₑ σ x)
Varₑ (drop* σ) x       = vs* (Varₑ σ x)
Varₑ (keep σ)  vz      = vz
Varₑ (keep σ)  (vs x)  = vs (Varₑ σ x)
Varₑ (keep* σ) (vs* x) = vs* (Varₑ σ x)

Idₑ : ∀ {n Γ} → OPE {n} Γ {n} Γ idₑ
Idₑ {Γ = ∙}     = ∙
Idₑ {Γ = Γ ▶ A} = keep Idₑ
Idₑ {Γ = Γ ▶*}  = keep* Idₑ

infixr 4 _oₑ_
_oₑ_ : ∀ {n m k Γ Δ Σ σ δ} → OPE {m} Δ {k} Σ σ → OPE {n} Γ {m} Δ δ
      → OPE Γ Σ (σ ∘ₑ δ)
σ       oₑ ∙       = σ
σ       oₑ drop  δ = drop (σ oₑ δ)
σ       oₑ drop* δ = drop* (σ oₑ δ)
drop σ  oₑ keep  δ = drop (σ oₑ δ)
keep σ  oₑ keep  δ = keep (σ oₑ δ)
drop* σ oₑ keep* δ = drop* (σ oₑ δ)
keep* σ oₑ keep* δ = keep* (σ oₑ δ)

-- Tmₑ : ∀ {n Γ m Δ σ A} → OPE {n} Γ {m} Δ σ → Tm Δ A → Tm Γ (Tyₑ σ A)
-- Tmₑ σ (var x)   = var (Varₑ σ x)
-- Tmₑ σ (lam t)   = lam (Tmₑ (keep σ) t)
-- Tmₑ σ (app t u) = app (Tmₑ σ t) (Tmₑ σ u)
-- Tmₑ σ (Lam t)   = Lam (Tmₑ (keep* σ) t)
-- Tmₑ σ (App t a) = App (Tmₑ σ t) (tyₑ (opeOf σ) a)
-- Tmₑ σ (Let t u) = Let (Tmₑ σ t) (Tmₑ (keep σ) u)

--------------------------------------------------------------------------------

data Nf {n}(Γ : Con n) : Ty n → Set
data Ne {n}(Γ : Con n) : Ty n → Set

data Nf {n} Γ where
  lam : ∀ {a b} → Nf (Γ ▶ El a) (El b) → Nf Γ (El (a ⇒ b))
  Lam : ∀ {A} → Nf (Γ ▶*) A → Nf Γ (all A)
  ne  : Ne Γ (El ι) → Nf Γ (El ι)

data Ne {n} Γ where
  var : ∀ {A} → Var Γ A → Ne Γ A
  app : ∀ {a b} → Ne Γ (El (a ⇒ b)) → Nf Γ (El a) → Ne Γ (El b)
  App : ∀ {A} → Ne Γ (all A) → (a : ty n) → Ne Γ (Tyₛ (idₛ ,ₛ a) A)

Nfₑ : ∀ {n m Γ Δ σ A} → OPE {n} Γ {m} Δ σ → Nf Δ A → Nf Γ (Tyₑ σ A)
Neₑ : ∀ {n m Γ Δ σ A} → OPE {n} Γ {m} Δ σ → Ne Δ A → Ne Γ (Tyₑ σ A)
Nfₑ σ (lam t)   = lam (Nfₑ (keep σ) t)
Nfₑ σ (Lam t)   = Lam (Nfₑ (keep* σ) t)
Nfₑ σ (ne t)    = ne (Neₑ σ t)
Neₑ σ (var x)   = var (Varₑ σ x)
Neₑ σ (app t u) = app (Neₑ σ t) (Nfₑ σ u)
Neₑ σ (App t a) = App (Neₑ σ t) (tyₑ (opeOf σ) a)

-- record conᴹ : Set₁ where
--   field
--     ! : ℕ → Set
--     ₑ : ∀ {n m} → ope n m → ! m → ! n
-- open conᴹ

-- record tyᴹ (nᴹ : conᴹ) (a : T: Set₁ where
--   field
--     ! : ∀ {n} →

record tyᴹ {n}(a : ty n) : Set₁ where
  field
    ! : ∀ {n} → Con n → Set
    ₑ : ∀ {n m Γ Δ σ} → OPE {n} Γ {m} Δ σ → ! Δ → ! Γ
    Q : ∀ {Γ} → ! Γ → Nf Γ (El a)
    U : ∀ {Γ} → Ne Γ (El a) → ! Γ
open tyᴹ

tyᴹˢ : ∀ {n}(a : ty n) → tyᴹ a
tyᴹˢ a = {!!}
