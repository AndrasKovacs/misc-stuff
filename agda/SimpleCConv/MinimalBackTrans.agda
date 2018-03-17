
module MinimalBackTrans where

open import Lib

infixr 4 _⇒_
infixr 4 _▶_
infixr 5 _*_

data Ty : Set where
  𝔹   : Ty
  _*_ _⇒_ : Ty → Ty → Ty

data Con : Set where
  ∙   : Con
  _▶_ : Con → Ty → Con

data _∈_ (A : Ty) : Con → Set where
  vz : ∀ {Γ} → A ∈ (Γ ▶ A)
  vs : ∀ {B Γ} → A ∈ Γ → A ∈ (Γ ▶ B)

data Tm Γ : Ty → Set where
  true false : Tm Γ 𝔹
  π₁   : ∀ {A B} → Tm Γ (A * B) → Tm Γ A
  π₂   : ∀ {A B} → Tm Γ (A * B) → Tm Γ B
  _,_  : ∀ {A B} → Tm Γ A → Tm Γ B → Tm Γ (A * B)
  if   : ∀ {A} → Tm Γ 𝔹 → Tm Γ A → Tm Γ A → Tm Γ A
  var  : ∀ {A} → A ∈ Γ → Tm Γ A
  lam  : ∀ {A B} → Tm (Γ ▶ A) B → Tm Γ (A ⇒ B)
  app  : ∀ {A B} → Tm Γ (A ⇒ B) → Tm Γ A → Tm Γ B

--------------------------------------------------------------------------------

data Ty' : Ty → Set where
  𝔹   : Ty' 𝔹
  _⇒_ : ∀ {A B} → Ty' A → Ty' B → Ty' (A ⇒ B)

data Con' : Con → Set where
  ∙ : Con' ∙
  _▶_ : ∀ {Γ A} → Con' Γ → Ty' A → Con' (Γ ▶ A)

data Tm' {Γ} : ∀ {A} → Tm Γ A → Set where
  true  : Tm' true
  false : Tm' false
  var   : ∀ {A}(x : A ∈ Γ) → Ty' A → Tm' (var x)
  if    : ∀ {A}{t u v} → Tm' t → Tm' {Γ}{A} u → Tm' v → Tm' (if t u v)
  lam   : ∀ {A B}{t : Tm (Γ ▶ A) B} → Tm' t → Tm' (lam t)
  app   : ∀ {A B}{t : Tm Γ (A ⇒ B)}{u : Tm Γ A} → Tm' t → Tm' u → Tm' (app t u)

-- Order-preserving embedding
data OPE : Con → Con → Set where
  ∙    : OPE ∙ ∙
  drop : ∀ {A Γ Δ} → OPE Γ Δ → OPE (Γ ▶ A) Δ
  keep : ∀ {A Γ Δ} → OPE Γ Δ → OPE (Γ ▶ A) (Δ ▶ A)

-- OPE is a category
idₑ : ∀ {Γ} → OPE Γ Γ
idₑ {∙}     = ∙
idₑ {Γ ▶ A} = keep (idₑ {Γ})

wk : ∀ {A Γ} → OPE (Γ ▶ A) Γ
wk = drop idₑ

_∘ₑ_ : ∀ {Γ Δ Σ} → OPE Δ Σ → OPE Γ Δ → OPE Γ Σ
σ      ∘ₑ ∙      = σ
σ      ∘ₑ drop δ = drop (σ ∘ₑ δ)
drop σ ∘ₑ keep δ = drop (σ ∘ₑ δ)
keep σ ∘ₑ keep δ = keep (σ ∘ₑ δ)

∈ₑ : ∀ {A Γ Δ} → OPE Γ Δ → A ∈ Δ → A ∈ Γ
∈ₑ ∙        v      = v
∈ₑ (drop σ) v      = vs (∈ₑ σ v)
∈ₑ (keep σ) vz     = vz
∈ₑ (keep σ) (vs v) = vs (∈ₑ σ v)

Tmₑ : ∀ {A Γ Δ} → OPE Γ Δ → Tm Δ A → Tm Γ A
Tmₑ σ (t , u)    = Tmₑ σ t , Tmₑ σ u
Tmₑ σ (π₁ t)     = π₁ (Tmₑ σ t)
Tmₑ σ (π₂ t)     = π₂ (Tmₑ σ t)
Tmₑ σ (if t u v) = if (Tmₑ σ t) (Tmₑ σ u) (Tmₑ σ v)
Tmₑ σ false      = false
Tmₑ σ true       = true
Tmₑ σ (var v)    = var (∈ₑ σ v)
Tmₑ σ (lam t)    = lam (Tmₑ (keep σ) t)
Tmₑ σ (app f a)  = app (Tmₑ σ f) (Tmₑ σ a)

mutual
  data Nf (Γ : Con) : Ty → Set where
    ne    : ∀ {A} → Ne Γ A → Nf Γ A
    lam   : ∀ {A B} → Nf (Γ ▶ A) B → Nf Γ (A ⇒ B)
    _,_   : ∀ {A B} → Nf Γ A → Nf Γ B → Nf Γ (A * B)
    true  : Nf Γ 𝔹
    false : Nf Γ 𝔹

  data Ne (Γ : Con) : Ty → Set where
    var  : ∀ {A} → A ∈ Γ → Ne Γ A
    app  : ∀ {A B} → Ne Γ (A ⇒ B) → Nf Γ A → Ne Γ B
    if   : ∀ {A} → Ne Γ 𝔹 → Nf Γ A → Nf Γ A → Ne Γ A
    π₁   : ∀ {A B} → Ne Γ (A * B) → Ne Γ A
    π₂   : ∀ {A B} → Ne Γ (A * B) → Ne Γ B

mutual
  Nfₑ : ∀ {Γ Δ A} → OPE Γ Δ → Nf Δ A → Nf Γ A
  Nfₑ σ (ne x) = ne (Neₑ σ x)
  Nfₑ σ (lam t) = lam (Nfₑ (keep σ) t)
  Nfₑ σ (t , u) = Nfₑ σ t , Nfₑ σ u
  Nfₑ σ true = true
  Nfₑ σ false = false

  Neₑ : ∀ {Γ Δ A} → OPE Γ Δ → Ne Δ A → Ne Γ A
  Neₑ σ (var x) = var (∈ₑ σ x)
  Neₑ σ (app t x) = app (Neₑ σ t) (Nfₑ σ x)
  Neₑ σ (if t x x₁) = if (Neₑ σ t) (Nfₑ σ x) (Nfₑ σ x₁)
  Neₑ σ (π₁ t) = π₁ (Neₑ σ t)
  Neₑ σ (π₂ t) = π₂ (Neₑ σ t)


--------------------------------------------------------------------------------


Tyᴹ : Ty → Con → Set
Tyᴹ 𝔹        Γ = Nf Γ 𝔹
Tyᴹ (A * B)  Γ = Tyᴹ A Γ × Tyᴹ B Γ
Tyᴹ (A ⇒ B)  Γ = ∀ {Δ} → OPE Δ Γ → Tyᴹ A Δ → Tyᴹ B Δ

Conᴹ : Con → Con → Set
Conᴹ ∙       Δ = ⊤
Conᴹ (Γ ▶ A) Δ = Conᴹ Γ Δ × Tyᴹ A Δ

OPEᴹ : ∀ {Γ Δ} → OPE Γ Δ → ∀ {Σ} → Conᴹ Γ Σ → Conᴹ Δ Σ
OPEᴹ ∙        Γᴹ        = tt
OPEᴹ (drop σ) (Γᴹ , _)  = OPEᴹ σ Γᴹ
OPEᴹ (keep σ) (Γᴹ , Aᴹ) = OPEᴹ σ Γᴹ , Aᴹ

Tyᴹₑ : ∀ {A Γ Δ} → OPE Δ Γ → Tyᴹ A Γ → Tyᴹ A Δ
Tyᴹₑ {𝔹}      σ t = Nfₑ σ t
Tyᴹₑ {A * B}  σ t = (Tyᴹₑ σ (₁ t)) , (Tyᴹₑ σ (₂ t))
Tyᴹₑ {A ⇒ B}  σ t = λ δ → t (σ ∘ₑ δ)

Conᴹₑ : ∀ {Γ Δ Σ} → OPE Σ Δ → Conᴹ Γ Δ → Conᴹ Γ Σ
Conᴹₑ {∙}     σ tt        = tt
Conᴹₑ {_ ▶ _} σ (Γᴹ , tᴹ) = Conᴹₑ σ Γᴹ , Tyᴹₑ σ tᴹ

mutual
  qᴹ : ∀ {A Γ} → Tyᴹ A Γ → Nf Γ A
  qᴹ {𝔹}      t = t
  qᴹ {A * B}  t = qᴹ (₁ t) , qᴹ (₂ t)
  qᴹ {A ⇒ B}  t = lam (qᴹ (t wk (uᴹ (var vz))))

  uᴹ : ∀ {A Γ} → Ne Γ A → Tyᴹ A Γ
  uᴹ {𝔹}      t = ne t
  uᴹ {A * B}  t = uᴹ (π₁ t) , uᴹ (π₂ t)
  uᴹ {A ⇒ B}  t = λ σ a → uᴹ (Ne.app (Neₑ σ t) (qᴹ a))

∈ᴹ : ∀ {Γ A} → A ∈ Γ → ∀ {Δ} → Conᴹ Γ Δ → Tyᴹ A Δ
∈ᴹ {∙} () Γᴹ
∈ᴹ {Γ ▶ _} vz     Γᴹ = ₂ Γᴹ
∈ᴹ {Γ ▶ _} (vs x) Γᴹ = ∈ᴹ x (₁ Γᴹ)

Tmᴹ : ∀ {Γ A} → Tm Γ A → ∀ {Δ} → Conᴹ Γ Δ → Tyᴹ A Δ
Tmᴹ (var x) Γᴹ = ∈ᴹ x Γᴹ
Tmᴹ true Γᴹ = true
Tmᴹ false Γᴹ = false
Tmᴹ (if t u v) Γᴹ with Tmᴹ t Γᴹ
... | ne n  = uᴹ (if n (qᴹ (Tmᴹ u Γᴹ)) (qᴹ (Tmᴹ v Γᴹ)))
... | true  = Tmᴹ u Γᴹ
... | false = Tmᴹ v Γᴹ
Tmᴹ (π₁ t) Γᴹ = ₁ (Tmᴹ t Γᴹ)
Tmᴹ (π₂ t) Γᴹ = ₂ (Tmᴹ t Γᴹ)
Tmᴹ (t , u) Γᴹ = Tmᴹ t Γᴹ , Tmᴹ u Γᴹ
Tmᴹ (lam t) Γᴹ = λ σ a → Tmᴹ t (Conᴹₑ σ Γᴹ , a)
Tmᴹ (app t u) Γᴹ = Tmᴹ t Γᴹ idₑ (Tmᴹ u Γᴹ)

uConᴹ : ∀ {Γ} → Conᴹ Γ Γ
uConᴹ {∙}     = tt
uConᴹ {Γ ▶ A} = Conᴹₑ wk uConᴹ , uᴹ (var vz)

nf : ∀ {Γ A} → Tm Γ A → Nf Γ A
nf t = qᴹ (Tmᴹ t uConᴹ)

--------------------------------------------------------------------------------

mutual
  ⌜_⌝Nf : ∀ {Γ A} → Nf Γ A → Tm Γ A
  ⌜ ne x ⌝Nf = ⌜ x ⌝Ne
  ⌜ lam t ⌝Nf = lam ⌜ t ⌝Nf
  ⌜ t , t₁ ⌝Nf = ⌜ t ⌝Nf , ⌜ t₁ ⌝Nf
  ⌜ true ⌝Nf = true
  ⌜ false ⌝Nf = false

  ⌜_⌝Ne : ∀ {Γ A} → Ne Γ A → Tm Γ A
  ⌜ var x ⌝Ne = var x
  ⌜ app t x ⌝Ne = app ⌜ t ⌝Ne ⌜ x ⌝Nf
  ⌜ if t x x₁ ⌝Ne = if ⌜ t ⌝Ne ⌜ x ⌝Nf ⌜ x₁ ⌝Nf
  ⌜ π₁ t ⌝Ne = π₁ ⌜ t ⌝Ne
  ⌜ π₂ t ⌝Ne = π₂ ⌜ t ⌝Ne

mutual
  tr : ∀ {Γ A} → Con' Γ → Ty' A → (t : Nf Γ A) → Tm' (⌜ t ⌝Nf)
  tr Γ A (ne t) = trNe↓ Γ A t
  tr Γ (A ⇒ B) (lam t) = lam (tr (Γ ▶ A) B t)
  tr Γ () (t , u)
  tr Γ A true    = true
  tr Γ A false   = false

  tr∈ : ∀ {Γ A} → Con' Γ →  A ∈ Γ → Ty' A
  tr∈ (Γ ▶ x) vz     = x
  tr∈ (Γ ▶ _) (vs x) = tr∈ Γ x

  trNe↓ : ∀ {Γ A} → Con' Γ → Ty' A → (t : Ne Γ A) → Tm' (⌜ t ⌝Ne)
  trNe↓ Γ A (var x)    = var x A
  trNe↓ Γ A (app t u)  = case trNe↑ Γ t of λ {((A ⇒ B) , t) → app t (tr Γ A u)}
  trNe↓ Γ A (if t u v) = if (trNe↓ Γ 𝔹 t) (tr Γ A u) (tr Γ A v)
  trNe↓ Γ A (π₁ t)     = case trNe↑ Γ t .₁ of λ ()
  trNe↓ Γ A (π₂ t)     = case trNe↑ Γ t .₁ of λ ()

  trNe↑ : ∀ {Γ A} → Con' Γ → (t : Ne Γ A) → Ty' A × Tm' (⌜ t ⌝Ne)
  trNe↑ Γ (var x)    = tr∈ Γ x , var x (tr∈ Γ x)
  trNe↑ Γ (app t u)  = case trNe↑ Γ t of λ {((A ⇒ B) , t) → B , app t (tr Γ A u)}
  trNe↑ Γ (if t u v) = {!!}
  trNe↑ Γ (π₁ t)     = case trNe↑ Γ t .₁ of λ ()
  trNe↑ Γ (π₂ t)     = case trNe↑ Γ t .₁ of λ ()

  -- trNe : ∀ {Γ A} → Con' Γ → (t : Ne Γ A) → Ty' A × Tm' (⌜ t ⌝Ne)
  -- trNe Γ (var x)    = tr∈ Γ x , var x (tr∈ Γ x)
  -- trNe Γ (app t u)  = case trNe Γ t of λ {((A ⇒ B) , t) → B , app t (tr Γ A u)}
  -- trNe Γ (if t u v) = {!!}
  -- trNe Γ (π₁ t)     = case trNe Γ t .₁ of λ ()
  -- trNe Γ (π₂ t)     = case trNe Γ t .₁ of λ ()

  -- backtrans : ∀ {Γ A} → Con' Γ → Ty' A → Nf Γ A → ∃ (Tm' {Γ}{A})
  -- backtrans Γ A       (ne t)  = {!!}
  -- backtrans Γ (A ⇒ B) (lam t) = , lam (backtrans (Γ ▶ A) B t .₂)
  -- backtrans Γ () (t , u)
  -- backtrans Γ A true    = , true
  -- backtrans Γ A false   = , false

  -- backNe : ∀ {Γ A} → Con' Γ → Ty' A → Ne Γ A → ∃ (Tm' {Γ}{A})
  -- backNe Γ A (var x) = , var x
  -- backNe Γ A (app t u) = {!backNe Γ ? t!}
  -- backNe Γ A (if t u v) = {!!}
  -- backNe Γ A (π₁ t) = {!!}
  -- backNe Γ A (π₂ t) = {!!}
