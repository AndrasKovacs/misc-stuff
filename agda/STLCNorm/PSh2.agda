{-# OPTIONS --without-K #-}

open import Lib

-- Syntax
--------------------------------------------------------------------------------

infixr 4 _⇒_

data Ty : Set where
  ι   : Ty
  _⇒_ : Ty → Ty → Ty

data Con : Set where
  ∙   : Con
  _,_ : Con → Ty → Con

data _∈_ (A : Ty) : Con → Set where
  vz : ∀ {Γ} → A ∈ (Γ , A)
  vs : ∀ {B Γ} → A ∈ Γ → A ∈ (Γ , B)

data Tm Γ : Ty → Set where
  var : ∀ {A} → A ∈ Γ → Tm Γ A
  lam : ∀ {A B} → Tm (Γ , A) B → Tm Γ (A ⇒ B)
  app : ∀ {A B} → Tm Γ (A ⇒ B) → Tm Γ A → Tm Γ B

-- Renaming
--------------------------------------------------------------------------------

infix 3 _⊆_
infixr 9 _∘ᵣ_

data _⊆_ : Con → Con → Set where
  ∙    : ∙ ⊆ ∙
  add  : ∀ {A Γ Δ} → Γ ⊆ Δ → Γ     ⊆ Δ , A
  keep : ∀ {A Γ Δ} → Γ ⊆ Δ → Γ , A ⊆ Δ , A

-- (Con, _⊆_) is a category

idᵣ : ∀ {Γ} → Γ ⊆ Γ
idᵣ {∙}     = ∙
idᵣ {Γ , A} = keep (idᵣ {Γ})

wk : ∀ {A Γ} → Γ ⊆ Γ , A
wk = add idᵣ

_∘ᵣ_ : ∀ {Γ Δ Σ} → Δ ⊆ Σ → Γ ⊆ Δ → Γ ⊆ Σ
∙      ∘ᵣ r'      = r'
add r  ∘ᵣ r'      = add (r ∘ᵣ r')
keep r ∘ᵣ add r'  = add (r ∘ᵣ r')
keep r ∘ᵣ keep r' = keep (r ∘ᵣ r')

idlᵣ : ∀ {Γ Δ}(r : Γ ⊆ Δ) → idᵣ ∘ᵣ r ≡ r
idlᵣ ∙        = refl
idlᵣ (add r)  = ap add (idlᵣ r)
idlᵣ (keep r) = ap keep (idlᵣ r)

idrᵣ : ∀ {Γ Δ}(r : Γ ⊆ Δ) → r ∘ᵣ idᵣ ≡ r
idrᵣ ∙        = refl
idrᵣ (add r)  = ap add (idrᵣ r)
idrᵣ (keep r) = ap keep (idrᵣ r)

assᵣ :
  ∀ {Γ Δ Σ Ξ}(r : Σ ⊆ Ξ)(r' : Δ ⊆ Σ)(r'' : Γ ⊆ Δ)
  → (r ∘ᵣ r') ∘ᵣ        r''        ≡ r ∘ᵣ (r' ∘ᵣ r'')
assᵣ ∙        r'        r''        = refl
assᵣ (add r)  r'        r''        = ap add  (assᵣ r r' r'')
assᵣ (keep r) (add r')  r''        = ap add  (assᵣ r r' r'')
assᵣ (keep r) (keep r') (add r'')  = ap add  (assᵣ r r' r'')
assᵣ (keep r) (keep r') (keep r'') = ap keep (assᵣ r r' r'')

-- (A ∈_) is a functor

∈↑ : ∀ {Γ Δ A} → Γ ⊆ Δ → A ∈ Γ → A ∈ Δ
∈↑ ∙        ()
∈↑ (add r)  v      = vs (∈↑ r v)
∈↑ (keep r) vz     = vz
∈↑ (keep r) (vs v) = vs (∈↑ r v)

∈↑-id : ∀ {Γ A}(v : A ∈ Γ) → ∈↑ idᵣ v ≡ v
∈↑-id vz     = refl
∈↑-id (vs v) = ap vs (∈↑-id v)

∈↑-∘ :
  ∀ {Γ Δ Σ A}(v : A ∈ Γ)(σ : Δ ⊆ Σ)(δ : Γ ⊆ Δ)
  → ∈↑ σ (∈↑ δ v) ≡ ∈↑ (σ ∘ᵣ δ) v
∈↑-∘ () ∙       ∙
∈↑-∘ v      (add σ)  δ        = ap vs (∈↑-∘ v σ δ)
∈↑-∘ v      (keep σ) (add δ)  = ap vs (∈↑-∘ v σ δ)
∈↑-∘ vz     (keep σ) (keep δ) = refl
∈↑-∘ (vs v) (keep σ) (keep δ) = ap vs (∈↑-∘ v σ δ)

-- (Tm _ A) is a functor

Tm↑ : ∀ {Γ Δ A} → Γ ⊆ Δ → Tm Γ A → Tm Δ A
Tm↑ r (var v)   = var (∈↑ r v)
Tm↑ r (lam t)   = lam (Tm↑ (keep r) t)
Tm↑ r (app f x) = app (Tm↑ r f) (Tm↑ r x)

Tm↑-id : ∀ {Γ A}(t : Tm Γ A) → Tm↑ idᵣ t ≡ t
Tm↑-id (var v)   = ap var (∈↑-id v)
Tm↑-id (lam t)   = ap lam (Tm↑-id t)
Tm↑-id (app f x) = ap2 app (Tm↑-id f) (Tm↑-id x)

Tm↑-∘ :
  ∀ {Γ Δ Σ A}(t : Tm Γ A)(σ : Δ ⊆ Σ)(δ : Γ ⊆ Δ)
  → Tm↑ σ (Tm↑ δ t) ≡ Tm↑ (σ ∘ᵣ δ) t
Tm↑-∘ (var v)   σ δ = ap var (∈↑-∘ v σ δ)
Tm↑-∘ (lam t)   σ δ = ap lam (Tm↑-∘ t (keep σ) (keep δ))
Tm↑-∘ (app f x) σ δ = ap2 app (Tm↑-∘ f σ δ) (Tm↑-∘ x σ δ)

-- Substitution
--------------------------------------------------------------------------------

infix  6 _∘_
infixl 8 _[_]
infixl 8 _[_]∈
infixl 3 _^_

data Tms (Γ : Con) : Con → Set where
  ∙   : Tms Γ ∙
  _,_ : ∀ {A Δ} → Tms Γ Δ → Tm Γ A → Tms Γ (Δ , A)

,≡ : ∀ {Γ Δ A}{σ δ : Tms Γ Δ}{t t' : Tm Γ A} → σ ≡ δ → t ≡ t' → (Tms Γ (Δ , A) ∋ (σ , t)) ≡ δ , t'
,≡ refl refl = refl

Tms↑ : ∀ {Γ Δ Σ} → Γ ⊆ Σ → Tms Γ Δ → Tms Σ Δ
Tms↑ r ∙       = ∙
Tms↑ r (σ , t) = Tms↑ r σ , Tm↑ r t

Tms↑-∘ :
  ∀ {Γ Δ Σ Ξ}(ν : Tms Γ Ξ)(σ : Δ ⊆ Σ)(δ : Γ ⊆ Δ)
  → Tms↑ σ (Tms↑ δ ν) ≡ Tms↑ (σ ∘ᵣ δ) ν
Tms↑-∘ ∙       σ δ = refl
Tms↑-∘ (ν , t) σ δ = ,≡ (Tms↑-∘ ν σ δ) (Tm↑-∘ t σ δ)

_^_ : ∀ {Γ Δ} → Tms Γ Δ → ∀ A → Tms (Γ , A) (Δ , A)
σ ^ A = Tms↑ wk σ , var vz

_[_]∈ : ∀ {Γ Δ A} → A ∈ Δ → Tms Γ Δ → Tm Γ A
vz   [ σ , t ]∈ = t
vs v [ σ , _ ]∈ = v [ σ ]∈

_[_] : ∀ {Γ Δ A} → Tm Δ A → Tms Γ Δ → Tm Γ A
var v   [ σ ] = v [ σ ]∈
lam t   [ σ ] = lam (t [ σ ^ _ ])
app f x [ σ ] = app (f [ σ ]) (x [ σ ])

idₛ : ∀ {Γ} → Tms Γ Γ
idₛ {∙    } = ∙
idₛ {Γ , A} = idₛ {Γ} ^ A

_∘_ : ∀ {Γ Δ Σ} → Tms Δ Σ → Tms Γ Δ → Tms Γ Σ
∙       ∘ δ = ∙
(σ , t) ∘ δ = σ ∘ δ , t [ δ ]

∈↑-comm :
  ∀ {Γ Δ Σ A}(v : A ∈ Γ)(r : Δ ⊆ Σ)(σ : Tms Δ Γ)
  → v [ Tms↑ r σ ]∈ ≡ Tm↑ r (v [ σ ]∈)
∈↑-comm vz     r (σ , _) = refl
∈↑-comm (vs v) r (σ , _) = ∈↑-comm v r σ

Tm↑-comm :
  ∀ {Γ Δ Σ A}(t : Tm Γ A)(r : Δ ⊆ Σ)(σ : Tms Δ Γ)
  → t [ Tms↑ r σ ] ≡ Tm↑ r (t [ σ ])
Tm↑-comm (var v)     r σ = ∈↑-comm v r σ
Tm↑-comm (lam {A} t) r σ =
  ap lam (ap (λ x → t [ x , var vz ])
      (Tms↑-∘ σ wk r
    ◾ ap (λ x → Tms↑ (add x) σ) (idlᵣ r)
    ◾ ap (λ x → Tms↑ (add x) σ) (idrᵣ r ⁻¹)
    ◾ Tms↑-∘ σ (keep r) wk ⁻¹)
  ◾ Tm↑-comm t (keep r) (σ ^ _))
Tm↑-comm (app f x) r σ = ap2 app (Tm↑-comm f r σ) (Tm↑-comm x r σ)

Tms↑-comm :
  ∀ {Γ Δ Σ Ξ}
  → (σ : Tms Δ Ξ)(r : Γ ⊆ Σ)(δ : Tms Γ Δ)
  → σ ∘ Tms↑ r δ ≡ Tms↑ r (σ ∘ δ)
Tms↑-comm ∙       r δ = refl
Tms↑-comm (σ , t) r δ = ,≡ (Tms↑-comm σ r δ) (Tm↑-comm t r δ)

emb : ∀ {Γ Δ} → Γ ⊆ Δ → Tms Δ Γ
emb ∙        = ∙
emb (add r)  = Tms↑ wk (emb r)
emb (keep r) = emb r ^ _

emb-id : ∀ {Γ} → emb (idᵣ {Γ}) ≡ idₛ
emb-id {∙}     = refl
emb-id {Γ , A} = ap (λ x → Tms↑ (add idᵣ) x , var vz) emb-id

emb-∈↑ : ∀ {Γ Δ A}(r : Γ ⊆ Δ)(v : A ∈ Γ) → var (∈↑ r v) ≡ v [ emb r ]∈
emb-∈↑ ∙ ()
emb-∈↑ (add {A} r)  v
  rewrite ∈↑-comm v (wk {A}) (emb r) | emb-∈↑ r v ⁻¹ | ∈↑-id (∈↑ r v) = refl
emb-∈↑ (keep r) vz     = refl
emb-∈↑ (keep {A} r) (vs v)
  rewrite ∈↑-comm v (wk {A}) (emb r) | emb-∈↑ r v ⁻¹ | ∈↑-id (∈↑ r v) = refl

emb-Tm↑ : ∀ {Γ Δ A}(r : Γ ⊆ Δ)(t : Tm Γ A) → Tm↑ r t ≡ t [ emb r ]
emb-Tm↑ r (var v)   = emb-∈↑ r v
emb-Tm↑ r (lam t)   = ap lam (emb-Tm↑ (keep r) t)
emb-Tm↑ r (app f x) = ap2 app (emb-Tm↑ r f) (emb-Tm↑ r x)

emb-Tms↑ : ∀ {Γ Δ Σ}(r : Γ ⊆ Σ)(σ : Tms Γ Δ) → Tms↑ r σ ≡ σ ∘ emb r
emb-Tms↑ r ∙       = refl
emb-Tms↑ r (σ , t) = ,≡ (emb-Tms↑ r σ) (emb-Tm↑ r t)

[id]∈ : ∀{Γ A}(v : A ∈ Γ) → v [ idₛ ]∈ ≡ var v
[id]∈ vz     = refl
[id]∈ (vs v) = ∈↑-comm v (add idᵣ) idₛ
             ◾ ap (Tm↑ (add idᵣ)) ([id]∈ v)
             ◾ ap (λ v → var (vs v)) (∈↑-id v)

[id] : ∀{Γ A}(t : Tm Γ A) → t [ idₛ ] ≡ t
[id] (var v)   = [id]∈ v
[id] (lam t)   = ap lam ([id] t)
[id] (app f x) = ap2 app ([id] f) ([id] x)

idr : ∀{Γ Δ}(σ : Tms Γ Δ) → σ ∘ idₛ ≡ σ
idr ∙       = refl
idr (σ , t) = ,≡ (idr σ) ([id] t)

idl : ∀{Γ Δ}(σ : Tms Γ Δ) → idₛ ∘ σ ≡ σ
idl {Δ = ∙}     ∙       = refl
idl {Δ = Δ , x} (σ , t) = ,≡ ({!!} ◾ idl σ) refl

[][]∈ :
  ∀ {Γ Δ Σ A}(v : A ∈ Σ)(σ : Tms Γ Δ)(δ : Tms Δ Σ)
  → v [ δ ]∈ [ σ ] ≡ v [ δ ∘ σ ]∈
[][]∈ vz     σ (δ , t) = refl
[][]∈ (vs v) σ (δ , t) = [][]∈ v σ δ

[][] :
  ∀ {Γ Δ Σ A}(t : Tm Σ A)(δ : Tms Δ Σ)(σ : Tms Γ Δ)
  → t [ δ ] [ σ ] ≡ t [ δ ∘ σ ]
[][] (var v)       σ δ = [][]∈ v δ σ
[][] (lam {A} t)   σ δ =
  ap lam ([][] t (σ ^ _)(δ ^ _) ◾ ap (t [_]) (,≡ ({!!} ◾ Tms↑-comm σ wk δ) refl))
[][] (app f x)     σ δ = ap2 app ([][] f σ δ) ([][] x σ δ)

ass :
  ∀ {Δ Γ Σ Ω}(σ : Tms Σ Ω)(δ : Tms Γ Σ)(ν : Tms Δ Γ)
  → (σ ∘ δ) ∘ ν ≡ σ ∘ (δ ∘ ν)
ass ∙       δ ν = refl
ass (σ , t) δ ν = ,≡ (ass σ δ ν) ([][] t δ ν)

-- Normal forms
--------------------------------------------------------------------------------

infix 3 _∈_
infixl 7 _$ₙ_

mutual
  data Nf (Γ : Con) : Ty → Set where
    ne   : Ne Γ ι → Nf Γ ι
    lamₙ : ∀ {A B} → Nf (Γ , A) B → Nf Γ (A ⇒ B)

  data Ne (Γ : Con) : Ty → Set where
    var  : ∀ {A} → A ∈ Γ → Ne Γ A
    _$ₙ_ : ∀ {A B} → Ne Γ (A ⇒ B) → Nf Γ A → Ne Γ B

mutual
  Nf↑ : ∀ {Γ Δ A} → Γ ⊆ Δ → Nf Γ A → Nf Δ A
  Nf↑ r (ne n)   = ne (Ne↑ r n)
  Nf↑ r (lamₙ t) = lamₙ (Nf↑ (keep r) t)

  Ne↑ : ∀ {Γ Δ A} → Γ ⊆ Δ → Ne Γ A → Ne Δ A
  Ne↑ r (var v)  = var (∈↑ r v)
  Ne↑ r (n $ₙ t) = Ne↑ r n $ₙ Nf↑ r t

mutual
  ⌜_⌝ : ∀ {Γ A} → Nf Γ A → Tm Γ A
  ⌜ ne n   ⌝ = ⌜ n ⌝Ne
  ⌜ lamₙ t ⌝ = lam ⌜ t ⌝

  ⌜_⌝Ne : ∀ {Γ A} → Ne Γ A → Tm Γ A
  ⌜ var v  ⌝Ne = var v
  ⌜ n $ₙ t ⌝Ne = app ⌜ n ⌝Ne ⌜ t ⌝

-- Conversion
--------------------------------------------------------------------------------

data _~_ {Γ} : ∀ {A} → Tm Γ A → Tm Γ A → Set where
  η     : ∀ {A B}(t : Tm Γ (A ⇒ B))                  →  t              ~ lam (app (Tm↑ wk t) (var vz))
  β     : ∀ {A B}(t : Tm (Γ , A) B) t'               →  app (lam t) t' ~ t [ idₛ , t' ]

  lam   : ∀ {A B}{t t' : Tm (Γ , A) B}      → t ~ t' →  lam t          ~ lam t'
  app₁  : ∀ {A B}{f f' : Tm Γ (A ⇒ B)}{x}   → f ~ f' →  app f x        ~ app f' x
  app₂  : ∀ {A B}{f : Tm Γ (A ⇒ B)} {x x'}  → x ~ x' →  app f x        ~ app f x'
  ~refl : ∀ {A}{t : Tm Γ A}    → t ~ t
  _~⁻¹  : ∀ {A}{t t' : Tm Γ A} → t ~ t' → t' ~ t
  _~◾_  : ∀ {A}{t t' t'' : Tm Γ A} → t ~ t' → t' ~ t'' → t ~ t''

infix 3 _~_
infixl 4 _~◾_

-- Normalization
--------------------------------------------------------------------------------

mutual
  ⌜⌝Ne↑ : ∀ {Γ Δ A}(r : Γ ⊆ Δ)(n : Ne Γ A) → ⌜ Ne↑ r n ⌝Ne ≡ Tm↑ r ⌜ n ⌝Ne
  ⌜⌝Ne↑ r (var v)  = refl
  ⌜⌝Ne↑ r (n $ₙ t) = ap2 app (⌜⌝Ne↑ r n) (⌜⌝↑ r t)

  ⌜⌝↑ : ∀ {Γ Δ A}(r : Γ ⊆ Δ)(n : Nf Γ A) → ⌜ Nf↑ r n ⌝ ≡ Tm↑ r ⌜ n ⌝
  ⌜⌝↑ r (ne n)   = ⌜⌝Ne↑ r n
  ⌜⌝↑ r (lamₙ n) = ap lam (⌜⌝↑ (keep r) n)

Tm↑~ : ∀ {Γ Δ A}{t t' : Tm Γ A} → (r : Γ ⊆ Δ) → t ~ t' → Tm↑ r t ~ Tm↑ r t'
Tm↑~ {A = A ⇒ B} r (η t) =
  coe (ap (λ x → Tm↑ r t ~ lam (app x (var vz)))
    (Tm↑-∘ t wk r ◾ ap (λ x → Tm↑ (add x) t) (idlᵣ r ◾ idrᵣ r ⁻¹) ◾ Tm↑-∘ t (keep r) wk ⁻¹))
  (η (Tm↑ r t))
Tm↑~ r (β t t') =
  coe (ap (app (lam (Tm↑ (keep r) t)) (Tm↑ r t') ~_)
    (ap (_[ idₛ , Tm↑ r t' ]) (emb-Tm↑ (keep r) t)
    ◾ [][] t _ _ ◾ ap (t [_]) (,≡ {!!} refl)
    ◾ Tm↑-comm t r (idₛ , t')))
  (β (Tm↑ (keep r) t) (Tm↑ r t'))
Tm↑~ r (lam {t         = t} {t'} t~t') = lam (Tm↑~ (keep r) t~t')
Tm↑~ r (app₁ t~t')     = app₁ (Tm↑~ r t~t')
Tm↑~ r (app₂ t~t')     = app₂ (Tm↑~ r t~t')
Tm↑~ r ~refl           = ~refl
Tm↑~ r (t~t' ~⁻¹)      = Tm↑~ r t~t' ~⁻¹
Tm↑~ r (t~t' ~◾ t~t'') = Tm↑~ r t~t' ~◾ Tm↑~ r t~t''

⟦_⟧Ty : (A : Ty) → ∀ {Γ} → Tm Γ A → Set
⟦ ι     ⟧Ty {Γ} t = Σ (Nf Γ ι) λ n → t ~ ⌜ n ⌝
⟦ A ⇒ B ⟧Ty {Γ} t = ∀ Δ (r : Γ ⊆ Δ)(a : Tm Δ A)(⟦a⟧ : ⟦ A ⟧Ty a) → ⟦ B ⟧Ty (app (Tm↑ r t) a)

⟦_⟧Con : (Δ : Con) → ∀ {Γ} → Tms Γ Δ → Set
⟦ ∙     ⟧Con Δ       = ⊤
⟦ Γ , A ⟧Con (Δ , t) = ⟦ Γ ⟧Con Δ × ⟦ A ⟧Ty t

⟦Ty⟧↑ : ∀ {A Γ Δ t} → (r : Γ ⊆ Δ) → ⟦ A ⟧Ty t → ⟦ A ⟧Ty (Tm↑ r t)
⟦Ty⟧↑ {ι}     r (n , p) = Nf↑ r n , coe (ap (_ ~_) (⌜⌝↑ r n ⁻¹)) (Tm↑~ r p)
⟦Ty⟧↑ {A ⇒ B} r tᴹ      =
  λ Σ r' a aᴹ → coe (ap (λ x → ⟦ B ⟧Ty (app x a)) (Tm↑-∘ _ r' r ⁻¹)) (tᴹ Σ (r' ∘ᵣ r) a aᴹ)

⟦Ty⟧~ : ∀ {A Γ t t'} → t ~ t' → ⟦ A ⟧Ty {Γ} t → ⟦ A ⟧Ty t'
⟦Ty⟧~ {ι}     t~t' (n , p) = n , (t~t' ~⁻¹ ~◾ p)
⟦Ty⟧~ {A ⇒ B} t~t' tᴹ      = λ Σ r a aᴹ → ⟦Ty⟧~ (app₁ (Tm↑~ r t~t')) (tᴹ Σ r a aᴹ)

⟦Con⟧↑ : ∀ {Σ Γ Δ}(r : Γ ⊆ Δ)(σ : Tms Γ Σ) → ⟦ Σ ⟧Con σ → ⟦ Σ ⟧Con (Tms↑ r σ)
⟦Con⟧↑ r ∙       σᴹ        = tt
⟦Con⟧↑ r (σ , t) (σᴹ , tᴹ) = ⟦Con⟧↑ r σ σᴹ , ⟦Ty⟧↑ r tᴹ

⟦_⟧∈ : ∀ {Γ A} → (v : A ∈ Γ) → ∀ {Δ}(σ : Tms Δ Γ) → ⟦ Γ ⟧Con σ → ⟦ A ⟧Ty (v [ σ ]∈)
⟦ vz   ⟧∈ (σ , _) (_  , tᴹ) = tᴹ
⟦ vs v ⟧∈ (σ , _) (σᴹ , _ ) = ⟦ v ⟧∈ σ σᴹ

⟦_⟧Tm : ∀ {Γ A}(t : Tm Γ A) → ∀ {Δ}(σ : Tms Δ Γ) → ⟦ Γ ⟧Con σ → ⟦ A ⟧Ty (t [ σ ])
⟦ var v   ⟧Tm σ σᴹ = ⟦ v ⟧∈ σ σᴹ
⟦ lam t   ⟧Tm σ σᴹ = λ Σ r a aᴹ
  → ⟦Ty⟧~
      (coe
        (ap (_~ app (lam (Tm↑ (keep r) (t [ σ ^ _ ]))) a)
          ( ap (_[ idₛ , a ]) (Tm↑-comm t (keep r) (σ ^ _) ⁻¹)
          ◾ [][] t (Tms↑ (keep r) (Tms↑ wk σ) , var vz) (idₛ , a)
          ◾ ap (t [_])
              (,≡
                (ap (_∘ _) (Tms↑-∘ σ (keep r) wk)
                ◾ ap (λ x → Tms↑ (add x) σ ∘ _) (idrᵣ r)
                ◾ {!!})
                refl)))
        (β (Tm↑ (keep r) (t [ σ ^ _ ])) a ~⁻¹))
      (⟦ t ⟧Tm (Tms↑ r σ , a) (⟦Con⟧↑ r σ σᴹ , aᴹ))

⟦ app f a ⟧Tm σ σᴹ =
  coe (ap (λ x → ⟦ _ ⟧Ty (app x (a [ σ ]))) (Tm↑-id (f [ σ ])))
  (⟦ f ⟧Tm σ σᴹ _ idᵣ (a [ σ ]) (⟦ a ⟧Tm σ σᴹ))

mutual
   q : ∀ A {Γ}{t : Tm Γ A} → ⟦ A ⟧Ty t → Σ (Nf Γ A) λ n → t ~ ⌜ n ⌝
   q ι       {Γ} {t} tᴹ = tᴹ
   q (A ⇒ B) {Γ} {t} tᴹ =
     let (n , p) = q B (tᴹ (Γ , A) (add idᵣ) (var vz) (u A (var vz)))
     in lamₙ n , (η t ~◾ lam p)

   u : ∀ A {Γ} → (n : Ne Γ A) → ⟦ A ⟧Ty ⌜ n ⌝Ne
   u ι       n = ne n , ~refl
   u (A ⇒ B) n Δ r a aᴹ =
     let (aₙ , a~aₙ) = q A aᴹ
     in ⟦Ty⟧~
       (coe (ap (λ x → app ⌜ Ne↑ r n ⌝Ne ⌜ aₙ ⌝ ~ app x a) (⌜⌝Ne↑ r n))
         (app₂ (a~aₙ ~⁻¹)))
       (u B (Ne↑ r n $ₙ aₙ))

uCon : ∀ Γ → ⟦ Γ ⟧Con idₛ
uCon ∙       = tt
uCon (Γ , A) = ⟦Con⟧↑ wk _ (uCon Γ) , u A (var vz)

norm : ∀ {Γ A} → (t : Tm Γ A) → Σ (Nf Γ A) λ n → t ~ ⌜ n ⌝
norm {Γ}{A} t = q A (coe (ap ⟦ A ⟧Ty ([id] t)) (⟦ t ⟧Tm {Γ} idₛ (uCon Γ)))

-- Stability
--------------------------------------------------------------------------------

mutual
  stab∈ : ∀ {Γ}(v : ι ∈ Γ) → proj₁ (norm (var v)) ≡ ne (var v)
  stab∈ vz     = refl
  stab∈ (vs v) = {!stab∈ v!}

  stabNe : ∀ {Γ A} → (n : Ne Γ A) → proj₁ (norm ⌜ n ⌝Ne) ≡ {!!}
  stabNe (var v)  = {!!}
  stabNe (f $ₙ n) = {!stabNe f!}

  stab : ∀ {Γ A} → (n : Nf Γ A) → proj₁ (norm ⌜ n ⌝) ≡ n
  stab (ne n)   = {!!}
  stab (lamₙ n) = {!!} ◾ ap lamₙ (stab n)



