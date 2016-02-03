
open import Data.List
open import Data.Nat
open import Data.Product
open import Data.Unit
open import Function hiding (_$_)
open import Data.Empty
open import Data.Sum
open import Relation.Binary.PropositionalEquality

data ⋆ : Set where
  ι   : ⋆
  _▷_ : ⋆ → ⋆ → ⋆
infixr 5 _▷_

data Cx (A : Set) : Set where
  𝓔   : Cx A
  _,_ : Cx A → A → Cx A
infixl 4 _,_

data _∈_ (τ : ⋆) : Cx ⋆ → Set where
  zero : ∀ {Γ}           → τ ∈ Γ , τ
  suc  : ∀ {Γ σ} → τ ∈ Γ → τ ∈ Γ , σ
infix 4 _∈_  

data _⊢_ (Γ : Cx ⋆) : ⋆ → Set where
  var :
    ∀ {τ}
    → τ ∈ Γ
    --------
    → Γ ⊢ τ

  lam :
    ∀ {σ τ}
    → Γ , σ ⊢ τ
    ------------
    → Γ ⊢ σ ▷ τ

  app :
    ∀ {σ τ}
    → Γ ⊢ σ ▷ τ → Γ ⊢ σ
    --------------------
    → Γ ⊢ τ    
infix 3 _⊢_

⟦_⟧⋆ : ⋆ → Set
⟦ ι     ⟧⋆ = ℕ
⟦ σ ▷ τ ⟧⋆ = ⟦ σ ⟧⋆ → ⟦ τ ⟧⋆

⟦_⟧c  : Cx ⋆ → (⋆ → Set) → Set
⟦ 𝓔     ⟧c V = ⊤
⟦ Γ , σ ⟧c V = ⟦ Γ ⟧c V × V σ

⟦_⟧∈ : ∀ {Γ τ V} → τ ∈ Γ →  ⟦ Γ ⟧c V → V τ
⟦ zero  ⟧∈ (γ , t) = t
⟦ suc i ⟧∈ (γ , s) = ⟦ i ⟧∈ γ

⟦_⟧⊢ : ∀ {Γ τ} → Γ ⊢ τ →  ⟦ Γ ⟧c ⟦_⟧⋆ → ⟦ τ ⟧⋆
⟦ var i   ⟧⊢   = ⟦ i ⟧∈
⟦ lam t   ⟧⊢ γ = λ s → ⟦ t ⟧⊢ (γ , s)
⟦ app f s ⟧⊢ γ = ⟦ f ⟧⊢ γ (⟦ s ⟧⊢ γ)

-- alternatively : see "order preserving embeddings"
Ren Sub : Cx ⋆ → Cx ⋆ → Set
Ren Γ Δ = ∀ {τ} → τ ∈ Γ → τ ∈ Δ
Sub Γ Δ = ∀ {τ} → τ ∈ Γ → Δ ⊢ τ

_<><_ : ∀ {A} → Cx A → List A → Cx A
xz <>< []       = xz
xz <>< (a ∷ as) = (xz , a) <>< as
infixl 4 _<><_

Shub : Cx ⋆ → Cx ⋆ → Set
Shub Γ Δ = ∀ Ξ → Sub (Γ <>< Ξ) (Δ <>< Ξ)

_//_ : ∀ {Γ Δ} (θ : Shub Γ Δ) {τ} → Γ ⊢ τ → Δ ⊢ τ
θ // var i   = θ [] i
θ // lam t   = lam ((θ ∘ (_∷_ _)) // t)
θ // app f s = app (θ // f) (θ // s)

wkr : ∀ {Γ Δ σ} → Ren Γ Δ → Ren (Γ , σ) (Δ , σ)
wkr r zero    = zero
wkr r (suc i) = suc (r i)

ren : ∀ {Γ Δ} → Ren Γ Δ → Shub Γ Δ
ren r []      = var ∘ r
ren r (_ ∷ Ξ) = ren (wkr r) Ξ

wks : ∀ {Γ Δ σ} → Sub Γ Δ → Sub (Γ , σ) (Δ , σ)
wks s zero    = var zero
wks s (suc i) = ren suc // s i

sub : ∀ {Γ Δ} → Sub Γ Δ → Shub Γ Δ
sub s []      = s
sub s (_ ∷ Ξ) = sub (wks s) Ξ

weak : ∀ {Γ} Ξ → Ren Γ (Γ <>< Ξ)
weak []      = id
weak (_ ∷ Ξ) = weak Ξ ∘ suc


-- Auto lambda
------------------------------------------------------------

_<>>_ : ∀ {A} → Cx A → List A → List A
𝓔        <>> ys = ys
(xs , x) <>> ys = xs <>> (x ∷ ys)
infixl 4 _<>>_

rev-lem : ∀ {A} Γ (xs : List A) → (𝓔 <>< (Γ <>> xs)) ≡  ((𝓔 <>< (Γ <>> [])) <>< xs)
rev-lem 𝓔       xs = refl
rev-lem (Γ , x) xs rewrite rev-lem Γ (x ∷ xs) | rev-lem Γ (x ∷ []) = refl

rev-rev : ∀ {A} Γ → 𝓔 {A} <>< (Γ <>> []) ≡ Γ
rev-rev 𝓔       = refl
rev-rev (Γ , x) rewrite rev-lem Γ (x ∷ []) | rev-rev Γ = refl

rev-inj : ∀ {A}(Γ Δ : Cx A) → Γ <>> [] ≡ Δ <>> [] → Γ ≡ Δ
rev-inj Γ Δ p = subst₂ _≡_ (rev-rev Γ) (rev-rev Δ) (cong (_<><_ 𝓔) p)

lem : ∀ {A}(Δ Γ : Cx A) Ξ → Δ <>> [] ≡ Γ <>> Ξ → Γ <>< Ξ ≡ Δ
lem Δ Γ []      p = rev-inj Γ Δ (sym p)
lem Δ Γ (x ∷ Ξ) p = lem Δ (Γ , x) Ξ p

lambda :
  ∀ {Γ σ τ}
  → ((∀ {Δ Ξ} {{_ : Δ <>> [] ≡ Γ <>> (σ ∷ Ξ)}} → Δ ⊢ σ) → Γ , σ ⊢ τ)
  → Γ ⊢ σ ▷ τ
lambda {Γ} f =
  lam (f (λ {Δ} {Ξ} {{q}}
    → subst (λ Γ → Γ ⊢ _) (lem Δ Γ (_ ∷ Ξ) q) (var (weak Ξ zero))))  

myTest : 𝓔 ⊢ (ι ▷ ι) ▷ (ι ▷ ι)
myTest = lambda λ f → lambda λ x → app f (app f x)

-- Normalization
------------------------------------------------------------

mutual
  data _⊨_ (Γ : Cx ⋆) : ⋆ → Set where
    lam : ∀ {σ τ} → Γ , σ ⊨ τ → Γ ⊨ σ ▷ τ
    _$_ : ∀ {τ} → τ ∈ Γ → Γ ⊨⋆ τ → Γ ⊨ ι

  data _⊨⋆_ (Γ : Cx ⋆) : ⋆ → Set where
    []  : Γ ⊨⋆ ι
    _,_ : ∀ {σ τ} → Γ ⊨ σ → Γ ⊨⋆ τ → Γ ⊨⋆ σ ▷ τ

infix 3 _⊨_ _⊨⋆_
infix 3 _$_

_-_ : ∀ (Γ : Cx ⋆) {τ} → τ ∈ Γ → Cx ⋆
𝓔 - ()
(Γ , x) - zero  = Γ
(Γ , x) - suc i = (Γ - i) , x
infixl 6 _-_

_≠_ : ∀ {Γ σ}(i : σ ∈ Γ) → Ren (Γ - i) Γ
zero  ≠ i'     = suc i'
suc i ≠ zero   = zero
suc i ≠ suc i' = suc (i ≠ i')

mutual 
  renNm : ∀ {Γ Δ τ} → Ren Γ Δ → Γ ⊨ τ → Δ ⊨ τ
  renNm r (lam t)  = lam (renNm (wkr r) t)
  renNm r (i $ sp) = r i $ renSp r sp

  renSp : ∀ {Γ Δ τ} → Ren Γ Δ → Γ ⊨⋆ τ → Δ ⊨⋆ τ
  renSp r []       = []
  renSp r (t , sp) = renNm r t , renSp r sp

data Veq? {Γ σ}(i : σ ∈ Γ) : ∀ {τ} → τ ∈ Γ → Set where
  same : Veq? i i
  diff : ∀ {τ}(i' : τ ∈ Γ - i) → Veq? i (i ≠ i')

veq? : ∀ {Γ σ τ}(i : σ ∈ Γ)(i' : τ ∈ Γ) → Veq? i i'
veq? zero zero     = same
veq? zero (suc i') = diff i'
veq? (suc i) zero  = diff zero
veq? (suc i) (suc i') with veq? i i'
veq? (suc i) (suc .i)        | same    = same
veq? (suc i) (suc .(i ≠ i')) | diff i' = diff (suc i')

mutual 
  ⟨_⟶_⟩_ : ∀ {Γ σ τ}(i : σ ∈ Γ) → Γ - i ⊨ σ → Γ ⊨ τ → Γ - i ⊨ τ
  ⟨ i ⟶ s ⟩ lam t    = lam (⟨ suc i ⟶ renNm suc s ⟩ t)
  ⟨ i ⟶ s ⟩ (i' $ ts) with veq? i i'
  ⟨ i ⟶ s ⟩ .i $ ts        | same    = s $$ ⟨ i ⟶ s ⟩⋆ ts
  ⟨ i ⟶ s ⟩ .(i ≠ i') $ ts | diff i' = i' $ ⟨ i ⟶ s ⟩⋆ ts
  infix 2 ⟨_⟶_⟩_

  ⟨_⟶_⟩⋆_ : ∀ {Γ σ τ}(i : σ ∈ Γ) → Γ - i ⊨ σ → Γ ⊨⋆ τ → Γ - i ⊨⋆ τ
  ⟨ i ⟶ s ⟩⋆ []       = []
  ⟨ i ⟶ s ⟩⋆ (t , sp) = (⟨ i ⟶ s ⟩ t) , (⟨ i ⟶ s ⟩⋆ sp)

  _$$_ : ∀ {Γ τ} → Γ ⊨ τ → Γ ⊨⋆ τ → Γ ⊨ ι
  s     $$ []       = s
  lam s $$ (t , sp) = (⟨ zero ⟶ t ⟩ s) $$ sp
  infix 3 _$$_

-- η-expansion
------------------------------------------------------------

intros : Cx ⋆ → ⋆ → Cx ⋆
intros Γ ι       = Γ
intros Γ (τ ▷ σ) = intros (Γ , τ) σ

renIntros : ∀ Γ τ → Ren Γ (intros Γ τ)
renIntros Γ ι       = id
renIntros Γ (τ ▷ σ) = renIntros (Γ , τ) σ ∘ suc

expand : ∀ {Γ} τ → intros Γ τ ⊨ ι → Γ ⊨ τ
expand ι       t = t
expand (τ ▷ σ) t = lam (expand σ t)

mutual 
  η : ∀ {Γ τ} → τ ∈ Γ → Γ ⊨ τ
  η {Γ}{τ} i = expand τ (renIntros Γ τ i $ mkSpine Γ τ)
  
  mkSpine : ∀ Γ τ → intros Γ τ ⊨⋆ τ
  mkSpine Γ ι       = []
  mkSpine Γ (τ ▷ σ) = η (renIntros (Γ , τ) σ zero) , mkSpine (Γ , τ) σ

-- effectfully's version
-- https://github.com/effectfully/DataData/blob/master/STLC/Hereditary.agda#L96
-- how the hell does he come up with this

-- mutual
--   η : ∀ {Γ τ} → τ ∈ Γ → Γ ⊨ τ
--   η i = η* (λ Δ s → weak Δ i $ s)

--   η* : ∀ {τ Γ} → (∀ Δ → Γ <>< Δ ⊨⋆ τ → Γ <>< Δ ⊨ ι) → Γ ⊨ τ
--   η* {ι}     c = c [] []
--   η* {τ ▷ σ} c = lam (η* λ Δ sp → c (τ ∷ Δ) (η (weak Δ zero) , sp))

normalize : ∀ {Γ τ} → Γ ⊢ τ → Γ ⊨ τ
normalize (var i) = η i
normalize (lam t) = lam (normalize t)
normalize (app f s) with normalize f | normalize s
... | lam t | s' = ⟨ zero ⟶ s' ⟩ t

try₁ : 𝓔 ⊨ ((ι ▷ ι) ▷ (ι ▷ ι)) ▷ ((ι ▷ ι) ▷ (ι ▷ ι))
try₁ = normalize (lambda λ x → x)

church₂ : ∀ {τ} → 𝓔 ⊢ (τ ▷ τ) ▷ (τ ▷ τ)
church₂ = lambda λ f → lambda λ x → app f (app f x)

try₂ : 𝓔 ⊨ (ι ▷ ι) ▷ (ι ▷ ι)
try₂ = normalize (app (app church₂ church₂) church₂)

-- Normalization by evaluation
------------------------------------------------------------

data Stop Γ τ : Set where
  var : τ ∈ Γ → Stop Γ τ
  _$_ : ∀ {σ} → Stop Γ (σ ▷ τ) → Γ ⊨ σ → Stop Γ τ

renSt : ∀ {Γ Δ τ} → Ren Γ Δ → Stop Γ τ → Stop Δ τ
renSt r (var x) = var (r x)
renSt r (u $ x) = renSt r u $ renNm r x

stopSp : ∀ {Γ τ} → Stop Γ τ → Γ ⊨⋆ τ → Γ ⊨ ι
stopSp (var x) sp = x $ sp
stopSp (u $ x) sp = stopSp u (x , sp)

mutual 
  Val : Cx ⋆ → ⋆ → Set
  Val Γ τ = Go Γ τ ⊎ Stop Γ τ

  Go : Cx ⋆ → ⋆ → Set
  Go Γ ι       = ⊥
  Go Γ (τ ▷ σ) = ∀ {Δ} → Ren Γ Δ → Val Δ τ → Val Δ σ

renVal : ∀ {Γ Δ} τ → Ren Γ Δ → Val Γ τ → Val Δ τ
renVal ι ren (inj₁ ())
renVal (τ ▷ σ) ren (inj₁ r') = inj₁ (λ r → r' (r ∘ ren))
renVal τ       ren (inj₂ y)  = inj₂ (renSt ren y)

renVals : ∀ θ {Γ Δ} → Ren Γ Δ → ⟦ θ ⟧c (Val Γ) → ⟦ θ ⟧c (Val Δ)
renVals 𝓔       ren c       = tt
renVals (θ , x) ren (v , c) = renVals θ ren v , renVal x ren c

idEnv : ∀ Γ → ⟦ Γ ⟧c (Val Γ)
idEnv 𝓔       = tt
idEnv (Γ , x) = renVals Γ suc (idEnv Γ) , inj₂ (var zero)

quo : ∀ {Γ} τ → Val Γ τ → Γ ⊨ τ
quo ι (inj₁ ())
quo (τ ▷ σ) (inj₁ f) = lam (quo σ (f suc (inj₂ (var zero))))
quo {Γ} τ   (inj₂ s) = expand _ (stopSp (renSt (renIntros Γ τ) s) (mkSpine _ _))

apply : ∀ {Γ σ τ} → Val Γ (σ ▷ τ) → Val Γ σ → Val Γ τ
apply (inj₁ f) s = f id s
apply (inj₂ x) s = inj₂ (x $ quo _ s)

eval : ∀ {Γ Δ τ} → Γ ⊢ τ → ⟦ Γ ⟧c (Val Δ) → Val Δ τ
eval (var i)   γ = ⟦ i ⟧∈ γ
eval (lam t)   γ = inj₁ (λ r v → eval t (renVals _ r γ , v))
eval (app f x) γ = apply (eval f γ) (eval x γ)

normByEval : ∀ {Γ τ} → Γ ⊢ τ → Γ ⊨ τ
normByEval {Γ}{τ} t = quo τ (eval t (idEnv Γ))

