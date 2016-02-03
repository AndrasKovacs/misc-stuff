

open import Data.List
open import Data.Nat
open import Data.Product
open import Data.Unit
open import Function hiding (_$_)
open import Data.Empty
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

shiftr : ∀ {Γ Δ} Ξ → Ren Γ Δ → Ren (Γ <>< Ξ) (Δ <>< Ξ)
shiftr []      ren = ren
shiftr (_ ∷ Ξ) ren = shiftr Ξ (wkr ren)

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

normalize : ∀ {Γ τ} → Γ ⊢ τ → Γ ⊨ τ
normalize (var i) = η i
normalize (lam t) = lam (normalize t)
normalize (app f s) with normalize f | normalize s
... | lam t | s' = ⟨ zero ⟶ s' ⟩ t


  




