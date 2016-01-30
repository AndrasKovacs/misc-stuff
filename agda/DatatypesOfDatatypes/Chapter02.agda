

open import Data.List
open import Data.Nat
open import Data.Product
open import Data.Unit
open import Function
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

-- alternatively : see Order Preserving Embedding
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

lambda :
  ∀ {Γ σ τ}
  → ((∀ {Ξ} → Γ , σ <>< Ξ ⊢ σ) → Γ , σ ⊢ τ)
  → Γ ⊢ σ ▷ τ
lambda f = lam (f (λ {Ξ} → var (weak Ξ zero)))

_<>>_ : ∀ {A} → Cx A → List A → List A
𝓔        <>> ys = ys
(xs , x) <>> ys = xs <>> (x ∷ ys)
infixl 4 _<>>_


lem : ∀ {A}(Δ Γ : Cx A) Ξ → Δ <>> [] ≡ Γ <>> Ξ → Δ ≡ Γ <>< Ξ
lem Δ Γ []      p = {!!}
lem Δ Γ (x ∷ Ξ) p = lem Δ (Γ , x) Ξ p
