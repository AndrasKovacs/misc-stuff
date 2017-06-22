
module HereditarySubst where

data Ty : Set where
  ∙   : Ty
  _⇒_ : Ty → Ty → Ty
infixr 5 _⇒_   

data Con : Set where
  ε   : Con
  _,_ : Con → Ty → Con
infixl 5 _,_

data _∈_ : Ty → Con → Set where
  zero : ∀ {Γ σ} → σ ∈ (Γ , σ)
  suc  : ∀ {Γ σ σ'} → σ ∈ Γ → σ ∈ Γ , σ'
infixr 4 _∈_ 

data _⊢_ (Γ : Con) : Ty → Set where
  var : ∀ {σ} → σ ∈ Γ → Γ ⊢ σ
  lam : ∀ {σ τ} → Γ , σ ⊢ τ → Γ ⊢ σ ⇒ τ
  app : ∀ {σ τ} → Γ ⊢ (σ ⇒ τ) → Γ ⊢ σ → Γ ⊢ τ
infix 3 _⊢_

_-_ : ∀ {σ} Γ → σ ∈ Γ → Con
ε       - ()
(Γ , σ) - zero  = Γ
(Γ , σ) - suc x = Γ - x , σ
infixl 6 _-_

wkv : ∀ {Γ σ τ} (x : σ ∈ Γ) → τ ∈ Γ - x → τ ∈ Γ
wkv zero    y       = suc y
wkv (suc x) zero    = zero
wkv (suc x) (suc y) = suc (wkv x y)

data EqV {Γ}{σ} : ∀ {τ} → σ ∈ Γ → τ ∈ Γ → Set where
  same : ∀ {x} → EqV x x
  diff : ∀ {τ} x (y : τ ∈ Γ - x) → EqV x (wkv x y)

eqv : ∀ {Γ σ τ} (x : σ ∈ Γ)(y : τ ∈ Γ) → EqV x y
eqv zero zero = same
eqv zero (suc y) = diff zero y
eqv (suc x) zero = diff (suc x) zero
eqv (suc x) (suc y) with eqv x y
eqv (suc x) (suc .x)         | same      = same
eqv (suc x) (suc .(wkv x y)) | diff .x y = diff (suc x) (suc y)

mutual 
  data _⊨_ Γ : Ty → Set where
    lam : ∀ {σ τ} → Γ , σ ⊨ τ → Γ ⊨ σ ⇒ τ
    ne  : Ne Γ ∙ → Γ ⊨ ∙
  infix 3 _⊨_

  data Ne Γ : Ty → Set where
    _,_ : ∀ {σ τ} → σ ∈ Γ → Γ ⊨* σ , τ → Ne Γ τ 

  data _⊨*_,_ Γ : Ty → Ty → Set where
    ε   : ∀ {σ} → Γ ⊨* σ , σ 
    _,_ : ∀ {σ τ ρ} → Γ ⊨ σ → Γ ⊨* τ , ρ → Γ ⊨* σ ⇒ τ , ρ
  infix 3 _⊨*_,_

mutual
  wkNf : ∀ {Γ σ τ} (x : τ ∈ Γ) → Γ - x ⊨ σ → Γ ⊨ σ
  wkNf x (lam t)      = lam (wkNf (suc x) t)
  wkNf x (ne (f , s)) = ne (wkv x f , wkSp x s)

  wkSp : ∀ {Γ σ τ ρ} (x : τ ∈ Γ) → Γ - x ⊨* σ , ρ → Γ ⊨* σ , ρ
  wkSp x ε       = ε
  wkSp x (t , s) = wkNf x t , wkSp x s

appSp : ∀ {Γ σ τ ρ} → Γ ⊨* σ , τ ⇒ ρ → Γ ⊨ τ → Γ ⊨* σ , ρ
appSp ε       t = t , ε
appSp (x , s) t = x , appSp s t

open import Relation.Binary.PropositionalEquality

mutual
  η : ∀ {Γ σ} → σ ∈ Γ → Γ ⊨ σ
  η x = η-Ne (x , ε)

  η-Ne : ∀ {σ Γ} → Ne Γ σ → Γ ⊨ σ
  η-Ne {∙}     n       = ne n
  η-Ne {σ ⇒ τ} (x , s) = lam (η-Ne (suc x , appSp (wkSp zero s) (η zero)))

mutual
  ⟨_⟶_⟩_ : ∀ {Γ σ τ} → (x : σ ∈ Γ) → Γ - x ⊨ σ → Γ ⊨ τ → Γ - x ⊨ τ
  ⟨ x ⟶ s ⟩ lam t = lam (⟨ suc x ⟶ wkNf zero s ⟩ t)
  ⟨ x ⟶ s ⟩ ne (y , sp) with eqv x y
  ⟨ x ⟶ s ⟩ ne (.x , sp)         | same      = s ◇ ⟨ x ⟶ s ⟩* sp
  ⟨ x ⟶ s ⟩ ne (.(wkv x y) , sp) | diff .x y = ne (y , ⟨ x ⟶ s ⟩* sp)
  infix 2 ⟨_⟶_⟩_

  ⟨_⟶_⟩*_ : ∀ {Γ σ τ ρ}(x : σ ∈ Γ) → Γ - x ⊨ σ → Γ ⊨* τ , ρ → Γ - x ⊨* τ , ρ
  ⟨ x ⟶ s ⟩* ε        = ε
  ⟨ x ⟶ s ⟩* (t , sp) = (⟨ x ⟶ s ⟩ t) , ⟨ x ⟶ s ⟩* sp

  _◇_ : ∀ {Γ σ τ} → Γ ⊨ σ → Γ ⊨* σ , τ → Γ ⊨ τ
  t ◇ ε      = t
  lam f ◇ s , sp = (⟨ zero ⟶ s ⟩ f) ◇ sp


nfapp : ∀ {Γ σ τ} → Γ ⊨ σ ⇒ τ  → Γ ⊨ σ → Γ ⊨ τ
nfapp (lam t) s = ⟨ zero ⟶ s ⟩ t

infix 3 _◇_

nf : ∀ {Γ σ} → Γ ⊢ σ → Γ ⊨ σ
nf (var x)   = η x
nf (lam t)   = lam (nf t)
nf (app f x) = nfapp (nf f) (nf x)

