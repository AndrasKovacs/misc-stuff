
-- predicative polymorphic System F
-- Inspired by Conor McBride's "Outrageous but Meaningful Coincidences".

open import Function
open import Data.Nat
open import Data.Fin
open import Data.Empty
open import Data.Unit
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Data.Product
open import Data.Vec hiding (_∈_; module _∈_)

infixr 5 _⇒_ 
data U0 : Set where
  one zero : U0
  _⇒_      : U0 → U0 → U0

data U : Set where
  one zero : U
  _⇒_      : U → U → U
  ∀'       : (U0 → U) → U

embed : U0 → U
embed one = one
embed zero = zero
embed (a ⇒ b) = embed a ⇒ embed b

tvar = embed
ᵏ = const

! : ∀ {n} → Fin n → Vec U0 n → U
! i γ = embed (lookup i γ)

⟦_⟧ᵘ : U → Set
⟦ one   ⟧ᵘ = ⊤
⟦ zero  ⟧ᵘ = ⊥
⟦ a ⇒ b ⟧ᵘ = ⟦ a ⟧ᵘ → ⟦ b ⟧ᵘ
⟦ ∀' t  ⟧ᵘ = ∀ x → ⟦ t x ⟧ᵘ

infixl 5 _,ᵛ_
data Cxt : ℕ → ℕ → Set where
  []    : Cxt 0 0
  _,ᵗ   : ∀ {t v} → Cxt t v → Cxt (suc t) v
  _,ᵛ_  : ∀ {t v} → Cxt t v → (Vec U0 t → U) → Cxt t (suc v)

⟦_⟧ᶜ : ∀ {t v} → Cxt t v → Vec U0 t → Set
⟦ []     ⟧ᶜ []       = ⊤
⟦ Γ ,ᵗ   ⟧ᶜ (x ∷ ts) = ⟦ Γ ⟧ᶜ ts
⟦ Γ ,ᵛ x ⟧ᶜ ts       = ⟦ Γ ⟧ᶜ ts × ⟦ x ts ⟧ᵘ

data _∈_ : ∀ {t v} → (Vec U0 t → U) → Cxt t v → Set where
  []   : ∀ {t v x}{Γ : Cxt t v} → x ∈ (Γ ,ᵛ x)
  _,ᵗ  : ∀ {t v x}{Γ : Cxt t v} → x ∈ Γ → (x ∘ tail) ∈ Γ ,ᵗ 
  _,ᵛ  : ∀ {t v x y}{Γ : Cxt t v} → x ∈ Γ → x ∈ (Γ ,ᵛ y)

lookupVar : ∀ {t v σ ts}{Γ : Cxt t v} → σ ∈ Γ → ⟦ Γ ⟧ᶜ ts → ⟦ σ ts ⟧ᵘ 
lookupVar [] (_ , x) = x
lookupVar {ts = _ ∷ _} (v ,ᵗ) γ = lookupVar v γ
lookupVar (v ,ᵛ) (γ , _) = lookupVar v γ

infix 5 _⊢_
data _⊢_ {t v}(Γ : Cxt t v) : (Vec U0 t → U) → Set where
  var   : ∀ {a} → a ∈ Γ → Γ ⊢ a
  unit  : Γ ⊢ ᵏ one
  magic : ∀ {σ} → Γ ⊢ ᵏ zero → Γ ⊢ σ 
  λ'    : ∀ {b} a → Γ ,ᵛ a ⊢ b → Γ ⊢ λ γ → a γ ⇒ b γ
  app   : ∀ {a b} → Γ ⊢ (λ γ → a γ ⇒ b γ) → Γ ⊢ a → Γ ⊢ b
  Λ     : ∀ {a} → Γ ,ᵗ ⊢ a → Γ ⊢ (λ γ → ∀' (λ τ → a (τ ∷ γ)))
  tapp  : 
    ∀ {a : Vec U0 (suc t) → U} 
    → Γ ⊢ (λ γ → ∀' (λ τ → a (τ ∷ γ))) → 
    (τ : Vec U0 t → U0) → Γ ⊢ (λ γ → a (τ γ ∷ γ))

eval : ∀ {t v σ ts}{Γ : Cxt t v} → Γ ⊢ σ → ⟦ Γ ⟧ᶜ ts → ⟦ σ ts ⟧ᵘ
eval (var x) = lookupVar x
eval unit    = ᵏ tt
eval (magic t) = ⊥-elim ∘ eval t
eval (λ' _ t) γ = λ x → eval t (γ , x)
eval (app a b) = eval a ˢ eval b
eval (Λ t) γ x = eval t γ
eval (tapp t τ) γ = eval t γ (τ _)  

ID : [] ⊢ ᵏ (∀' λ a → tvar a ⇒ tvar a)
ID = Λ (λ' (! zero) (var []))

IDAPP : [] ⊢ λ _ → ∀' (λ z → tvar z ⇒ tvar z) ⇒ ∀' (λ z → tvar z ⇒ tvar z)
IDAPP = 
  λ' _
    (Λ (λ' (! zero)
    (app (
      tapp 
        {a = λ γ → ! zero γ ⇒ ! zero γ} 
        (var ([] ,ᵗ ,ᵛ)) 
        (lookup zero)) 
      (var []))))

CONST : [] ⊢ ᵏ (∀' λ a → ∀' λ b → tvar a ⇒ tvar b ⇒ tvar a)
CONST = Λ (Λ (λ' (! (# 1)) (λ' (! zero) (var ([] ,ᵛ)))))
