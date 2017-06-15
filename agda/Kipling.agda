
{-# OPTIONS --without-K #-}

open import Level renaming (zero to lzero; suc to lsuc)
open import Data.Nat
open import Function
open import Data.Unit.Base
open import Data.Empty
open import Data.Product
open import Relation.Binary.PropositionalEquality hiding ([_])

infix 6 _⁻¹
infixr 5 _◾_

coe : ∀ {α}{A B : Set α} → A ≡ B → A → B
coe refl a = a
ap = cong
_◾_ = trans
_⁻¹ = sym

--------------------------------------------------------------------------------

mutual
  data UU : Set where
    Π*    : (A : UU) → (EL A → UU) → UU
    nat*  : UU
    unit* : UU

  EL : UU → Set
  EL (Π* A B) = (a : EL A) → EL (B a)
  EL nat*     = ℕ
  EL unit*    = ⊤

--------------------------------------------------------------------------------

infixl 6 _▷_ _▷'_

Con' = Set
Ty'  = λ (Γ : Con') → Γ → Set
Var' = λ (Γ : Con')(A : Ty' Γ) → (α : Γ) → A α
Tm'  = λ (Γ : Con')(A : Ty' Γ) → (α : Γ) → A α

data Con : Set₁
⟦_⟧ᶜ     : Con → Con'

data Ty  : Con' → Set₁
⟦_⟧ᵗ     : ∀ {Γ} → Ty Γ → Ty' Γ

data Var : (Γ : Con') → Ty' Γ → Set₁
⟦_⟧ᵛ     : ∀ {Γ A} → Var Γ A → Var' Γ A

data Tm  : (Γ : Con') → Ty' Γ → Set₁
⟦_⟧      : ∀ {Γ A} → Tm Γ A → Tm' Γ A

data Con where
  ∙   : Con
  _▷_ : ∀ Γ → Ty ⟦ Γ ⟧ᶜ → Con

_▷'_ : (Γ : Con') → Ty' Γ → Con'
Γ ▷' A = Σ Γ A

∙' = ⊤

⟦ ∙     ⟧ᶜ = ∙'
⟦ Γ ▷ A ⟧ᶜ = ⟦ Γ ⟧ᶜ ▷' ⟦ A ⟧ᵗ

U'  = λ {Γ : Con'}(_ : Γ) → UU
El' = λ {Γ : Con'}(t : Γ → UU)(α : Γ) → EL (t α)

data Ty where
  U     : ∀ {Γ} → Ty Γ
  El    : ∀ {Γ} → Tm Γ U' → Ty Γ

Π' : ∀ {Γ : Con'} → (A : Tm' Γ U') → (Tm' (Γ ▷' El' A) U') → Tm' Γ U'
Π' A B α = Π* (A α) (λ a → B (α , a))

⟦ U        ⟧ᵗ = U'
⟦ El t     ⟧ᵗ = El' ⟦ t ⟧

π₁ = proj₁
π₂ = proj₂

vs'ᵗ : ∀ {Γ A} → Ty' Γ → Ty' (Γ ▷' A)
vs'ᵗ A = A ∘ π₁

data Var where
  vz : ∀ {Γ A} → Var (Γ ▷' A) (vs'ᵗ A)
  vs : ∀ {Γ B A} → Var Γ A → Var (Γ ▷' B) (vs'ᵗ A)

vz' = π₂

vs' : ∀ {Γ : Con'}{A : Ty' Γ}{B} → Tm' Γ A → Tm' (Γ ▷' B) (vs'ᵗ A)
vs' v = v ∘ π₁

⟦ vz   ⟧ᵛ = vz'
⟦ vs v ⟧ᵛ = vs' ⟦ v ⟧ᵛ

infixl 8 _★_
_★_ = _ˢ_
lam' = curry

unit' = λ {Γ : Con'}(_ : Γ) → unit*
nat'  = λ {Γ : Con'}(_ : Γ) → nat*
tt'   = λ {Γ : Con'}(_ : Γ) → ⊤ ∋ tt
zero' = λ {Γ : Con'}(_ : Γ) → zero
suc'  = λ {Γ : Con'}(n : Γ → ℕ)(α : Γ) → suc (n α)

ℕE : ∀ {α}(P : ℕ → Set α) → P zero → (∀ n → P n → P (suc n)) → ∀ n → P n
ℕE P z s zero    = z
ℕE P z s (suc n) = s n (ℕE P z s n)

natE' :
  ∀ {Γ : Con'}
  → (P : Ty' (Γ ▷' El' nat'))
  → Tm' Γ (lam' P ★ zero')
  → Tm' (Γ ▷' El' nat' ▷' (lam' P ∘ π₁) ★ vz') ((lam' P ∘ π₁ ∘ π₁) ★ suc' (vs' vz')) 
  → (n : Tm' Γ (El' nat'))
  → Tm' Γ (lam' P ★ n)
natE' P z s n α = ℕE (λ x → P (α , x)) (z α) (λ n nᴾ → s ((α , n) , nᴾ)) (n α)
  
data Tm where
  var  : ∀ {Γ A} → Var Γ A → Tm Γ A
  lam  : ∀ {Γ A B} → Tm (Γ ▷' El' A) (El' B) → Tm Γ (El' (Π' A B))
  app  : ∀ {Γ A B} → Tm Γ (El' (Π' A B)) → (t : Tm Γ (El' A)) → Tm Γ (El' (lam' B ★ ⟦ t ⟧))
  Π    : ∀ {Γ} (A : Tm Γ U') → Tm (Γ ▷' El' ⟦ A ⟧) U' → Tm Γ U'
  
  nat  : ∀ {Γ} → Tm Γ U'
  
  natE :
    ∀ {Γ}
    → (P : Ty (Γ ▷' El' nat'))
    → Tm Γ (lam' ⟦ P ⟧ᵗ ★ zero')
    → Tm (Γ ▷' El' nat' ▷' (lam' ⟦ P ⟧ᵗ ∘ π₁) ★ vz') ((lam' ⟦ P ⟧ᵗ ∘ π₁ ∘ π₁) ★ suc' (vs' vz')) 
    → (n : Tm Γ (El' nat'))
    → Tm Γ (lam' ⟦ P ⟧ᵗ ★ ⟦ n ⟧)
    
  zero : ∀ {Γ} → Tm Γ (El' nat')
  suc  : ∀ {Γ} → Tm Γ (El' nat') → Tm Γ (El' nat')
  
  unit : ∀ {Γ} → Tm Γ U'
  tt   : ∀ {Γ} → Tm Γ (El' unit')

⟦ var v        ⟧ = ⟦ v ⟧ᵛ
⟦ lam t        ⟧ = lam' ⟦ t ⟧
⟦ app t u      ⟧ = ⟦ t ⟧ ★ ⟦ u ⟧
⟦ Π A B        ⟧ = Π' ⟦ A ⟧ ⟦ B ⟧
⟦ nat          ⟧ = nat'
⟦ zero         ⟧ = zero'
⟦ suc n        ⟧ = suc' ⟦ n ⟧
⟦ unit         ⟧ = unit'
⟦ tt           ⟧ = tt'
⟦ natE P z s n ⟧ = natE' ⟦ P ⟧ᵗ ⟦ z ⟧ ⟦ s ⟧ ⟦ n ⟧

--------------------------------------------------------------------------------

foo : Tm (∙' ▷' El' unit') (El' unit')
foo = var vz

bar : Tm ∙' U'
bar = natE U nat (Π nat nat) zero

baz : Tm ∙' (El' nat')
baz = app (lam (var vz)) zero

apps   : ∀ {Γ A} → Tm Γ A → ℕ
appsTy : ∀ {Γ} → Ty Γ → ℕ

appsTy U            = 0
appsTy (El t)       = apps t
apps (var x)        = 0
apps (lam t)        = apps t
apps (app t u)      = 1 + apps t + apps u
apps (Π a b)        = apps a + apps b
apps nat            = 0
apps (natE P z s n) = appsTy P + apps z + apps s + apps n
apps zero           = 0
apps (suc t)        = apps t
apps unit           = 0
apps tt             = 0


