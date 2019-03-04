
open import Relation.Binary.PropositionalEquality
open import Data.Sum
open import Function
open import Data.Empty

data Ty : Set where
  ι   : Ty
  _⇒_ : Ty → Ty → Ty
infixr 5 _⇒_

data Con : Set where
  ∙   : Con
  _▶_ : Con → Ty → Con
infixl 5 _▶_

data Var : Con → Ty → Set where
  zero : ∀ {Γ A} → Var (Γ ▶ A) A
  suc  : ∀ {Γ A B} → Var Γ A → Var (Γ ▶ B) A

data Tm (Γ : Con) : Ty → Set where
  var : ∀ {A} → Var Γ A → Tm Γ A
  lam : ∀ {A B} → Tm (Γ ▶ A) B → Tm Γ (A ⇒ B)
  app : ∀ {A B} → Tm Γ (A ⇒ B) → Tm Γ A → Tm Γ B

_-_ : ∀ {A} Γ → Var Γ A → Con
∙       - ()
(Γ ▶ A) - zero  = Γ
(Γ ▶ A) - suc x = Γ - x ▶ A
infixl 6 _-_

wkv : ∀ {Γ A B} (x : Var Γ A) → Var (Γ - x) B → Var Γ B
wkv zero    y       = suc y
wkv (suc x) zero    = zero
wkv (suc x) (suc y) = suc (wkv x y)

eqv : ∀ {Γ A B} (x : Var Γ A)(y : Var Γ B) → (A ≡ B) ⊎ Var (Γ - x) B
eqv zero    zero    = inj₁ refl
eqv zero    (suc y) = inj₂ y
eqv (suc x) zero    = inj₂ zero
eqv (suc x) (suc y) = Data.Sum.map id suc (eqv x y)

mutual
  data Nf Γ : Ty → Set where
    lam : ∀ {A B} → Nf (Γ ▶ A) B → Nf Γ (A ⇒ B)
    ne  : ∀ {A} → Var Γ A → Sp Γ A ι → Nf Γ ι

  data Sp (Γ : Con) : Ty → Ty → Set where
    []  : ∀ {A}     → Sp Γ A A
    _∷_ : ∀ {A B C} → Nf Γ A → Sp Γ B C → Sp Γ (A ⇒ B) C
  infixr 4 _∷_

mutual
 wkNf : ∀ {Γ A B}(x : Var Γ B) → Nf (Γ - x) A → Nf Γ A
 wkNf x (lam t)   = lam (wkNf (wkv zero x) t)
 wkNf x (ne y sp) = ne (wkv x y) (wkSp x sp)

 wkSp : ∀ {Γ A B C} (x : Var Γ C) → Sp (Γ - x) A B → Sp Γ A B
 wkSp x []       = []
 wkSp x (t ∷ sp) = wkNf x t ∷ wkSp x sp

snocSp : ∀ {Γ A B C} → Sp Γ A (B ⇒ C) → Nf Γ B → Sp Γ A C
snocSp []       u = u ∷ []
snocSp (t ∷ sp) u = t ∷ snocSp sp u

mutual
  η : ∀ {Γ A} → Var Γ A → Nf Γ A
  η x = η' x []

  η' : ∀ {Γ A B} → Var Γ A → Sp Γ A B → Nf Γ B
  η' {B = ι}     x sp = Nf.ne x sp
  η' {B = A ⇒ B} x sp = lam (η' (wkv zero x) (snocSp (wkSp zero sp) (η zero)))

mutual
  Nfₛ : ∀ {Γ A B}(x : Var Γ A) → Nf (Γ - x) A → Nf Γ B → Nf (Γ - x) B
  Nfₛ x t (lam u)   = lam (Nfₛ (wkv zero x) (wkNf zero t) u)
  Nfₛ x t (ne y sp) with eqv x y | Spₛ x t sp
  ... | inj₁ refl  | sp' = appSp t sp'
  ... | inj₂ y'    | sp' = ne y' sp'

  Spₛ : ∀ {Γ A B C}(x : Var Γ C) → Nf (Γ - x) C → Sp Γ A B → Sp (Γ - x) A B
  Spₛ x t []       = []
  Spₛ x t (u ∷ sp) = Nfₛ x t u ∷ Spₛ x t sp

  appSp : ∀ {Γ A B} → Nf Γ A → Sp Γ A B → Nf Γ B
  appSp t       []       = t
  appSp (lam t) (u ∷ sp) = appSp (Nfₛ zero u t) sp

nf : ∀ {Γ A} → Tm Γ A → Nf Γ A
nf (var x)   = η x
nf (lam t)   = lam (nf t)
nf (app t u) with nf t | nf u
... | lam t' | u' = Nfₛ zero u' t'

consistent : Tm ∙ ι → ⊥
consistent t = case nf t of λ {(ne () _)}
