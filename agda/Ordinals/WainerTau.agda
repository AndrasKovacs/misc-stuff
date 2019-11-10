
-- Wainer's τ ordinal from "Slow growing versus fast growing",
-- is the same size as ψ(Ω_ω).

open import Agda.Builtin.FromNat
open import Data.Nat hiding (_⊔_; _<_)
open import Data.Unit
open import Function

iterℕ : {A : Set} → ℕ → (A → A) → A → A
iterℕ zero    f = id
iterℕ (suc n) f = f ∘ iterℕ n f

instance
  Numberℕ : Number ℕ
  Numberℕ .Number.Constraint _ = ⊤
  Numberℕ .Number.fromNat    m = m

infix 3 _<_
data _<_ (n : ℕ) : ℕ → Set where
  here : n < suc n
  suc  : ∀ {m} → n < m → n < suc m

-- Tree ordinal classes up to ω
data Ω' (i : ℕ)(El : ∀ j → j < i → Set) : Set where
  zero : Ω' i El
  suc  : Ω' i El → Ω' i El
  lim  : ∀ j p → (El j p → Ω' i El) → Ω' i El

El : ∀ {i} j → j < i → Set
El j here    = Ω' j El
El j (suc p) = El j p

Ω : ℕ → Set
Ω n = Ω' n El

⇑ : ∀ {i} → Ω i → Ω (suc i)
⇑ zero        = zero
⇑ (suc a)     = suc (⇑ a)
⇑ (lim j p a) = lim j (suc p) (⇑ ∘ a)

ω : ∀ i → Ω (suc i)
ω i = lim i here ⇑

instance
  NumberΩ : ∀ {i} → Number (Ω i)
  NumberΩ .Number.Constraint _    = ⊤
  NumberΩ .Number.fromNat zero    = zero
  NumberΩ .Number.fromNat (suc m) = suc (fromNat m)

iterΩ : ∀ {i} → Ω i → (Ω i → Ω i) → Ω i → Ω i
iterΩ zero        f = id
iterΩ (suc a)     f = f ∘ iterΩ a f
iterΩ (lim j p a) f = λ b → lim j p λ i → iterΩ (a i) f b

-- generalized fast-growing hierarchy
F : ∀ {i} → Ω (suc i) → Ω i → Ω i
F zero              b = suc b
F (suc a)           b = iterΩ b (F a) b
F (lim j here a)    b = F (a b) b
F (lim j (suc p) a) b = lim j p λ i → F (a i) b

F↓ : ∀ {i} → Ω (suc i) → Ω 1
F↓ {zero}  a = a
F↓ {suc i} a = F↓ (F a (ω i))

Ω₀→ℕ : Ω 0 → ℕ
Ω₀→ℕ zero    = zero
Ω₀→ℕ (suc a) = suc (Ω₀→ℕ a)

τ : Ω 1
τ = lim 0 here (λ i → F↓ {Ω₀→ℕ i} 3)

mynumber : ℕ
mynumber = Ω₀→ℕ (F τ 10)
