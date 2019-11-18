

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

data Ω₁ : Set where
  zero : Ω₁
  suc  : Ω₁ → Ω₁
  lim  : (ℕ → Ω₁) → Ω₁

infix 3 _<_
data _<_ : Ω₁ → Ω₁ → Set where
  suc* : ∀ {a} → a < suc a
  suc  : ∀ {a b} → a < b → a < suc b
  lim* : ∀ {i b} → b i < lim b
  lim  : ∀ {i a b} → a < b i → a < lim b

-- Tree ordinal classes up to ω₁
data Ω' (i : Ω₁)(El : ∀ j → j < i → Set) : Set where
  zero : Ω' i El
  suc  : Ω' i El → Ω' i El
  lim  : ∀ j p → (El j p → Ω' i El) → Ω' i El

El : ∀ {i} j → j < i → Set
El j suc*    = Ω' j El
El j (suc p) = El j p
El j lim*    = Ω' j El
El j (lim p) = El j p

Ω : Ω₁ → Set
Ω n = Ω' n El

⇑ : ∀ {i} → Ω i → Ω (suc i)
⇑ zero        = zero
⇑ (suc a)     = suc (⇑ a)
⇑ (lim j p a) = lim j (suc p) (⇑ ∘ a)

ω : ∀ i → Ω (suc i)
ω i = lim i suc* ⇑

foo : ∀ i → Ω (lim i)
foo i = lim {!!} {!!} {!!}

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
F- : ∀ {i} → Ω (suc i) → Ω i → Ω i
F- zero              b = suc b
F- (suc a)           b = iterΩ b (F- a) b
F- (lim j suc* a)    b = F- (a b) b
F- (lim j (suc p) a) b = lim j p λ i → F- (a i) b

Flim : ∀ {a i} → Ω (lim a) → Ω (a i) → Ω (a i)
Flim = {!!}

postulate
  ω₀→ℕ : Ω zero → ℕ

F↓ : ∀ {i} → Ω (suc i) → Ω (suc zero)
F↓ {zero}  a = a
F↓ {suc i} a = F↓ (F- a (ω i))
F↓ {lim i} a = lim zero suc* λ x → {!!}

-- F< : ∀ {i j} → i < j → Ω j → Ω i
-- F< suc*    a = {!!}
-- F< (suc p) a = {!!}
-- F< lim*    a = {!!}
-- F< (lim p) a = {!!}

-- F↓ : ∀ {i} → Ω (suc i) → Ω 1
-- F↓ {zero}  a = a
-- F↓ {suc i} a = F↓ (F a (ω i))

-- Ω₀→ℕ : Ω 0 → ℕ
-- Ω₀→ℕ zero    = zero
-- Ω₀→ℕ (suc a) = suc (Ω₀→ℕ a)

-- τ : Ω 1
-- τ = lim 0 here (λ i → F↓ {Ω₀→ℕ i} 3)

-- mynumber : ℕ
-- mynumber = Ω₀→ℕ (F τ 10)
