
module BachmannHoward where

open import Agda.Builtin.FromNat
open import Data.Nat
open import Data.Unit
open import Function

iterℕ : {A : Set} → ℕ → (A → A) → A → A
iterℕ zero    f = id
iterℕ (suc n) f = f ∘ iterℕ n f

------------------------------------------------------------

data Ω₁ : Set where
  zero : Ω₁
  suc  : Ω₁ → Ω₁
  sup  : (ℕ → Ω₁) → Ω₁

data Ω₂ : Set where
  zero  : Ω₂
  suc   : Ω₂ → Ω₂
  supℕ  : (ℕ → Ω₂) → Ω₂
  supΩ₁ : (Ω₁ → Ω₂) → Ω₂

------------------------------------------------------------

ℕ→Ω₁ : ℕ → Ω₁
ℕ→Ω₁ zero    = zero
ℕ→Ω₁ (suc n) = suc (ℕ→Ω₁ n)

Ω₁→Ω₂ : Ω₁ → Ω₂
Ω₁→Ω₂ zero    = zero
Ω₁→Ω₂ (suc a) = suc (Ω₁→Ω₂ a)
Ω₁→Ω₂ (sup a) = supℕ (Ω₁→Ω₂ ∘ a)

instance
  NumberΩ₁ : Number Ω₁
  NumberΩ₁ .Number.Constraint _    = ⊤
  NumberΩ₁ .Number.fromNat n = ℕ→Ω₁ n

  Numberℕ : Number ℕ
  Numberℕ .Number.Constraint _ = ⊤
  Numberℕ .Number.fromNat    m = m

  NumberΩ₂ : Number Ω₂
  NumberΩ₂ .Number.Constraint _ = ⊤
  NumberΩ₂ .Number.fromNat n    = Ω₁→Ω₂ (ℕ→Ω₁ n)

------------------------------------------------------------

addΩ₁ : Ω₁ → Ω₁ → Ω₁
addΩ₁ a zero    = a
addΩ₁ a (suc b) = suc (addΩ₁ a b)
addΩ₁ a (sup b) = sup (addΩ₁ a ∘ b)

mulΩ₁ : Ω₁ → Ω₁ → Ω₁
mulΩ₁ a zero    = 0
mulΩ₁ a (suc b) = addΩ₁ (mulΩ₁ a b) a
mulΩ₁ a (sup b) = sup (mulΩ₁ a ∘ b)

expΩ₁ : Ω₁ → Ω₁ → Ω₁
expΩ₁ a zero    = 1
expΩ₁ a (suc b) = mulΩ₁ (expΩ₁ a b) a
expΩ₁ a (sup b) = sup (expΩ₁ a ∘ b)

ω₀ : Ω₁
ω₀ = sup ℕ→Ω₁

fixΩ₁≥ : (Ω₁ → Ω₁) → (Ω₁ → Ω₁)
fixΩ₁≥ f a = sup λ i → iterℕ i f a

lfpΩ₁ : (Ω₁ → Ω₁) → Ω₁
lfpΩ₁ f = fixΩ₁≥ f 0

ε₀ : Ω₁
ε₀ = lfpΩ₁ (expΩ₁ ω₀)

------------------------------------------------------------

addΩ₂ : Ω₂ → Ω₂ → Ω₂
addΩ₂ a zero     = a
addΩ₂ a (suc b)  = suc (addΩ₂ a b)
addΩ₂ a (supℕ b) = supℕ (addΩ₂ a ∘ b)
addΩ₂ a (supΩ₁ b) = supΩ₁ (addΩ₂ a ∘ b)

mulΩ₂ : Ω₂ → Ω₂ → Ω₂
mulΩ₂ a zero     = 0
mulΩ₂ a (suc b)  = addΩ₂ (mulΩ₂ a b) a
mulΩ₂ a (supℕ b) = supℕ (mulΩ₂ a ∘ b)
mulΩ₂ a (supΩ₁ b) = supΩ₁ (mulΩ₂ a ∘ b)

expΩ₂ : Ω₂ → Ω₂ → Ω₂
expΩ₂ a zero     = 1
expΩ₂ a (suc b)  = mulΩ₂ (expΩ₂ a b) a
expΩ₂ a (supℕ b) = supℕ (expΩ₂ a ∘ b)
expΩ₂ a (supΩ₁ b) = supΩ₁ (expΩ₂ a ∘ b)

fixΩ₂≥ : (Ω₂ → Ω₂) → (Ω₂ → Ω₂)
fixΩ₂≥ f a = supℕ λ i → iterℕ i f a

lfpΩ₂ : (Ω₂ → Ω₂) → Ω₂
lfpΩ₂ f = fixΩ₂≥ f 0

Ω : Ω₂
Ω = supΩ₁ Ω₁→Ω₂

ψ : Ω₂ → Ω₁
ψ zero      = ε₀
ψ (suc a)   = lfpΩ₁ (expΩ₁ (ψ a))
ψ (supℕ a)  = sup (ψ ∘ a)
ψ (supΩ₁ a) = lfpΩ₁ (ψ ∘ a)

Bachmann-Howard : Ω₁
Bachmann-Howard = ψ (lfpΩ₂ (expΩ₂ Ω))

-- fast-growing hierarchy
F : Ω₁ → ℕ → ℕ
F zero    n = suc n
F (suc a) n = iterℕ n (F a) n
F (sup a) n = F (a n) n

mynumber : ℕ
mynumber = F Bachmann-Howard 10
