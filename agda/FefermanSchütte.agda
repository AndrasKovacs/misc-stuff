
-- Feferman-Schütte ordinal

open import Agda.Builtin.FromNat
open import Data.Nat
open import Data.Unit
open import Function

iter : {A : Set} → ℕ → (A → A) → A → A
iter zero    f = id
iter (suc n) f = f ∘ iter n f

data O : Set where
  zero : O
  suc  : O → O
  sup  : (ℕ → O) → O

-- ℕ literal overloading
instance
  NumberO : Number O
  NumberO .Number.Constraint _ = ⊤
  NumberO .Number.fromNat    n = iter n suc zero

  Numberℕ : Number ℕ
  Numberℕ .Number.Constraint _ = ⊤
  Numberℕ .Number.fromNat    m = m

add : O → O → O
add a zero    = a
add a (suc b) = suc (add a b)
add a (sup b) = sup λ i → add a (b i)

mul : O → O → O
mul a zero    = 0
mul a (suc b) = add (mul a b) a
mul a (sup b) = sup λ i → mul a (b i)

exp : O → O → O
exp a zero    = 1
exp a (suc b) = mul (exp a b) a
exp a (sup b) = sup λ i → exp a (b i)

ω : O
ω = sup λ i → fromNat i

-- least fixpoint
lfix : (O → O) → O
lfix f = sup λ i → iter i f 0

-- least fixpoint above given ordinal
nextfix : (O → O) → O → O
nextfix f a = sup λ i → iter i f (suc a)

-- enumeration of fixpoints
fix : (O → O) → O → O
fix f zero    = lfix f
fix f (suc a) = nextfix f (fix f a)
fix f (sup a) = sup λ i → fix f (a i)

-- pointwise supremum
sup* : (ℕ → O → O) → O → O
sup* f a = sup λ i → f i a

-- binary Veblen function
φ : O → O → O
φ zero    = exp ω
φ (suc a) = fix (φ a)
φ (sup a) = sup* (φ ∘ a)
-- alternatively: φ (sup a) = fix (sup* (φ ∘ a))

-- Feferman-Schütte ordinal
Γ₀ : O
Γ₀ = lfix λ a → φ a 0

-- fast-growing hierarchy
FGH : O → ℕ → ℕ
FGH zero    n = suc n
FGH (suc a) n = iter n (FGH a) n
FGH (sup a) n = FGH (a n) n

mynumber : ℕ
mynumber = FGH Γ₀ 99
