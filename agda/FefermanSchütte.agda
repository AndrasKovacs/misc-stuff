
-- Feferman-Schütte ordinal

open import Agda.Builtin.FromNat
open import Data.Nat
open import Data.Unit
open import Function
open import Data.List

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

-- transfinite iteration, given a way for taking supremum of functions
Iter : {A : Set} → O → ((ℕ → A → A) → (A → A)) → (A → A) → A → A
Iter zero    s f = id
Iter (suc a) s f = f ∘ Iter a s f
Iter (sup a) s f = s (λ i → Iter (a i) s f)

sup1 : (ℕ → O → O) → O → O
sup1 f a = sup λ i → f i a

sup2 : (ℕ → (O → O) → (O → O)) → (O → O) → O → O
sup2 f g a = sup (λ i → f i g a)

add : O → O → O
add a b = Iter b sup1 suc a

mul : O → O → O
mul a b = Iter b sup1 (flip add a) a

exp : O → O → O
exp a b = Iter b sup1 (flip mul a) a

ω : O
ω = sup λ i → fromNat i

-- least fixpoint which is >= an ordinal
fix≥ : (O → O) → (O → O)
fix≥ f = sup1 λ i → iter i f

-- least fixpoint
fix₀ : (O → O) → O
fix₀ f = fix≥ f 0

-- enumeration of fixpoints
fix : (O → O) → (O → O)
fix f a = Iter a sup1 (fix≥ f ∘ suc) (fix₀ f)

-- Veblen
φ : O → O → O
φ a = Iter a sup2 fix (exp ω)

-- Feferman-Schütte
Γ₀ : O
Γ₀ = fix₀ (flip φ 0)

-- fast-growing hierarchy
FGH : O → ℕ → ℕ
FGH zero    n = suc n
FGH (suc a) n = iter n (FGH a) n
FGH (sup a) n = FGH (a n) n

mynumber : ℕ
mynumber = FGH Γ₀ 99
