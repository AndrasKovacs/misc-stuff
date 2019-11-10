
-- Feferman-Schütte ordinal

open import Agda.Builtin.FromNat
open import Data.Nat
open import Data.Unit
open import Function
open import Data.List

iter : {A : Set} → ℕ → (A → A) → A → A
iter zero    f = id
iter (suc n) f = f ∘ iter n f

data Ω₁ : Set where
  zero : Ω₁
  suc  : Ω₁ → Ω₁
  sup  : (ℕ → Ω₁) → Ω₁

-- ℕ literal overloading
instance
  NumberΩ₁ : Number Ω₁
  NumberΩ₁ .Number.Constraint _ = ⊤
  NumberΩ₁ .Number.fromNat    n = iter n suc zero

  Numberℕ : Number ℕ
  Numberℕ .Number.Constraint _ = ⊤
  Numberℕ .Number.fromNat    m = m

-- transfinite iteration
Iter : {A : Set} → Ω₁ → ((ℕ → A → A) → (A → A)) → (A → A) → A → A
Iter zero    s f = id
Iter (suc a) s f = f ∘ Iter a s f
Iter (sup a) s f = s (λ i → Iter (a i) s f)

sup1 : (ℕ → Ω₁ → Ω₁) → Ω₁ → Ω₁
sup1 f a = sup λ i → f i a

sup2 : (ℕ → (Ω₁ → Ω₁) → (Ω₁ → Ω₁)) → (Ω₁ → Ω₁) → Ω₁ → Ω₁
sup2 f g a = sup (λ i → f i g a)

add : Ω₁ → Ω₁ → Ω₁
add a b = Iter b sup1 suc a

mul : Ω₁ → Ω₁ → Ω₁
mul a b = Iter b sup1 (flip add a) 0

exp : Ω₁ → Ω₁ → Ω₁
exp a b = Iter b sup1 (flip mul a) 1

ω : Ω₁
ω = sup λ i → fromNat i

-- least fixpoint which is >= an ordinal
fix≥ : (Ω₁ → Ω₁) → (Ω₁ → Ω₁)
fix≥ f = sup1 λ i → iter i f

-- least fixpoint
fix₀ : (Ω₁ → Ω₁) → Ω₁
fix₀ f = fix≥ f 0

-- enumeration of fixpoints
fix : (Ω₁ → Ω₁) → (Ω₁ → Ω₁)
fix f a = Iter a sup1 (fix≥ f ∘ suc) (fix₀ f)

-- Veblen
φ : Ω₁ → Ω₁ → Ω₁
φ a = Iter a sup2 fix (exp ω)

-- Feferman-Schütte
Γ₀ : Ω₁
Γ₀ = fix₀ (flip φ 0)

-- fast-growing hierarchy
F : Ω₁ → ℕ → ℕ
F zero    n = suc n
F (suc a) n = iter n (F a) n
F (sup a) n = F (a n) n

mynumber : ℕ
mynumber = F Γ₀ 10
