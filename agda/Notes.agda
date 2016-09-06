
{-# OPTIONS --without-K #-}

open import Data.Nat
open import Relation.Binary.PropositionalEquality

ℕ-ind :
  ∀ (ℕ* : ℕ → Set)
  → ℕ* zero → (∀ {n} → ℕ* n → ℕ* (suc n))
  → ∀ n → ℕ* n
ℕ-ind ℕ* zero* suc* zero    = zero*
ℕ-ind ℕ* zero* suc* (suc n) = suc* (ℕ-ind ℕ* zero* suc* n)

J :
  ∀ {A : Set}(P : ∀ {x y : A} → x ≡ y → Set)
  → (∀ {x} → P {x} refl)
  → ∀ {x y} (p : x ≡ y) → P p
J P refl* refl = refl*

⊥ : Set
⊥ = 0 ≡ 1

⊥-ind : ⊥ → ∀ (A : Set)(x y : A) → x ≡ y
⊥-ind bot A x y = cong (ℕ-ind _ x (λ _ → y)) bot


