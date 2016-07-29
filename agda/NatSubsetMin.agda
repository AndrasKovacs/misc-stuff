
-- Every nonempty decidable subset of ℕ has a least element

open import Data.Nat
open import Data.Bool
open import Data.Product
open import Relation.Binary.PropositionalEquality
open import Data.Empty
open import Function

_∈_ : {A : Set} → A → (A → Bool) → Set
a ∈ s = s a ≡ true

_lb-of_ : ℕ → (ℕ → Bool) → Set
n lb-of s = ∀ b → b ∈ s → n ≤ b

_min-of_ : ℕ → (ℕ → Bool) → Set
n min-of s = n ∈ s × n lb-of s

minimum : (s : ℕ → Bool)(a : ℕ) → a ∈ s → ∃ (_min-of s)
minimum s n n∈s = find-min n n n∈s (λ _ _ p → p)
  where
    ≤→< : ∀ {a b} → a ≤ b → a ≢ b → a < b
    ≤→< {b = zero}  z≤n neq = ⊥-elim (neq refl)
    ≤→< {b = suc b} z≤n neq = s≤s z≤n
    ≤→< (s≤s p) neq = s≤s (≤→< p (neq ∘ cong suc))

    true≢false : true ≢ false
    true≢false ()

    find-min : ∀ low min → min ∈ s → (∀ x → x ∈ s → low ≤ x → min ≤ x) → ∃ (_min-of s)
    find-min zero      min min∈s bound = min , min∈s , λ x x∈s → bound x x∈s z≤n
    find-min (suc low) min min∈s bound with s low | inspect s low
    ... | true  | [ eq ] = minimum s low eq
    ... | false | [ eq ] = find-min low min min∈s bound'
      where
        bound' = λ x x∈s low≤x → bound x x∈s
          (≤→< low≤x λ p → true≢false (trans (sym x∈s) (trans (cong s (sym p)) eq)))

-- example
open import Relation.Nullary.Decidable

s : ℕ → Bool
s n = ⌊ 10 ≤? n ⌋

test : (proj₁ $ minimum s 30 refl) ≡ 10
test = refl
