
-- Solution to: https://coq-math-problems.github.io/Problem1/

open import Data.Nat
open import Data.Nat.Properties
open import Data.Nat.Properties.Simple
open import Induction.Nat
open import Relation.Binary.PropositionalEquality
open import Data.Product
open import Data.Sum
open import Relation.Nullary
open import Relation.Binary
open import Data.Empty
open import Function

decr : (ℕ → ℕ) → Set
decr f = ∀ n → f (suc n) ≤ f n

n-valley : ℕ → (ℕ → ℕ) → ℕ → Set
n-valley n f i = ∀ i' → i' ≤ n → f (suc (i' + i)) ≡ f (i' + i)

module < = StrictTotalOrder strictTotalOrder

¬≤ : ∀ {a b} → a ≢ b → ¬ (a < b) → ¬ (a ≤ b)
¬≤ p q r with ≤⇒≤′ r
... | ≤′-refl    = p refl
... | ≤′-step r' = q (≤′⇒≤ (s≤′s r'))

module _ (f : ℕ → ℕ)(decrf : decr f) where

  n-valley? : ∀ n i → n-valley n f i ⊎ (∃ λ i' → f i' < f i)
  n-valley? n i with <.compare (f (suc i)) (f i)
  ... | tri< a ¬b ¬c = inj₂ (suc i , a)
  ... | tri> ¬a ¬b c = ⊥-elim (¬≤ ¬b ¬a (decrf i))
  n-valley? zero    i | tri≈ ¬a b ¬c = inj₁ (λ {_ z≤n → b})
  n-valley? (suc n) i | tri≈ ¬a b ¬c with n-valley? n (suc i)
  ... | inj₁ p = inj₁ λ {
           zero q → b;
           (suc i') q → trans (cong (f ∘ suc) (sym (+-suc i' i)))
                        (trans (p i' (≤-pred q)) (cong f (+-suc i' i)))}
  ... | inj₂ p rewrite b = inj₂ p

p01 : ∀ f n → decr f → ∃ (n-valley n f)
p01 f n decrf =
  <-rec
    (λ x → ∀ i → f i ≡ x → ∃ (n-valley n f))
    (λ x rec i eq → case (n-valley? f decrf n i) of (λ {
        (inj₁ p) → i , p;
        (inj₂ (i' , p)) → rec (f i') (≤⇒≤′ $ subst (f i' <_) eq p) i' refl}))
    (f 0) 0 refl

