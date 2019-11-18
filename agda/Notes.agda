
open import Data.Product
open import Data.Sum
open import Relation.Binary.PropositionalEquality

data W (S : Set)(P : S → Set) : Set where
  lim : ∀ s → (P s → W S P) → W S P

_<_ : ∀ {S P} → W S P → W S P → Set
a < lim s f = ∃ λ p → a ≡ f p ⊎ a < f p
