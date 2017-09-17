
module UIP where

open import Lib

UIP : ∀ {α}{A : Set α}{a b : A}(p q : a ≡ b) → p ≡ q
UIP refl refl = refl
