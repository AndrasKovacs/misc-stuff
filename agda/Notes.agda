{-# OPTIONS --type-in-type --injective-type-constructors #-}

open import Data.Unit
open import Data.Empty

data J (c : Set → Set) : Set where
  j : c ⊤ → J c

data R : Set → Set₁ where
  mkr : ∀ {c} → (c (J c) → ⊥) → R (J c)

cfalse : R (J R) → ⊥
cfalse (mkr f) = f (mkr f)

