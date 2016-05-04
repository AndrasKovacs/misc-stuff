{-# OPTIONS --without-K #-}

{-
TT in TT
  - Separate equalities for each data
  - Parameters + equalities instead of indices  
  - Add El, Σ
-}


open import Relation.Binary.PropositionalEquality
open import Data.Product
open import Data.Nat
open import Function

J :
  ∀ {α β}{A : Set α}(P : (x y : A) → (p : x ≡ y) → Set β)
  → (∀ x → P x x refl)
  → ∀ x y (p : x ≡ y) → P x y p
J P refl* x _ refl = refl* x

-- Ω² : ∀ {α} → Set α → Set α
-- Ω² A = Σ A λ a → 

EckmannHilton :
  ∀ {α}{A : Set α}{a : A}(p : a ≡ a)(r t : p ≡ p)
  → trans r t ≡ trans t r
EckmannHilton {a = a} p r t = {!!}

