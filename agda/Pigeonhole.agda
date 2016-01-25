module Pigeonhole {α}{A : Set α} where

open import Data.Vec
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Data.Empty
open import Data.Product
open import Data.Unit
open import Data.Nat
import Level

Unique : ∀ {n} → Vec A n → Set α
Unique []       = Level.Lift ⊤
Unique (x ∷ xs) = ¬ (x ∈ xs) × Unique xs

_⊆_ : ∀ {n m} → Vec A n → Vec A m → Set α
xs ⊆ ys = ∀ {x} → x ∈ xs → x ∈ ys

remove :
  ∀ {n} x (xs : Vec A (suc n))
  → x ∈ xs → ∃ λ (xs' : Vec A n) → ∀ x' → x' ≢ x → x' ∈ xs → x' ∈ xs'
remove x (_ ∷ xs) here = xs , sub
  where
    sub : ∀ {x} x' → x' ≢ x → x' ∈ (x ∷ xs) → x' ∈ xs
    sub x₁ p1 here       = ⊥-elim (p1 refl)
    sub x' p1 (there p2) = p2  
remove {zero}  x (_  ∷ []) (there ())
remove {suc n} x (x' ∷ xs) (there el) with remove x xs el
... | xs' , sub = (x' ∷ xs') , sub'
  where
    sub' : ∀ {x'} x'' → x'' ≢ x → x'' ∈ (x' ∷ xs) → x'' ∈ (x' ∷ xs')
    sub' x'  p1 here       = here
    sub' x'' p1 (there p2) = there (sub x'' p1 p2)

pigeon : ∀ {n m} (xs : Vec A n) (ys : Vec A m) →  xs ⊆ ys → n > m →  ¬ Unique xs
pigeon []       ys sub () uniq
pigeon {m = zero} (x ∷ xs) [] sub (s≤s z≤n) (x∉xs , uxs) with sub here
... | ()
pigeon {suc n}{suc m} (x ∷ xs) ys sub (s≤s len) (x∉xs , uxs) with remove x ys (sub here)
... | ys' , sub' = pigeon xs ys' (λ p → sub' _ (lem x∉xs p) (sub (there p))) len uxs
  where  
    lem : ∀ {n}{x x' : A}{xs : Vec A n} → ¬ (x ∈ xs) → x' ∈ xs → x' ≢ x
    lem p1 here       refl = p1 here
    lem p1 (there p2) refl = p1 (there p2)  
