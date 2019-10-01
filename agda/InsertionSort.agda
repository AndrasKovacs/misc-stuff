{-# OPTIONS --without-K #-}

open import Data.Nat
open import Data.Sum renaming (map to smap)
open import Data.List renaming (map to lmap)
open import Data.Unit hiding (_≤_)
open import Data.Empty
open import Data.Product
open import Relation.Binary.PropositionalEquality

-- insertion sort
--------------------------------------------------------------------------------

cmpℕ : ∀ a b → a ≤ b ⊎ b ≤ a
cmpℕ zero    b       = inj₁ z≤n
cmpℕ (suc a) zero    = inj₂ z≤n
cmpℕ (suc a) (suc b) = smap s≤s s≤s (cmpℕ a b)

insert : ℕ → List ℕ → List ℕ
insert x []       = x ∷ []
insert x (y ∷ xs) with cmpℕ x y
... | inj₁ _ = x ∷ y ∷ xs
... | inj₂ _ = y ∷ insert x xs

sort : List ℕ → List ℕ
sort []       = []
sort (x ∷ xs) = insert x (sort xs)

-- ordering
--------------------------------------------------------------------------------

Ordered : ℕ → List ℕ → Set
Ordered b []       = ⊤
Ordered b (x ∷ xs) = b ≤ x × Ordered x xs

ins-ord : ∀ b x xs → b ≤ x → Ordered b xs → Ordered b (insert x xs)
ins-ord b x []       b≤x Ord-xs = b≤x , tt
ins-ord b x (y ∷ ys) b≤x (b≤y , Ord-ys) with cmpℕ x y
... | inj₁ p = b≤x , p , Ord-ys
... | inj₂ p = b≤y , ins-ord y x ys p Ord-ys

sort-ord : ∀ xs → Ordered 0 (sort xs)
sort-ord []       = tt
sort-ord (x ∷ xs) = ins-ord 0 x (sort xs) z≤n (sort-ord xs)

-- permutation
--------------------------------------------------------------------------------

data _▶_≡_ {A : Set}(x : A) : List A → List A → Set where
  here  : ∀ {xs} → x ▶ xs ≡ (x ∷ xs)
  there : ∀ {y xs ys} → x ▶ xs ≡ ys → x ▶ (y ∷ xs) ≡ (y ∷ ys)

Perm : {A : Set} → List A → List A → Set
Perm []       ys = ys ≡ []
Perm (x ∷ xs) ys = ∃₂ λ ys' (p : x ▶ ys' ≡ ys) → Perm xs ys'

ins-lem : ∀ x xs → x ▶ xs ≡ insert x xs
ins-lem x []       = here
ins-lem x (y ∷ ys) with cmpℕ x y
... | inj₁ _ = here
... | inj₂ _ = there (ins-lem x ys)

sort-perm : ∀ xs → Perm xs (sort xs)
sort-perm []       = refl
sort-perm (x ∷ xs) = _ , ins-lem x (sort xs) , sort-perm xs
