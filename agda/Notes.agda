{-# OPTIONS --without-K #-}

open import Data.Bool using (Bool; true; false)
open import Data.Empty
open import Data.List
open import Data.Nat hiding (_≤?_)
open import Data.Nat.Properties hiding (_≤?_)
open import Data.Product renaming (proj₁ to ₁; proj₂ to ₂)
open import Data.Unit using (⊤; tt)
open import Function
open import Level renaming (suc to lsuc; zero to lzero)
open import Relation.Binary.PropositionalEquality
  renaming (subst to tr; sym to infix 6 _⁻¹; trans to infixr 5 _◾_; cong to ap; cong₂ to ap2)
open import Relation.Nullary
open import Relation.Nullary.Decidable

_≤?_ : ∀ n m → Dec (n ≤ m)
zero  ≤? m     = yes z≤n
suc n ≤? zero  = no (λ ())
suc n ≤? suc m = map′ s≤s ≤-pred (n ≤? m)

isPartition' : ℕ → List ℕ → Set
isPartition' hi []       = hi > 0
isPartition' hi (x ∷ xs) = hi ≥ x × isPartition' x xs

isPartition : List ℕ → Set
isPartition []       = ⊤
isPartition (x ∷ xs) = isPartition' x xs

countGE : ℕ → List ℕ → ℕ
countGE k [] = 0
countGE k (x ∷ xs) with k ≤? x
... | yes _ = suc (countGE k xs)
... | no  _ = countGE k xs

dual : List ℕ → List ℕ
dual []       = []
dual (x ∷ xs) = applyUpTo (λ k → countGE (suc k) (x ∷ xs)) x

countGE-antitone : ∀ x xs → countGE (suc x) xs ≤ countGE x xs
countGE-antitone x []       = z≤n
countGE-antitone x (y ∷ ys) with x ≤? y | suc x ≤? y
... | yes p | yes q = s≤s (countGE-antitone x ys)
... | yes p | no ¬q = ≤-trans (countGE-antitone x ys) (n≤1+n _)
... | no ¬p | yes q = ⊥-elim (¬p (case q of λ {(s≤s q) → ≤-step q}))
... | no ¬p | no ¬q = countGE-antitone x ys

+-suc-ext : ∀ n → (λ x → n + suc x) ≡ (λ x → suc (n + x))
+-suc-ext zero    = refl
+-suc-ext (suc n) = ap (λ f x → suc (f x)) (+-suc-ext n)

lem1 : ∀ n x xs
       → isPartition' (countGE n (n + x ∷ xs))
                      (applyUpTo (λ k → countGE (suc (n + k)) (n + x ∷ xs)) x)
lem1 n x xs with x | n ≤? (n + x)
... | x'      | no ¬p = ⊥-elim (¬p (≤-stepsʳ x' ≤-refl))
... | zero    | yes p = s≤s z≤n
... | suc x'  | yes p rewrite +-suc n x' | +-identity .₂ n with lem1 (suc n) x' xs
... | hyp with suc n ≤? suc (n + x')
... | no ¬q = ⊥-elim (¬q (s≤s (m≤m+n _ _)))
... | yes q =
    s≤s (countGE-antitone n xs)
  , tr (λ f → isPartition'
                (suc (countGE (suc n) xs))
                (applyUpTo (λ k → countGE (suc (f k)) (suc (n + x') ∷ xs)) x'))
       (+-suc-ext n ⁻¹)
       hyp

lem2 : ∀ x xs → isPartition (applyUpTo (λ k → countGE (suc k) (x ∷ xs)) x)
lem2 zero          xs = tt
lem2 (suc zero)    xs = s≤s z≤n
lem2 (suc (suc x)) xs = s≤s (countGE-antitone 1 xs) , lem1 2 x xs

dual-is-part : ∀ xs → isPartition (dual xs)
dual-is-part []       = tt
dual-is-part (x ∷ xs) = lem2 x xs

lem3 :
  ∀ n x → countGE 1 (applyUpTo (λ x₁ → countGE (suc n + x₁) (n + x ∷ [])) x) ≡ x
lem3 n zero = refl
lem3 n (suc x) rewrite +-suc n x | +-identity .₂ n with suc n ≤? suc (n + x)
... | no ¬q = ⊥-elim (¬q (s≤s (m≤m+n _ _)))
... | yes p = ap suc (tr (λ f → countGE 1
      (applyUpTo (λ x₁ → countGE (suc (f x₁)) (suc n + x ∷ [])) x)
      ≡ x) (+-suc-ext n ⁻¹) (lem3 (suc n) x))

lem6 : ∀ xs → ¬ isPartition' 0 xs
lem6 (.0 ∷ xs) (z≤n , ps) = lem6 xs ps

lem5 : ∀ x xs → isPartition' x xs
              → dual (applyUpTo (λ k → countGE (suc k) (x ∷ xs)) x) ≡ x ∷ xs
lem5 zero    xs p = ⊥-elim (lem6 xs p)
lem5 (suc x) xs p = ap2 _∷_ (ap suc {!!}) {!!}

lem4 : ∀ x → dual (dual (suc x ∷ [])) ≡ (suc x ∷ [])
lem4 zero = refl
lem4 (suc x) = ap ((_∷ []) ∘ suc ∘ suc) (lem3 2 x)

duality : ∀ xs → isPartition xs → dual (dual xs) ≡ xs
duality [] p = refl
duality (x ∷ xs) p = lem5 x xs p
