{-# OPTIONS --without-K #-}

open import Data.Nat
open import Relation.Binary.PropositionalEquality

instance  -- we do this to get automatic ≤ proofs in examples
  z≤n' : ∀ {n} → zero  ≤ n
  z≤n' = z≤n
  s≤s' : ∀ {m n} {{m≤n : m ≤ n}} → suc m ≤ suc n
  s≤s' {{p}} = s≤s p

-- Partition is slightly generalized to allow lists ending with 0 A similarly
-- generalized dual function is easy to work with, and it behaves the same as
-- the old dual on non-0-ending lists.

data Partition (hi : ℕ) : ℕ → Set where
  nil  : Partition hi 0
  cons : ∀ {l} x {{_ : x ≤ hi}} → Partition x l → Partition hi (suc l)

zeros : ∀ hi l → Partition hi l
zeros hi zero    = nil
zeros hi (suc l) = cons 0 {{z≤n}} (zeros _ l)

zipsuc : ∀ {l x hi} → x ≤ hi → Partition l x → Partition (suc l) hi
zipsuc z≤n     nil         = zeros _ _
zipsuc (s≤s p) (cons x xs) = cons (suc x) (zipsuc p xs)

-- The basic idea is that "dual" can be viewed as the transposition
-- of a special matrix. For normal Agda matrices, transposition would be:

--   tr []         = replicate []
--   tr (xs ∷ xss) = zipWith _∷_ xs (tr xss)

-- (which is exactly "traverse id" over the zippy Vec Applicative)

-- We may view (Partition hi l) as a decreasing ragged Bool matrix with
-- dimensions hi and l.

dual : ∀ {hi l} → Partition hi l → Partition l hi
dual {hi} nil          = zeros 0 hi
dual (cons x {{p}} xs) = zipsuc p (dual xs)

dual-zeros : ∀ hi l → dual (zeros hi l) ≡ zeros l hi
dual-zeros hi zero = refl
dual-zeros hi (suc l) rewrite dual-zeros 0 l = refl

dual-zipsuc :
  ∀ {hi l} {x} (p : x ≤ hi) (xs : Partition l x) →
    dual (zipsuc p xs) ≡ cons x {{p}} (dual xs)
dual-zipsuc {hi} {l} z≤n nil = dual-zeros (suc l) hi
dual-zipsuc (s≤s p) (cons x xs) rewrite dual-zipsuc p xs = refl

dual-involutive : ∀ {hi l}(xs : Partition hi l) → dual (dual xs) ≡ xs
dual-involutive {hi} nil with dual (zeros 0 hi)
... | nil = refl
dual-involutive (cons x {{p}} xs)
  rewrite dual-zipsuc p (dual xs) | dual-involutive xs = refl

-- examples
------------------------------------------------------------

ex1 : Partition 3 3
ex1 = cons 3 (cons 2 (cons 2 nil))

p1 : dual (dual ex1) ≡ ex1
p1 = refl

ex2 : Partition 5 4
ex2 = cons 4 (cons 4 (cons 3 (cons 0 nil)))

p2 : dual (dual ex2) ≡ ex2
p2 = refl
