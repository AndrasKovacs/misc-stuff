
-- from Launchbury et al.'s http://arxiv.org/pdf/1309.5135.pdf

open import Data.Nat
open import Data.List
open import Data.Unit
open import Function
open import Data.Maybe
open import Data.Product
open import Data.Bool

H : Set → Set → ℕ → Set
H A B zero    = ⊤
H A B (suc n) = (H A B n → A) → B

_#_ : ∀ {m n A B} → (H B A m → B) → (H A B n → A) → B
_#_ {zero}  g f = g tt
_#_ {suc m} g f = g (_#_ f)

foldListH : {A B C : Set} → (as : List A) → (A → B → C) → C → H C B (length as) → C
foldListH []       f z k = z
foldListH (a ∷ as) f z k = f a (k (foldListH as f z))

zipWithH : ∀ {A B C} → (A → B → C) → List A → List B → List C
zipWithH {A}{B}{C} f as bs =
    foldListH as (λ a → maybe′ (λ {(g , abs) → g a ∷ abs}) []) []
  # foldListH bs (λ b cs → just (flip f b , cs)) nothing

foldℕH : ∀ {A B} n → (A → B) → B → H B A n → B
foldℕH zero    s z k = z
foldℕH (suc n) s z k = s (k (foldℕH n s z))

min : ℕ → ℕ → ℕ
min m n = foldℕH m suc 0 # foldℕH n id 0

-- minus in O(n + m) using only folds!
minus : ℕ → ℕ → ℕ
minus a b = length $ filter id $ zipWithH _∧_ as abs
  where as  = replicate a true
        abs = replicate b false ++ as
