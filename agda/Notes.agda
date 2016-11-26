
open import Relation.Binary.PropositionalEquality
open import Data.Nat
open import Data.Product
open import Data.Empty
open import Relation.Nullary
open import Function

≤⇒< : ∀ {a b} → a ≤ b → a ≢ b → a < b
≤⇒< {b = zero}  z≤n      p2 = ⊥-elim (p2 refl)
≤⇒< {b = suc b} z≤n      p2 = s≤s z≤n
≤⇒<             (s≤s p1) p2 = s≤s (≤⇒< p1 (p2 ∘ cong suc))

-- divMod n with (suc d)
divMod : ∀ n d → ∃₂ λ m k → (n ≡ m + k * suc d) × (m ≤ d)
divMod zero    d = zero , zero , refl , z≤n
divMod (suc n) d with divMod n d
... | m , k , p1 , p2 with m ≟ d
divMod (suc n) d | .d , k , p1 , p2 | yes refl = 0 , suc k , cong suc p1 , z≤n
... | no ¬p = suc m , k , cong suc p1 , ≤⇒< p2 ¬p

exp : ℕ → ℕ → ℕ
exp a zero    = 1
exp a (suc b) = a * exp a b

log : ∀ n d → ∃₂ λ e m → suc n ≡ m + exp (suc d) e
log zero    d = 0 , 0 , refl
log (suc n) d = {!!}


-- log2 :: 

-- 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16
-- 0 1 1 2 2 2 2 3 3 3  3  3  3  3  3  4
-- 0 0 1 0 1 2 3 0 1 2  3  4  5  6  7  0

-- suc n = m + (suc (suc d))^k 





