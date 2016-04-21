
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
