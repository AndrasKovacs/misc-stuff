
open import Data.Nat
open import Data.Fin


next : ∀ {n} → Fin n → Fin n
next {zero} ()
next {suc zero}    zero = zero
next {suc (suc n)} zero = suc zero
next {suc n}    (suc f) = suc (next f)
