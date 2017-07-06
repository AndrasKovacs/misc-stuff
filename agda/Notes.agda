
open import Data.Nat

data Vec (A : Set) : ℕ → Set where
  []  : Vec A zero
  _∷_ : ∀ {n} → A → Vec A n → Vec A (suc n)

foo : Vec (ℕ → ℕ) zero
foo = {!!}


-- data VecA
-- data VecB
-- data VecC

infixr 5 _∷_


