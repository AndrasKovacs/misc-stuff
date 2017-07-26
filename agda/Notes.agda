
open import Lib

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

data Vec (A : Set) : ℕ → Set where
  []  : Vec A zero
  _∷_ : ∀ {n} → A → Vec A n → Vec A (suc n)
infixr 5 _∷_

zipwith : ∀ {A B C n} → (A → B → C) → Vec A n → Vec B n → Vec C n
zipwith f []       bs       = []
zipwith f (a ∷ as) (b ∷ bs) = f a b ∷ zipwith f as bs



