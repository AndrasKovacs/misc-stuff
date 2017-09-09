

open import Lib


ap : {A B : Set}(f : A → B){t u : A} → t ≡ u → f u ≡ f t
ap f {t}{u} eq = coe ((λ x → f x ≡ f t) & eq) (refl {_}{_}{f t}) -- J (λ {u} _ → f t ≡ f u) (refl {_}{_}{f t}) eq


-- open import Relation.Binary.PropositionalEquality

-- data ℕ : Set where
--   zero : ℕ
--   suc  : ℕ → ℕ

-- foo : ℕ
-- foo = _

-- bar : foo ≡ zero
-- bar = refl

-- foo : Set
-- foo = a
--   where
--   a : Set
--   a = _

--   data ℕ : Set where
--     zero : ℕ
--     suc  : ℕ → ℕ

--   b : a
--   b = zero

-- a : Set
-- a = _

-- b : a
-- b = zero
