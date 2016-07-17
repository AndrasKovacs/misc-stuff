
open import Data.Product
open import Relation.Binary.PropositionalEquality
open import Level

Eqv : ∀ {α β} → Set α → Set β → Set (α ⊔ β)
Eqv A B =
  ∃ λ (f : A → B) → ∃ λ (g : B → A)
  → (∀ a → g (f a) ≡ a) × (∀ b → f (g b) ≡ b)
  
-- this is the trivial direction in the "(A ~ B) ~ (A ≡ B)" equivalence
idToEqv : ∀ {α}{A B : Set α} → A ≡ B → Eqv A B
idToEqv refl = (λ x → x) , (λ x → x) , (λ x → refl) , (λ x → refl)

-- The other direction along with the inverses' proofs.
-- They must be taken as axioms in most current type theories
postulate
  ua     : ∀ {α}{A B : Set α} → Eqv A B → A ≡ B
  toFrom : ∀ {α}{A B : Set α} → (e : Eqv A B) → idToEqv (ua e) ≡ e
  fromTo : ∀ {α}{A B : Set α} → (e : A ≡ B) → ua (idToEqv e) ≡ e

Univalence : ∀ {α}{A B : Set α} → Eqv (A ≡ B) (Eqv A B)
Univalence = idToEqv , ua , fromTo , toFrom









