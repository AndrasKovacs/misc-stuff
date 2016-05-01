
-- J equivalent to subst + singletons are contractible

open import Data.Product
open import Relation.Binary.PropositionalEquality

IsContr : ∀ {α} → Set α → Set α
IsContr A = ∃ λ (a : A) → ∀ a' → a' ≡ a

Sing : ∀ {α} → (A : Set α) → A → Set α
Sing A a = ∃ λ b → a ≡ b

singContr : ∀ {α A} a → IsContr (Sing {α} A a)
singContr a = (a , refl) , (λ {(_ , refl) → refl})

J :
  ∀ {α β}{A : Set α}(P : (x y : A) → (p : x ≡ y) → Set β)
  → (∀ x → P x x refl)
  → ∀ x y (p : x ≡ y) → P x y p
J P refl* x y p = subst (uncurry (P x)) (sym (proj₂ (singContr x) _)) (refl* x)
