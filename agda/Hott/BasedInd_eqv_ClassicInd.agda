
open import Data.Product
open import Relation.Binary.PropositionalEquality
open import Function
open import Level

JT : ∀ {α β} → Set _
JT {α}{β} =
  ∀ {A : Set α}(P : (x y : A) → (p : x ≡ y) → Set β)
  → (∀ x → P x x refl)
  → ∀ x y (p : x ≡ y) → P x y p

JT' : ∀ {α β} → Set _
JT' {α}{β} = 
  ∀ {A : Set α}(x : A)(P : (y : A) → (p : x ≡ y) → Set β)
  → P x refl
  → ∀ y (p : x ≡ y) → P y p

J'→J : (∀ {α β} → JT' {α}{β}) → (∀ {α β} → JT {α}{β})
J'→J j' {A} P refl* x y p = j' {A} x (λ y p → P x y p) (refl* x) y p


IsContr : ∀ {α} → Set α → Set α
IsContr A = ∃ λ (a : A) → ∀ a' → a' ≡ a

Sing : ∀ {α} → (A : Set α) → A → Set α
Sing A a = ∃ λ b → a ≡ b

singContr : ∀ {α A} a → IsContr (Sing {α} A a)
singContr a = (a , refl) , (λ {(_ , refl) → refl})

-- with universes
J→J' : (∀ {α β} → JT {α}{β}) → (∀ {α β} → JT' {α}{β})
J→J' j {α}{β}{A} x P refl* y p =
   j
    (λ x y (p : x ≡ y) → (P : ∀ y → x ≡ y → Set β) → (refl* : P x refl) → P y p)
    (λ _ _ refl* → refl*)
    x y p P refl*

-- without
J→J'₂ : JT {zero}{zero} → JT' {zero}{zero}
J→J'₂ j {A} x P refl* y p =
  let
    IsContr : Set → Set
    IsContr A = ∃ λ (a : A) → ∀ a' → a ≡ a'
    
    Sing : (A : Set) → A → Set
    Sing A a = ∃ λ b → a ≡ b

    subst :
      ∀ {A : Set} (P : A → Set) {x y : A} →
      x ≡ y → P x → P y
    subst P p px = j (λ x y p → P x → P y) (λ x px → px) _ _ p px
    
    singContr : ∀ (a : A) → IsContr (Sing A a)
    singContr a = (a , refl) , (λ pair → 
      j {A = A}
        (λ x y p → (x , refl) ≡ (Σ A (_≡_ x) ∋ (y , p)))
        (λ _ → refl)
        a (proj₁ pair) (proj₂ pair) )

  in subst (uncurry P) (proj₂ (singContr x) (y , p)) refl*



