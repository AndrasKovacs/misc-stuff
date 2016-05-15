module library where

data Zero : Set where

exfalso : {C : Set} → Zero → C
exfalso ()

record One : Set where
* = record {}

data Two : Set where
  tt ff : Two

not : Two → Two
not tt = ff
not ff = tt

and : Two → Two → Two
and tt tt = tt
and _ _ = ff

or : Two → Two → Two
or ff ff = ff
or _ _ = tt

record Σ (A : Set) (B : A → Set) : Set where
  constructor _,_
  field
    proj₀ : A
    proj₁ : B proj₀
open Σ
infixl 7 _,_

data _+_ (A B : Set) : Set where
  inl : A → A + B
  inr : B → A + B
infix 2 _+_

case : {A B : Set} {C : A + B → Set} → ((a : A) → C (inl a)) → ((b : B) → C (inr b)) → (x : A + B) → C x
case cl cr (inl a) = cl a
case cl cr (inr b) = cr b

_×_ : Set → Set → Set
A × B = Σ A (λ _ → B)
infixl 3 _×_

¬_ : Set → Set
¬ A = A → Zero
infix 5 ¬_

_∨_ : Set → Set → Set
A ∨ B = ¬ (¬ A × ¬ B)

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

data _≡_ {A : Set} (a : A) : A → Set where
  refl : a ≡ a
infix 3 _≡_

_⊢_≡_ : {A : Set}{B : A → Set}{a a' : A} → a ≡ a' → B a → B a' → Set
refl ⊢ a ≡ a' = a ≡ a'

ap : {A B : Set}{x y : A}(f : A → B) → x ≡ y → f x ≡ f y
ap f refl = refl

transport : {A : Set} (P : A → Set) {x y : A} → x ≡ y → P x → P y
transport P refl u = u

ap2 : {A B C : Set} {a a' : A} {b b' : B} (f : A → B → C)
    → a ≡ a' → b ≡ b' → f a b ≡ f a' b'
ap2 f refl refl = refl

J : {A : Set} {P : {x y : A} → x ≡ y → Set} {a a' : A} → ((a : A) → P (refl {_} {a})) → {x y : A} (q : x ≡ y) → P q
J f {x} refl = f x

_⁻¹ : {A : Set} {x y : A} → x ≡ y → y ≡ x
refl ⁻¹ = refl

postulate
  funext : {A : Set} {B : A → Set} {f g : (a : A) → B a} → ((a : A) → f a ≡ g a) → f ≡ g
