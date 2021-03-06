{-# OPTIONS --without-K #-}

module Lib where

open import Level
open import Relation.Binary.PropositionalEquality public
open import Data.Empty public
open import Data.Product public
open import Data.Nat public hiding (_⊔_)
open import Data.Fin public using (Fin; zero; suc)

infix 3 _∋_
_∋_ : ∀ {α}(A : Set α) → A → A
A ∋ a = a

_∘_ : ∀ {a b c}
        {A : Set a} {B : A → Set b} {C : {x : A} → B x → Set c} →
        (∀ {x} (y : B x) → C y) → (g : (x : A) → B x) →
        ((x : A) → C (g x))
f ∘ g = λ x → f (g x)

id : ∀ {a} {A : Set a} → A → A
id x = x

const : ∀ {a b} {A : Set a} {B : Set b} → A → B → A
const x = λ _ → x

infix 0 case_return_of_ case_of_

case_return_of_ :
  ∀ {a b} {A : Set a}
  (x : A) (B : A → Set b) → ((x : A) → B x) → B x
case x return B of f = f x

case_of_ : ∀ {a b} {A : Set a} {B : Set b} → A → (A → B) → B
case x of f = case x return _ of f

_◾_ : ∀{i}{A : Set i}{x y z : A} → x ≡ y → y ≡ z → x ≡ z
refl ◾ refl = refl
infixr 4 _◾_

_⁻¹ : ∀{i}{A : Set i}{x y : A} → x ≡ y → y ≡ x
refl ⁻¹ = refl
infix 6 _⁻¹

_≡⟨_⟩_ : ∀{i}{A : Set i}(x : A){y z : A} → x ≡ y → y ≡ z → x ≡ z
x ≡⟨ x≡y ⟩ y≡z = x≡y ◾ y≡z
infixr 2 _≡⟨_⟩_

_∎ : ∀{i}{A : Set i}(x : A) → x ≡ x
x ∎ = refl
infix  3 _∎

coe : ∀{i}{A B : Set i} → A ≡ B → A → B
coe refl a = a

_&_ :
  ∀{i j}{A : Set i}{B : Set j}(f : A → B){a₀ a₁ : A}(a₂ : a₀ ≡ a₁)
  → f a₀ ≡ f a₁
f & refl = refl
infixl 9 _&_

_⊗_ :
  ∀ {α β}{A : Set α}{B : Set β}
    {f g : A → B}(p : f ≡ g){a a' : A}(q : a ≡ a')
  → f a ≡ g a'
refl ⊗ refl = refl
infixl 8 _⊗_

apd : ∀{i j}{A : Set i}{B : A → Set j}(f : (x : A) → B x){a₀ a₁ : A}(a₂ : a₀ ≡ a₁)
    → coe (B & a₂) (f a₀) ≡ f a₁
apd f refl = refl

J : {A : Set} {x : A} (P : {y : A} → x ≡ y → Set) → P refl → {y : A} → (w : x ≡ y) → P w
J P pr refl = pr

record ⊤ : Set where
  constructor tt

data _⊎_ (A B : Set) : Set where
  inl : A → A ⊎ B
  inr : B → A ⊎ B
infixr 1 _⊎_

either : {A B C : Set} → (A → C) → (B → C) → A ⊎ B → C
either f g (inl x) = f x
either f g (inr x) = g x

ind⊎ : {A B : Set}(P : A ⊎ B → Set) → ((a : A) → P (inl a)) → ((b : B) → P (inr b))
     → (w : A ⊎ B) → P w
ind⊎ P ca cb (inl a) = ca a
ind⊎ P ca cb (inr b) = cb b

postulate
  ext  : ∀{i j}{A : Set i}{B : A → Set j}{f g : (x : A) → B x}
          → ((x : A) → f x  ≡ g x) → _≡_ f g

  exti : ∀{i j}{A : Set i}{B : A → Set j}{f g : {x : A} → B x}
          → ((x : A) → f {x} ≡ g {x}) → _≡_ {A = {x : A} → B x} f g

Π-≡ :
  ∀ {α β}{A A' : Set α}{B : A → Set β}{B' : A' → Set β}
  → (p : A ≡ A') → ((a : A) → B a ≡ B' (coe p a))
  → ((a : A) → B a) ≡ ((a' : A') → B' a')
Π-≡ {A = A} {B = B} {B'} refl q = (λ B → (x : A) → B x) & ext q

Π-≡-i :
  ∀ {α β}{A A' : Set α}{B : A → Set β}{B' : A' → Set β}
  → (p : A ≡ A') → ((a : A) → B a ≡ B' (coe p a))
  → ({a : A} → B a) ≡ ({a' : A'} → B' a')
Π-≡-i {A = A}{B = B} refl q = (λ B → {x : A} → B x) & ext q

coe-$ :
 ∀ {α β γ}{A : Set α}{B : Set β}(C : A → B → Set γ)
   {b b' : B}(p : b ≡ b')(f : ∀ a → C a b)
 →  coe ((λ x → ∀ a → C a x) & p) f ≡ (λ a → coe (C a & p) (f a))
coe-$ C refl f = refl

coe-$-i :
 ∀ {α β γ}{A : Set α}{B : Set β}(C : A → B → Set γ)
   {b b' : B}(p : b ≡ b')(f : ∀ {a} → C a b)
 →  (λ {a} → coe ((λ x → ∀ {a} → C a x) & p) f {a}) ≡ (λ {a} → coe (C a & p) (f {a}))
coe-$-i C refl f = refl
