{-# OPTIONS --without-K #-}

module Lib where

open import Level
open import Relation.Binary.PropositionalEquality public using (_≡_; refl)
open import Data.Empty public

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

tr : ∀ {i j}{A : Set i}(B : A → Set j){a₀ : A}{a₁ : A}(a₂ : a₀ ≡ a₁) → B a₀ → B a₁
tr B refl b₀ = b₀

infix 0 case_return_of_ case_of_

case_return_of_ :
  ∀ {a b} {A : Set a}
  (x : A) (B : A → Set b) → ((x : A) → B x) → B x
case x return B of f = f x

case_of_ : ∀ {a b} {A : Set a} {B : Set b} → A → (A → B) → B
case x of f = case x return _ of f

_◾_ : ∀{i}{A : Set i}{x y z : A} → x ≡ y → y ≡ z → x ≡ z
refl ◾ p = p
infixr 4 _◾_

_⁻¹ : ∀{i}{A : Set i}{x y : A} → x ≡ y → y ≡ x
refl ⁻¹ = refl
infix 6 _⁻¹

coe : ∀{i}{A B : Set i} → A ≡ B → A → B
coe refl a = a

happly : ∀ {α β}{A : Set α}{B : Set β}{f g : A → B} → f ≡ g → ∀ a → f a ≡ g a
happly refl a = refl

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

J :
  ∀ {α β}{A : Set α} {x : A}(P : ∀ y → x ≡ y → Set β)
  → P x refl → {y : A} → (w : x ≡ y) → P y w
J P pr refl = pr

record Σ {i j} (A : Set i) (B : A → Set j) : Set (i ⊔ j) where
  constructor _,_
  field
    ₁ : A
    ₂ : B ₁
infixr 5 _,_

∃ : ∀ {a b} {A : Set a} → (A → Set b) → Set (a ⊔ b)
∃ = Σ _

∃₂ : ∀ {a b c} {A : Set a} {B : A → Set b}
     (C : (x : A) → B x → Set c) → Set (a ⊔ b ⊔ c)
∃₂ C = ∃ λ a → ∃ λ b → C a b

,_ : ∀ {a b} {A : Set a} {B : A → Set b} {x} → B x → ∃ B
, y = _ , y

open Σ public

_×_ : ∀{i j} → Set i → Set j → Set (i ⊔ j)
A × B = Σ A λ _ → B
infixr 4 _×_

,Σ≡ : ∀{i j}{A : Set i}{B : A → Set j}{a a' : A}{b : B a}{b' : B a'}
     (p : a ≡ a') → coe (B & p) b ≡ b' → (Σ A B ∋ (a , b)) ≡ (a' , b')
,Σ≡ refl refl = refl

curry : ∀ {a b c} {A : Set a} {B : A → Set b} {C : Σ A B → Set c} →
        ((p : Σ A B) → C p) →
        ((x : A) → (y : B x) → C (x , y))
curry f x y = f (x , y)

uncurry : ∀ {a b c} {A : Set a} {B : A → Set b} {C : Σ A B → Set c} →
          ((x : A) → (y : B x) → C (x , y)) →
          ((p : Σ A B) → C p)
uncurry f (x , y) = f x y

record ⊤ : Set where
  constructor tt

data _⊎_ {i j}(A : Set i)(B : Set j) : Set (i ⊔ j) where
  inl : A → A ⊎ B
  inr : B → A ⊎ B
infixr 1 _⊎_

either : ∀{i j k}{A : Set i}{B : Set j}{C : Set k} → (A → C) → (B → C) → A ⊎ B → C
either f g (inl x) = f x
either f g (inr x) = g x

ind⊎ : ∀{i j k}{A : Set i}{B : Set j}(P : A ⊎ B → Set k)
       → ((a : A) → P (inl a)) → ((b : B) → P (inr b))
     → (w : A ⊎ B) → P w
ind⊎ P ca cb (inl a) = ca a
ind⊎ P ca cb (inr b) = cb b

postulate
  ext  : ∀{i j}{A : Set i}{B : A → Set j}{f g : (x : A) → B x}
          → ((x : A) → f x  ≡ g x) → _≡_ f g

  exti : ∀{i j}{A : Set i}{B : A → Set j}{f g : {x : A} → B x}
          → ((x : A) → f {x} ≡ g {x}) → _≡_ {A = {x : A} → B x} f g

record Reveal_·_is_ {a b} {A : Set a} {B : A → Set b}
                    (f : (x : A) → B x) (x : A) (y : B x) :
                    Set (a ⊔ b) where
  constructor con
  field eq : f x ≡ y

inspect : ∀ {a b} {A : Set a} {B : A → Set b}
          (f : (x : A) → B x) (x : A) → Reveal f · x is f x
inspect f x = con refl

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
