{-# OPTIONS --without-K #-}

module Lib where
open import Level

--------------------------------------------------------------------------------

infix 3 _∋_
_∋_ : ∀ {α}(A : Set α) → A → A
A ∋ a = a

_∘_ : ∀ {a b c}
        {A : Set a} {B : A → Set b} {C : {x : A} → B x → Set c} →
        (∀ {x} (y : B x) → C y) → (g : (x : A) → B x) →
        ((x : A) → C (g x))
f ∘ g = λ x → f (g x)

--------------------------------------------------------------------------------

data _≡_ {i}{A : Set i} (x : A) : A → Set i where
  refl : x ≡ x
infix 4 _≡_

{-# BUILTIN EQUALITY _≡_ #-}
{-# BUILTIN REFL refl #-}

_◾_ : ∀{i}{A : Set i}{x y z : A} → x ≡ y → y ≡ z → x ≡ z
refl ◾ refl = refl
infixr 4 _◾_

_⁻¹ : ∀{i}{A : Set i}{x y : A} → x ≡ y → y ≡ x
refl ⁻¹ = refl
infix 6 _⁻¹

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

apd2' :
  ∀ {i j k}{A : Set i}{B : A → Set j}{C : Set k}
  (f : ∀ a → B a → C){a₀ a₁ : A}(a₂ : a₀ ≡ a₁){b₀ : B a₀}{b₁ : B a₁}
  (b₂ : coe (B & a₂) b₀ ≡ b₁) → f a₀ b₀ ≡ f a₁ b₁
apd2' f refl refl = refl

apd2 :
  ∀ {i j k}{A : Set i}{B : A → Set j}{C : ∀ a → B a → Set k}
    (f : ∀ a → (b : B a) → C a b){a₀ a₁ : A}(a₂ : a₀ ≡ a₁){b₀ : B a₀}{b₁ : B a₁}
    (b₂ : coe (B & a₂) b₀ ≡ b₁) → coe (apd2' C a₂ b₂) (f a₀ b₀) ≡ f a₁ b₁
apd2 f refl refl = refl

--------------------------------------------------------------------------------

record Σ {i j} (A : Set i) (B : A → Set j) : Set (i ⊔ j) where
  constructor _,_
  field
    proj₁ : A
    proj₂ : B proj₁
infixr 5 _,_

∃ : ∀ {a b} {A : Set a} → (A → Set b) → Set (a ⊔ b)
∃ = Σ _

∃₂ : ∀ {a b c} {A : Set a} {B : A → Set b}
     (C : (x : A) → B x → Set c) → Set (a ⊔ b ⊔ c)
∃₂ C = ∃ λ a → ∃ λ b → C a b

open Σ public

_×_ : ∀{i j} → Set i → Set j → Set (i ⊔ j)
A × B = Σ A λ _ → B
infixr 4 _×_

,Σ≡ : ∀{i j}{A : Set i}{B : A → Set j}{a a' : A}{b : B a}{b' : B a'}
     (p : a ≡ a') → coe (B & p) b ≡ b' → (Σ A B ∋ (a , b)) ≡ (a' , b')
,Σ≡ refl refl = refl

--------------------------------------------------------------------------------

record ⊤ : Set where
  constructor tt

data ⊥ : Set where

⊥-elim : ∀{i}{A : Set i} → ⊥ → A
⊥-elim ()

data _⊎_ (A B : Set) : Set where
  inl : A → A ⊎ B
  inr : B → A ⊎ B
infixr 1 _⊎_

--------------------------------------------------------------------------------

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

