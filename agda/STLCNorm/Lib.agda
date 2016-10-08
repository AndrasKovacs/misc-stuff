{-# OPTIONS --without-K #-}

module Lib where

open import Level

_∋_ : ∀ {a} (A : Set a) → A → A
A ∋ x = x

infixl 0 _∋_

idfun : ∀{i}{A : Set i} → A → A
idfun x = x

data _≡_ {i}{A : Set i} (x : A) : A → Set i where
  refl : x ≡ x
infix 4 _≡_

{-# BUILTIN EQUALITY _≡_ #-}
{-# BUILTIN REFL refl #-}

_◾_ : ∀{i}{A : Set i}{x y z : A} → x ≡ y → y ≡ z → x ≡ z
refl ◾ refl = refl

infixl 4 _◾_

_⁻¹ : ∀{i}{A : Set i}{x y : A} → x ≡ y → y ≡ x
refl ⁻¹ = refl

infix 5 _⁻¹

_≡⟨_⟩_ : ∀{i}{A : Set i}(x : A){y z : A} → x ≡ y → y ≡ z → x ≡ z
x ≡⟨ x≡y ⟩ y≡z = x≡y ◾ y≡z

infixr 2 _≡⟨_⟩_

_∎ : ∀{i}{A : Set i}(x : A) → x ≡ x
x ∎ = refl

infix  3 _∎

coe : ∀{i}{A B : Set i} → A ≡ B → A → B
coe refl a = a

_≡[_]≡_ : ∀{i}{A B : Set i} → A → A ≡ B → B → Set i
x ≡[ α ]≡ y = coe α x ≡ y

infix 4 _≡[_]≡_

coh : ∀{i}{A B : Set i}(p : A ≡ B) → (a : A) → a ≡[ p ]≡ coe p a
coh p a = refl

ap : ∀{i j}{A : Set i}{B : Set j}(f : A → B){a₀ a₁ : A}(a₂ : a₀ ≡ a₁)
    → f a₀ ≡ f a₁
ap f refl = refl

apd : ∀{i j}{A : Set i}{B : A → Set j}(f : (x : A) → B x){a₀ a₁ : A}(a₂ : a₀ ≡ a₁)
    → f a₀ ≡[ ap B a₂ ]≡ f a₁
apd f refl = refl

J : {A : Set} {x : A} (P : {y : A} → x ≡ y → Set) → P refl → {y : A} → (w : x ≡ y) → P w
J P pr refl = pr

ap2 : ∀{i j k}{A : Set i}{B : Set j}{C : Set k}(f : A → B → C)
    → {a₀ a₁ : A}(a₂ : a₀ ≡ a₁){b₀ b₁ : B}(b₂ : b₀ ≡ b₁)
    → f a₀ b₀ ≡ f a₁ b₁
ap2 f refl refl = refl

record Σ {i j} (A : Set i) (B : A → Set j) : Set (i ⊔ j) where
  constructor _,_
  field
    proj₁ : A
    proj₂ : B proj₁

infixl 5 _,_

open Σ public

_×_ : ∀{i j} → Set i → Set j → Set (i ⊔ j)
A × B = Σ A λ _ → B

infix 4 _×_

record ⊤ : Set where
  constructor tt

data ⊥ : Set where

⊥-elim : ∀{i}{A : Set i} → ⊥ → A
⊥-elim ()

data _⊎_ (A B : Set) : Set where
  inl : A → A ⊎ B
  inr : B → A ⊎ B
infixr 1 _⊎_

ind⊎ : {A B : Set}(P : A ⊎ B → Set) → ((a : A) → P (inl a)) → ((b : B) → P (inr b))
     → (w : A ⊎ B) → P w
ind⊎ P ca cb (inl a) = ca a
ind⊎ P ca cb (inr b) = cb b

postulate
  funext  : ∀{i j}{A : Set i}{B : A → Set j}{f g : (x : A) → B x}
          → ((x : A) → f x  ≡ g x) → _≡_ f g

  funexti : ∀{i j}{A : Set i}{B : A → Set j}{f g : {x : A} → B x}
          → ((x : A) → f {x} ≡ g {x}) → _≡_ {A = {x : A} → B x} f g

