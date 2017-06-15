{-# OPTIONS --without-K #-}

module Lib where

open import Level public renaming (suc to lsuc; zero to lzero)
open import Relation.Binary.PropositionalEquality public using (_≡_; refl)
open import Function public
open import Data.Product public
open import Data.Bool public
open import Data.Nat public hiding (_≟_; _⊔_)

_◾_ : ∀{i}{A : Set i}{x y z : A} → x ≡ y → y ≡ z → x ≡ z
refl ◾ q = q
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

J : ∀{α β}{A : Set α} {x : A} (P : ∀ {y} → x ≡ y → Set β) → P refl → ∀ {y} p → P {y} p
J P pr refl = pr

postulate
  ext  : ∀{i j}{A : Set i}{B : A → Set j}{f g : (x : A) → B x}
          → ((x : A) → f x  ≡ g x) → _≡_ f g
          
  exti : ∀{i j}{A : Set i}{B : A → Set j}{f g : {x : A} → B x}
          → ((x : A) → f {x} ≡ g {x}) → _≡_ {A = {x : A} → B x} f g

