{-# OPTIONS --without-K --rewriting #-}

module Lib where

open import Level public
open import Relation.Binary.PropositionalEquality public using (_≡_; refl)
open import Data.Empty public

{-# BUILTIN REWRITE _≡_ #-}
postulate cheat : ∀ {α}{A : Set α} → A

infix 3 _∋_
_∋_ : ∀ {α}(A : Set α) → A → A
A ∋ a = a

infixr 9 _∘_
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
refl ◾ p = p
infixr 4 _◾_

◾refl : ∀ {i}{A : Set i}{x y : A}(p : x ≡ y) → (p ◾ refl) ≡ p
◾refl refl = refl
{-# REWRITE ◾refl #-}

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

id& : ∀{i}{A : Set i}{a₀ a₁ : A}(p : a₀ ≡ a₁) → id & p ≡ p
id& refl = refl
{-# REWRITE id& #-}

const& :
  ∀ {i j}{A : Set i}{B : Set j}{a₀ a₁ : A}(p : a₀ ≡ a₁){b : B}
  → (λ _ → b) & p ≡ refl
const& refl = refl
{-# REWRITE const& #-}

coe∘ : ∀ {i}{A B C : Set i}(p : B ≡ C)(q : A ≡ B)(a : A)
       → coe p (coe q a) ≡ coe (q ◾ p) a
coe∘ refl refl _ = refl

coecoe⁻¹ : ∀ {i}{A B : Set i}(p : A ≡ B) x → coe p (coe (p ⁻¹) x) ≡ x
coecoe⁻¹ refl x = refl

coecoe⁻¹' : ∀ {i}{A B : Set i}(p : A ≡ B) x → coe (p ⁻¹) (coe p x) ≡ x
coecoe⁻¹' refl x = refl

tr : ∀ {i j}{A : Set i}(B : A → Set j){a₀ : A}{a₁ : A}(a₂ : a₀ ≡ a₁) → B a₀ → B a₁
tr B p = coe (B & p)

tr2 :
  ∀ {i j k}{A : Set i}{B : A → Set j}(C : ∀ a → B a → Set k)
    {a₀ : A}{a₁ : A}(a₂ : a₀ ≡ a₁)
    {b₀ : B a₀}{b₁ : B a₁}(b₂ : tr B a₂ b₀ ≡ b₁)
  → C a₀ b₀ → C a₁ b₁
tr2 {B = B} C {a₀}{.a₀} refl refl c₀ = c₀

happly : ∀ {α β}{A : Set α}{B : Set β}{f g : A → B} → f ≡ g → ∀ a → f a ≡ g a
happly refl a = refl

&⁻¹ : ∀{i j}{A : Set i}{B : Set j}(f : A → B){a₀ a₁ : A}(a₂ : a₀ ≡ a₁)
      → f & a₂ ⁻¹ ≡ f & (a₂ ⁻¹)
&⁻¹ f refl = refl

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

J⁻¹ :
  ∀ {α β}{A : Set α} {x : A}(P : ∀ y → x ≡ y → Set β)
  → {y : A} → (w : x ≡ y) → P y w → P x refl
J⁻¹ P refl p = p

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

,≡ : ∀{i j}{A : Set i}{B : A → Set j}{a a' : A}{b : B a}{b' : B a'}
     (p : a ≡ a') → coe (B & p) b ≡ b' → (Σ A B ∋ (a , b)) ≡ (a' , b')
,≡ refl refl = refl

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
  constructor mkReveal
  field eq : f x ≡ y

inspect : ∀ {a b} {A : Set a} {B : A → Set b}
          (f : (x : A) → B x) (x : A) → Reveal f · x is f x
inspect f x = mkReveal refl

Π≡ :
  ∀ {α β}{A A' : Set α}{B : A → Set β}{B' : A' → Set β}
  → (p : A ≡ A') → ((a : A) → B a ≡ B' (coe p a))
  → ((a : A) → B a) ≡ ((a' : A') → B' a')
Π≡ {A = A} {B = B} {B'} refl q = (λ B → (x : A) → B x) & ext q

Π≡i :
  ∀ {α β}{A A' : Set α}{B : A → Set β}{B' : A' → Set β}
  → (p : A ≡ A') → ((a : A) → B a ≡ B' (coe p a))
  → ({a : A} → B a) ≡ ({a' : A'} → B' a')
Π≡i {A = A}{B = B} refl q = (λ B → {x : A} → B x) & ext q
