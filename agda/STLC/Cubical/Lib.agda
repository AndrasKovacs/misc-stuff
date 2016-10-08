{-# OPTIONS --rewriting #-}

module STLC.Cubical.Lib where

open import Level

-- Σ
--------------------------------------------------------------------------------

record Σ {i j} (A : Set i) (B : A → Set j) : Set (i ⊔ j) where
  constructor _,_
  field
    proj₁ : A
    proj₂ : B proj₁

infixl 5 _,_
infix  4 _×_

open Σ public

_×_ : ∀{i j} → Set i → Set j → Set (i ⊔ j)
A × B = Σ A λ _ → B

-- Cubical (TODO : heterogeneous path?)
--------------------------------------------------------------------------------

infix  0 _↦_
infixl 9 _$_
infixl 4 _∘ᵀ_ 
infix 3 [_]_≡_
infix 4 _≡_

postulate _↦_ : ∀ {α} {A : Set α} → A → A → Set
{-# BUILTIN REWRITE _↦_ #-}

postulate
  I        : Set
  ₀ ₁      : I
  _[_-_]   : I → I → I → I

data [_]_≡_ {ℓ} (A : I → Set ℓ) : A ₀ → A ₁ → Set ℓ where
  path : (M : (i : I) → A i) → [ A ] M ₀ ≡ M ₁

_≡_ : ∀{α}{A : Set α} → A → A → Set α
_≡_{_}{A} a a' = [ (λ _ → A) ] a ≡ a'

_$_ : ∀ {ℓ} {A : I → Set ℓ} {a b} → [ A ] a ≡ b → ∀ i → A i
path M $ i = M i

postulate
  co   : ∀ {ℓ} {S T : Set ℓ} (Q : S ≡ T) (i j : I) → Q $ i → Q $ j
  _∘ᵀ_ : ∀ {ℓ} {S T U : Set ℓ} → S ≡ T → T ≡ U → S ≡ U

infixr 20 co
syntax co Q p q a = a [ p ∣ Q ∣ q ⟩

infix 2 path
syntax path (λ i → t) = ⟨ i ⟩ t

postulate
  [-]-left   : ∀ q r → ₀ [ q - r ] ↦ q
  [-]-right  : ∀ q r → ₁ [ q - r ] ↦ r
  $-₀        : ∀ ℓ (A : I → Set ℓ) a a' (p : [ A ] a ≡ a') → p $ ₀ ↦ a
  $-₁        : ∀ ℓ (A : I → Set ℓ) a a' (p : [ A ] a ≡ a') → p $ ₁ ↦ a'  
  co-0-0 : ∀ ℓ (A B : Set ℓ) (p : A ≡ B) a → a [ ₀ ∣ p ∣ ₀ ⟩ ↦ a
  co-1-1 : ∀ ℓ (A B : Set ℓ) (p : A ≡ B) a → a [ ₁ ∣ p ∣ ₁ ⟩ ↦ a

{-# REWRITE [-]-left   #-}
{-# REWRITE [-]-right  #-}
{-# REWRITE $-₀        #-}
{-# REWRITE $-₁        #-}
{-# REWRITE co-0-0 #-}
{-# REWRITE co-1-1 #-}

postulate
  [₀-₀]      : ∀ p → p [ ₀ - ₀ ] ↦ ₀
  [₀-₁]      : ∀ p → p [ ₀ - ₁ ] ↦ p
  [₁-₁]      : ∀ p → p [ ₁ - ₁ ] ↦ ₁
  path-η     : ∀ ℓ (A : I → Set ℓ) (a : A ₀)(a' : A ₁) (p : [ A ] a ≡ a') → ⟨ i ⟩ (p $ i) ↦ p

{-# REWRITE [₀-₀]  #-}
{-# REWRITE [₀-₁]  #-}
{-# REWRITE [₁-₁]  #-}
{-# REWRITE path-η #-}

postulate
  co-const : ∀ ℓ (A : Set ℓ) a p q → a [ p ∣ ⟨ _ ⟩ A ∣ q ⟩ ↦ a
{-# REWRITE co-const #-}

postulate
  co-∘ᵀ   :
    ∀ ℓ (S T U : Set ℓ) (Q : S ≡ T) (Q' : T ≡ U) (a : S)
    → a [ ₀ ∣ Q ∘ᵀ Q' ∣ ₁ ⟩ ↦ ((a [ ₀ ∣ Q ∣ ₁ ⟩) [ ₀ ∣ Q' ∣ ₁ ⟩)
    
  co-∘ᵀ′  :
    ∀ ℓ (S T U : Set ℓ) (Q : S ≡ T) (Q' : T ≡ U) a
    → a [ ₁ ∣ Q ∘ᵀ Q' ∣ ₀ ⟩ ↦ ((a [ ₁ ∣ Q' ∣ ₀ ⟩) [ ₁ ∣ Q ∣ ₀ ⟩)

  co-Σ   : ∀ ℓ (S : I → Set ℓ) (T : (i : I) → S i → Set ℓ) (s : S ₀) (t : T ₀ s)
             → (s , t) [ ₀ ∣ ⟨ i ⟩ Σ (S i) (T i) ∣ ₁ ⟩ ↦
               let s- : (j : I) → S j
                   s- j = s [ ₀ ∣ ⟨ i ⟩ S i ∣ j ⟩
               in  s- ₁ , t [ ₀ ∣ ⟨ i ⟩ T i (s- i) ∣ ₁ ⟩

  co-Σ′  : ∀ ℓ (S : I → Set ℓ) (T : (i : I) → S i → Set ℓ) (s : S ₁) (t : T ₁ s)
             → (s , t) [ ₁ ∣ ⟨ i ⟩ Σ (S i) (T i) ∣ ₀ ⟩ ↦
               let s- : (j : I) → S j
                   s- j = s [ ₁ ∣ ⟨ i ⟩ S i ∣ j ⟩
               in  s- ₀ , t [ ₁ ∣ ⟨ i ⟩ T i (s- i) ∣ ₀ ⟩

  co-Π   : ∀ ℓ (S : I → Set ℓ) (T : (i : I) → S i → Set ℓ) (t : (x : S ₀) → (T ₀ x))
             → (λ x → t x) [ ₀ ∣ ⟨ i ⟩ ((x : S i) → T i x) ∣ ₁ ⟩ ↦ λ x →
               let s- : (j : I) → S j
                   s- j = x [ ₁ ∣ ⟨ i ⟩ S i ∣ j ⟩
               in  t (s- ₀) [ ₀ ∣ ⟨ i ⟩ T i (s- i) ∣ ₁ ⟩

  co-Π′  : ∀ ℓ (S : I → Set ℓ) (T : (i : I) → S i → Set ℓ) (t : (x : S ₁) →  T ₁ x)
             → (λ x → t x) [ ₁ ∣ ⟨ i ⟩ ((x : S i) → T i x) ∣ ₀ ⟩ ↦ λ x →
               let s- : (j : I) → S j
                   s- j = x [ ₀ ∣ ⟨ i ⟩ S i ∣ j ⟩
               in  t (s- ₁) [ ₁ ∣ ⟨ i ⟩ T i (s- i) ∣ ₀ ⟩

  co-≡   : ∀ ℓ (S T : I → Set ℓ) (Q : S ₀ ≡ T ₀)
             → Q [ ₀ ∣ ⟨ i ⟩ S i ≡ T i ∣ ₁ ⟩ ↦ 
               (⟨ i ⟩ S (i [ ₁ - ₀ ])) ∘ᵀ Q ∘ᵀ (⟨ i ⟩ T i)

  co-≡′  : ∀ ℓ (S T : I → Set ℓ) (Q : S ₁ ≡ T ₁)
             → Q [ ₁ ∣ ⟨ i ⟩ S i ≡ T i ∣ ₀ ⟩ ↦
               (⟨ i ⟩ S i) ∘ᵀ Q ∘ᵀ (⟨ i ⟩ T (i [ ₁ - ₀ ]))

{-# REWRITE co-∘ᵀ  #-}
{-# REWRITE co-∘ᵀ′ #-}
{-# REWRITE co-Σ  #-}
{-# REWRITE co-Σ′ #-}
{-# REWRITE co-Π  #-}
{-# REWRITE co-Π′ #-}
{-# REWRITE co-≡  #-}
{-# REWRITE co-≡′ #-}

-- lib
--------------------------------------------------------------------------------

coe : ∀ {ℓ} {S T : Set ℓ} (Q : S ≡ T) → Q $ ₀ → Q $ ₁
coe Q x = x [ ₀ ∣ Q ∣ ₁ ⟩

_≡[_]≡_ : ∀{i}{A B : Set i} → A → A ≡ B → B → Set i
x ≡[ p ]≡ y = [ (λ i → p $ i) ] x ≡ y

infix 4 _≡[_]≡_

ap : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} (f : A → B)
       {x y : A} → x ≡ y → f x ≡ f y
ap f p = ⟨ i ⟩ f (p $ i)

apd : ∀ {ℓ ℓ'} {A : Set ℓ} {B : A → Set ℓ'} (f : (a : A) → B a)
       {a a' : A} → (p : a ≡ a') → f a ≡[ ap B p ]≡ f a'
apd {B = B} f p = ⟨ i ⟩ f (p $ i)

ap2 : ∀{i j k}{A : Set i}{B : Set j}{C : Set k}(f : A → B → C)
    → {a₀ a₁ : A}(a₂ : a₀ ≡ a₁){b₀ b₁ : B}(b₂ : b₀ ≡ b₁)
    → f a₀ b₀ ≡ f a₁ b₁
ap2 f p q = ⟨ i ⟩ f (p $ i) (q $ i)

neg : I → I
neg i = i [ ₁ - ₀ ]

_⁻¹ : ∀ {ℓ}{A : Set ℓ}{x y : A} → x ≡ y → y ≡ x
p ⁻¹ = ⟨ i ⟩ (p $ neg i)

refl : ∀ {α}{A : Set α}{a : A} → a ≡ a
refl {a = a} = ⟨ _ ⟩ a

funext :
  ∀{α β}{A : Set α}{B : A → Set β}{f g : (a : A) → B a}
  → ((a : A) → f a  ≡ g a) → f ≡ g
funext p = ⟨ i ⟩ λ a → p a $ i

infix 5 _⁻¹

_◾_ : ∀{i}{A : Set i}{x y z : A} → x ≡ y → y ≡ z → x ≡ z
_◾_ {x = x} p q = coe (⟨ i ⟩ x ≡ q $ i) p

infixl 4 _◾_

_≡⟨_⟩_ : ∀{i}{A : Set i}(x : A){y z : A} → x ≡ y → y ≡ z → x ≡ z
x ≡⟨ x≡y ⟩ y≡z = x≡y ◾ y≡z

infixr 2 _≡⟨_⟩_

_∎ : ∀{i}{A : Set i}(x : A) → x ≡ x
x ∎ = refl

infix  3 _∎

J : ∀ {ℓ ℓ′} {A : Set ℓ} {x : A} (P : (y : A) → x ≡ y → Set ℓ′)
  → P x refl → {y : A} (e : x ≡ y) → P y e
J P refl* e = coe (⟨ i ⟩ (P (e $ i) (⟨ j ⟩ e $ i [ ₀ - j ]))) refl*

--------------------------------------------------------------------------------

record ⊤ : Set where
  constructor tt

data ⊥ : Set where

⊥-elim : ∀{i}{A : Set i} → ⊥ → A
⊥-elim ()

