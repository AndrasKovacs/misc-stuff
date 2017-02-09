
{-# OPTIONS --type-in-type --rewriting #-}

postulate _↦_ : {A : Set} → A → A → Set
{-# BUILTIN REWRITE _↦_ #-}
infix 3 _↦_

postulate
  I : Set
  ₀ ₁ : I
  _[_-_] : I → I → I → I

infix 3 [_]_≡_
data [_]_≡_ (A : I → Set) : A ₀ → A ₁ → Set where
  path : (f : ∀ i → A i) → [ A ] f ₀ ≡ f ₁

syntax path (λ i → t) = ⟨ i ⟩ t

infix 3 _≡_
_≡_ = λ {A : Set} (x y : A) → [ (λ _ → A) ] x ≡ y

_$_ : ∀ {A}{x y} → [ A ] x ≡ y → ∀ i → A i
path f $ i = f i
infixl 8 _$_

{-# DISPLAY path f = f #-}

refl : ∀ {A}{a : A} → a ≡ a
refl {_}{a} = ⟨ _ ⟩ a

postulate
  $-₀ : ∀ {A}{x y}(p : [ A ] x ≡ y) → p $ ₀ ↦ x
  $-₁ : ∀ {A}{x y}(p : [ A ] x ≡ y) → p $ ₁ ↦ y
{-# REWRITE $-₀ #-}
{-# REWRITE $-₁ #-}

postulate
  [₀-₀]      : ∀ p   → p [ ₀ - ₀ ] ↦ ₀
  [₀-₁]      : ∀ p   → p [ ₀ - ₁ ] ↦ p
  [₁-₁]      : ∀ p   → p [ ₁ - ₁ ] ↦ ₁
  [-]-left   : ∀ q r → ₀ [ q - r ] ↦ q
  [-]-right  : ∀ q r → ₁ [ q - r ] ↦ r
  path-η     : ∀ A x y (Q : [ A ] x ≡ y) → ⟨ i ⟩ (Q $ i) ↦ Q
{-#  REWRITE [₀-₀]     #-}
{-#  REWRITE [₀-₁]     #-}
{-#  REWRITE [₁-₁]     #-}
{-#  REWRITE [-]-left  #-}
{-#  REWRITE [-]-right #-}
{-#  REWRITE path-η    #-}

record Σ (A : Set) (B : A → Set) : Set where
  constructor _,_
  field
    proj₁ : A
    proj₂ : B proj₁
open Σ

open import Data.Nat

infixr 5 _∙_
postulate
  _∙_        : ∀ {A x y z} → [ A ] x ≡ y → y ≡ z → [ A ] x ≡ z
  coe        : {A B : Set} → A ≡ B → A → B
  regularity : (A : Set) → coe (⟨ _ ⟩ A) ↦ (λ a → a)
{-# REWRITE regularity #-}

postulate
  coe-Π :
    (A : I → Set)(B : (i : I) → A i → Set)(f : (a : A ₀) → B ₀ a)
    → coe (⟨ i ⟩ ((a : A i) → B i a)) f
      ↦
      (λ a₁ → coe (⟨ i ⟩ B i (coe (⟨ j ⟩ A (j [ ₁ - i ])) a₁ )) (f (coe (⟨ i ⟩ A (i [ ₁ - ₀ ])) a₁)))

  coe-Σ :
    (A : I → Set)(B : ∀ i → A i → Set)(p : Σ (A ₀) (B ₀))
    → coe (⟨ i ⟩ (Σ (A i) (B i))) p
    ↦ ((coe (⟨ i ⟩ A i) (proj₁ p)) , coe (⟨ i ⟩ B i (coe (⟨ j ⟩ A (j [ ₀ - i ])) (proj₁ p))) (proj₂ p))

  coe-≡ :
      (A : I → Set)(x y : ∀ i → A i)(p : x ₀ ≡ y ₀)
    → coe (⟨ i ⟩ (_≡_ {A i} (x i) (y i))) p ↦ {!!} ∙ {!!} ∙ {!!}

-- --   coe-∙  : (A B C : Set)(p : A ≡ B)(q : B ≡ C) → coe (p ∙ q) ↦ (λ a → coe q (coe p a))
-- --   refl-∙ : (A : Set)(x y : A)(p : x ≡ y) → refl ∙ p ↦ p
-- --   ∙-refl : (A : Set)(x y : A)(p : x ≡ y) → p ∙ refl ↦ p

-- --   coe-suc  : (n : ℕ)(p : ℕ ≡ ℕ) → coe p (suc n) ↦ suc (coe p n)
-- --   coe-zero : (p : ℕ ≡ ℕ) → coe p zero ↦ zero

-- -- {-# REWRITE coe-Π #-}
-- -- {-# REWRITE coe-Σ #-}
-- -- {-# REWRITE coe-zero #-}
-- -- {-# REWRITE coe-suc #-}
-- -- {-# REWRITE coe-∙ #-}
-- -- {-# REWRITE refl-∙ #-}
-- -- {-# REWRITE ∙-refl #-}
-- -- {-# REWRITE coe-≡ #-}

-- -- infix 5 _⁻¹
-- -- _⁻¹ : ∀ {A}{x y : A} → x ≡ y → y ≡ x
-- -- _⁻¹ p = ⟨ i ⟩ (p $ (i [ ₁ - ₀ ]))

-- -- infixl 6 _&_
-- -- _&_ : ∀ {A B}(f : A → B){x y : A} → x ≡ y → f x ≡ f y
-- -- _&_ f p = ⟨ i ⟩ f (p $ i)

-- -- infixr 4 _◾_
-- -- _◾_ : ∀ {A}{a b c : A} → a ≡ b → b ≡ c → a ≡ c
-- -- _◾_ {a = a} {b} {c} p q = coe ((a ≡_) & q) p

-- -- transp : ∀ {A}(P : A → Set){a b : A} → a ≡ b → P a → P b
-- -- transp P p = coe (P & p)

-- -- ext : ∀ {A}{B : A → Set}{f g : ∀ a → B a} → (∀ a → f a ≡ g a) → f ≡ g
-- -- ext {f = f} {g} p = ⟨ i ⟩ (λ a → p a $ i)

-- -- J : ∀ {A}{a : A}(P : ∀ a' → a ≡ a' → Set) → P a refl → ∀ {a'} (p : a ≡ a') → P a' p
-- -- J P refl* p = coe (⟨ i ⟩ P (p $ i) (⟨ j ⟩ (p $ i [ ₀ - j ]))) refl*

-- -- J-refl :
-- --   ∀ {A}{a : A}(P : ∀ a' → a ≡ a' → Set) refl* → J P refl* refl ≡ refl*
-- -- J-refl P refl* = ⟨ _ ⟩ refl*  
