{-# OPTIONS --type-in-type --rewriting #-}

-- toy cubical type theory with rewrite rules
-- which demonstrates computational funext

postulate _↦_ : {A : Set} → A → A → Set
{-# BUILTIN REWRITE _↦_ #-}
infix 3 _↦_

postulate
  I   : Set
  ₀ ₁ : I
  _∧_ : I → I → I
  ₀∧  : ∀ i → ₀ ∧ i ↦ ₀
  ∧₀  : ∀ i → i ∧ ₀ ↦ ₀
  ₁∧  : ∀ i → ₁ ∧ i ↦ i
  ∧₁  : ∀ i → i ∧ ₁ ↦ i
{-# REWRITE  ₀∧ ∧₀ ₁∧ ∧₁ #-}

infixl 4 _∧_

module _ {A : Set} where
  postulate
    _≡_   : A → A → Set
    path  : (f : I → A) → f ₀ ≡ f ₁
    _$_   : ∀ {x y} → x ≡ y → I → A
    $-₀   : ∀ {x y}(p : x ≡ y) → p $ ₀ ↦ x
    $-₁   : ∀ {x y}(p : x ≡ y) → p $ ₁ ↦ y
    pathβ : ∀ p i → path p $ i ↦ p i
  {-# REWRITE $-₀ $-₁ pathβ #-}

  postulate
    pathη : ∀ {x y}{p : x ≡ y} → path (λ i → p $ i) ↦ p
  {-# REWRITE pathη #-}

  infixl 8 _$_
  infix 3 _≡_
  syntax path (λ i → t) = ⟨ i ⟩ t

postulate
  coe        : {A B : Set} → A ≡ B → A → B
  regularity : (A : Set) → coe (⟨ _ ⟩ A) ↦ (λ a → a)
{-# REWRITE regularity #-}

refl : ∀ {A}{a : A} → a ≡ a
refl {_}{a} = ⟨ _ ⟩ a

--------------------------------------------------------------------------------

ap : ∀ {A B}(f : A → B){x y : A} → x ≡ y → f x ≡ f y
ap f p = ⟨ i ⟩ f (p $ i)

infixr 4 _◾_
_◾_ : ∀ {A}{a b c : A} → a ≡ b → b ≡ c → a ≡ c
_◾_ {a = a} {b} {c} p q = coe (ap (a ≡_) q) p

tr : ∀ {A}(P : A → Set){a b : A} → a ≡ b → P a → P b
tr P p = coe (ap P p)

ext : ∀ {A}{B : A → Set}{f g : ∀ a → B a} → (∀ a → f a ≡ g a) → f ≡ g
ext p = ⟨ i ⟩ (λ a → p a $ i)

J : ∀ {A}{a : A}(P : ∀ a' → a ≡ a' → Set) → P a refl → ∀ {a'} (p : a ≡ a') → P a' p
J P refl* p = coe (⟨ i ⟩ P (p $ i) (⟨ j ⟩ (p $ (i ∧ j)))) refl*

J-refl :
  ∀ {A}{a : A}(P : ∀ a' → a ≡ a' → Set) refl* → J P refl* refl ≡ refl*
J-refl {A}{a} P refl* = refl

infix 5 _⁻¹
_⁻¹ : ∀ {A}{x y : A} → x ≡ y → y ≡ x
_⁻¹ {A}{x}{y} p = tr (_≡ x) p refl

--------------------------------------------------------------------------------

open import Data.Nat

f : ℕ → ℕ
f = (_+ 0)

g : ℕ → ℕ
g x = x

p' : ∀ x → f x ≡ g x
p' zero    = refl
p' (suc x) = ap suc (p' x)

p : f ≡ g
p = ext p'

q : 10 ≡ 10
q = ap (λ f → f 10) p

works : q ≡ refl
works = refl
