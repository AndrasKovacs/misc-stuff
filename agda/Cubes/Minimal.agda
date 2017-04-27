
{-# OPTIONS --type-in-type --rewriting #-}

postulate _↦_ : {A : Set} → A → A → Set
{-# BUILTIN REWRITE _↦_ #-}
infix 3 _↦_

postulate
  I   : Set
  ₀ ₁ : I
  _∧_ : I → I → I 

infix 3 _≡_
data _≡_ {A : Set} : A → A → Set where
  path : (f : I → A) → f ₀ ≡ f ₁

syntax path (λ i → t) = ⟨ i ⟩ t

_$_ : ∀ {A}{x y : A} → x ≡ y → I → A
path f $ i = f i
infixl 8 _$_
{-# DISPLAY path f = f #-}

refl : ∀ {A}{a : A} → a ≡ a
refl {_}{a} = ⟨ _ ⟩ a

postulate
  $-₀ : ∀ {A}{x y : A}(p : x ≡ y) → p $ ₀ ↦ x
  $-₁ : ∀ {A}{x y : A}(p : x ≡ y) → p $ ₁ ↦ y
{-# REWRITE $-₀ #-}
{-# REWRITE $-₁ #-}

postulate
  ₀∧     : ∀ i → ₀ ∧ i ↦ ₀
  ∧₀     : ∀ i → i ∧ ₀ ↦ ₀
  ₁∧     : ∀ i → ₁ ∧ i ↦ i
  ∧₁     : ∀ i → i ∧ ₁ ↦ i
  path-η : ∀ (A : Set) (S T : A) (Q : S ≡ T) → ⟨ i ⟩ (Q $ i) ↦ Q
{-#  REWRITE ₀∧      #-}
{-#  REWRITE ∧₀      #-}
{-#  REWRITE ₁∧      #-}
{-#  REWRITE ∧₁      #-}  
{-#  REWRITE path-η  #-}

postulate
  coe        : {A B : Set} → A ≡ B → A → B
  regularity : (A : Set) → coe (⟨ _ ⟩ A) ↦ (λ a → a)
{-# REWRITE regularity #-}

--------------------------------------------------------------------------------

ap : ∀ {A B}(f : A → B){x y : A} → x ≡ y → f x ≡ f y
ap f p = ⟨ i ⟩ f (p $ i)

infixr 4 _◾_
_◾_ : ∀ {A}{a b c : A} → a ≡ b → b ≡ c → a ≡ c
_◾_ {a = a} {b} {c} p q = coe (ap (a ≡_) q) p

transport : ∀ {A}(P : A → Set){a b : A} → a ≡ b → P a → P b
transport P p = coe (ap P p)

ext : ∀ {A}{B : A → Set}{f g : ∀ a → B a} → (∀ a → f a ≡ g a) → f ≡ g
ext p = ⟨ i ⟩ (λ a → p a $ i)
  
J : ∀ {A}{a : A}(P : ∀ a' → a ≡ a' → Set) → P a refl → ∀ {a'} (p : a ≡ a') → P a' p
J P refl* p = coe (⟨ i ⟩ P (p $ i) (⟨ j ⟩ (p $ (i ∧ j)))) refl*

coe-refl : ∀ {A a} → coe (⟨ i ⟩ A) a ≡ a
coe-refl {A}{a} = refl

J-refl :
  ∀ {A}{a : A}(P : ∀ a' → a ≡ a' → Set) refl* → J P refl* refl ≡ refl*
J-refl {A}{a} P refl* = refl

infix 5 _⁻¹
_⁻¹ : ∀ {A}{x y : A} → x ≡ y → y ≡ x
_⁻¹ {x = x}{y} = J (λ y p → y ≡ x) refl

-- --------------------------------------------------------------------------------

-- open import Data.Nat

-- f : ℕ → ℕ
-- f = (_+ 0)

-- g : ℕ → ℕ
-- g x = x

-- p' : ∀ x → f x ≡ g x
-- p' zero    = refl
-- p' (suc x) = ap suc (p' x)

-- p : f ≡ g
-- p = ext p'

-- q : 10 ≡ 10
-- q = ap (λ f → f 10) p


