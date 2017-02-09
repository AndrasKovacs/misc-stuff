
{-# OPTIONS --type-in-type --rewriting #-}

postulate _↦_ : {A : Set} → A → A → Set
{-# BUILTIN REWRITE _↦_ #-}
infix 3 _↦_

postulate
  I : Set
  ₀ ₁ : I
  _[_-_] : I → I → I → I  

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
  [₀-₀]      : ∀ p   → p [ ₀ - ₀ ] ↦ ₀
  [₀-₁]      : ∀ p   → p [ ₀ - ₁ ] ↦ p
  [₁-₁]      : ∀ p   → p [ ₁ - ₁ ] ↦ ₁
  [-]-left   : ∀ q r → ₀ [ q - r ] ↦ q
  [-]-right  : ∀ q r → ₁ [ q - r ] ↦ r
  path-η     : ∀ (A : Set) (S T : A) (Q : S ≡ T) → ⟨ i ⟩ (Q $ i) ↦ Q
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
  _∙_        : {A : Set}{x y z : A} → x ≡ y → y ≡ z → x ≡ z
  coe        : {A B : Set} → A ≡ B → A → B
  regularity : (A : Set) → coe (⟨ _ ⟩ A) ↦ (λ a → a)
{-# REWRITE regularity #-}

postulate
  coe-Π :
    (A : I → Set)(B : (i : I) → A i → Set)(f : (a : A ₀) → B ₀ a)
    → coe (⟨ i ⟩ ((a : A i) → B i a)) f
      ↦
      (λ a → coe (⟨ i ⟩ B i (coe (⟨ j ⟩ A (j [ ₁ - i ])) a ))
                 (f (coe (⟨ i ⟩ A (i [ ₁ - ₀ ])) a)))

  coe-Σ :
    (A : I → Set)(B : ∀ i → A i → Set)(p : Σ (A ₀) (B ₀))
    → coe (⟨ i ⟩ (Σ (A i) (B i))) p
    ↦ ((coe (path A) (proj₁ p)) ,
       coe (⟨ i ⟩ B i (coe (⟨ j ⟩ A (j [ ₀ - i ])) (proj₁ p))) (proj₂ p))

  coe-≡ :
      (A : I → Set)(x y : ∀ i → A i)(p : x ₀ ≡ y ₀)
    → coe (⟨ i ⟩ (_≡_ {A i} (x i) (y i))) p ↦
       ⟨ i ⟩ coe (⟨ j ⟩ (A (i [ ₁ - j ]))) (x (i [ ₁ - ₀ ]))
     ∙ ⟨ i ⟩ coe (path A) (p $ i)
     ∙ ⟨ i ⟩ coe (⟨ j ⟩ (A (i [ j - ₁ ]))) (y i) 

  coe-∙  : (A B C : Set)(p : A ≡ B)(q : B ≡ C) → coe (p ∙ q) ↦ (λ a → coe q (coe p a))
  refl-∙ : (A : Set)(x y : A)(p : x ≡ y) → refl ∙ p ↦ p
  ∙-refl : (A : Set)(x y : A)(p : x ≡ y) → p ∙ refl ↦ p

  coe-suc  : (n : ℕ)(p : ℕ ≡ ℕ) → coe p (suc n) ↦ suc (coe p n)
  coe-zero : (p : ℕ ≡ ℕ) → coe p zero ↦ zero

{-# REWRITE coe-Π #-}
{-# REWRITE coe-Σ #-}
{-# REWRITE coe-zero #-}
{-# REWRITE coe-suc #-}
{-# REWRITE coe-∙ #-}
{-# REWRITE refl-∙ #-}
{-# REWRITE ∙-refl #-}
{-# REWRITE coe-≡ #-}

infix 5 _⁻¹
_⁻¹ : ∀ {A}{x y : A} → x ≡ y → y ≡ x
_⁻¹ p = ⟨ i ⟩ (p $ (i [ ₁ - ₀ ]))

infixl 6 _&_
_&_ : ∀ {A B}(f : A → B){x y : A} → x ≡ y → f x ≡ f y
_&_ f p = ⟨ i ⟩ f (p $ i)

infixr 4 _◾_
_◾_ : ∀ {A}{a b c : A} → a ≡ b → b ≡ c → a ≡ c
_◾_ {a = a} {b} {c} p q = p ∙ q

transp : ∀ {A}(P : A → Set){a b : A} → a ≡ b → P a → P b
transp P p = coe (P & p)

ext : ∀ {A}{B : A → Set}{f g : ∀ a → B a} → (∀ a → f a ≡ g a) → f ≡ g
ext {f = f} {g} p = ⟨ i ⟩ (λ a → p a $ i)

J : ∀ {A}{a : A}(P : ∀ a' → a ≡ a' → Set) → P a refl → ∀ {a'} (p : a ≡ a') → P a' p
J P refl* p = coe (⟨ i ⟩ P (p $ i) (⟨ j ⟩ (p $ i [ ₀ - j ]))) refl*

J-refl :
  ∀ {A}{a : A}(P : ∀ a' → a ≡ a' → Set) refl* → J P refl* refl ≡ refl*
J-refl P refl* = ⟨ _ ⟩ refl*  

--------------------------------------------------------------------------------

ap2 : ∀ {A B C}(f : A → B → C){a a' b b'} → a ≡ a' → b ≡ b' → f a b ≡ f a' b'
ap2 f {a} {a'} {b} {b'} p q = ⟨ i ⟩ f (p $ i) (q $ i)

-- foo :
--   ∀ (A : Set) A' B B' (p : A ≡ A')(q : B ≡ B')(r : A ≡ B)
--   → coe (ap2 _≡_ p q) r ≡ p ⁻¹ ◾ r ◾ q
-- foo A A' B B' = λ _ _ _ → refl
  -- J (λ _ p₁ →
  --      (q₁ : B ≡ B') (r₁ : A ≡ B) →
  --      coe (ap2 _≡_ p₁ q₁) r₁ ≡ p₁ ⁻¹ ◾ r₁ ◾ q₁)
  --   (J (λ _ q → (r : A ≡ B) → coe (ap2 _≡_ refl q) r ≡ refl ⁻¹ ◾ r ◾ q)
  --      (J (λ _ r → coe (ap2 _≡_ refl refl) r ≡ refl ⁻¹ ◾ r ◾ refl)
  --        refl))



    
-- foo :
--     (A : I → Set) (B : I → Set)(p : A ₀ ≡ B ₀)
--   → coe (⟨ i ⟩ (A i ≡ B i)) p ≡ (⟨ i ⟩ A (i [ ₁ - ₀ ])) ◾ p ◾ ⟨ i ⟩ B i
-- foo A B p = refl

-- foo : ∀ {a b : Set}(p : a ≡ b) → coe (refl ◾ p) ≡ coe p
-- foo p = J (λ _ p₁ → coe (refl ◾ p₁) ≡ coe p₁) refl _ p

-- f : ℕ → Set
-- f = λ _ → ℕ

-- g : ℕ → Set
-- g zero    = ℕ
-- g (suc n) = ℕ

-- p : f ≡ g
-- p = ext (λ {zero → refl; (suc _) → refl})

-- h : ∀ n → f n
-- h = λ n → n

-- coe-→ :
--   ∀ A A' (p : A ≡ A') B B' (q : B ≡ B') (f : A → B)
--   → coe (⟨ i ⟩ (p $ i → q $ i)) f ≡ (λ a' → coe q (f (coe (p ⁻¹) a')))
-- coe-→ A =
--   J
--   (λ A'' p₁ →
--      ∀ B B' (q : B ≡ B') (f₁ : A → B) →
--      coe (path (λ i → p₁ $ i → q $ i)) f₁ ≡
--      (λ a' → coe q (f₁ (coe (p₁ ⁻¹) a'))))
--   (λ B → J {a = B}
--            (λ B' q →
--               (f₁ : A → B) →
--               coe (path (λ i → A → q $ i)) f₁ ≡ (λ a' → coe q (f₁ a')))
--            (λ f₁ → refl))     

-- i : ∀ n → g n
-- i = coe (⟨ i ⟩ ((n : ℕ) → (p $ i) n)) h

-- j : i ≡ (λ {zero → zero; (suc n) → suc n})
-- j = ext (λ {zero → {!coe-→!}; (suc n) → {!!}})


--  ((n : ℕ) → f n) ≡ ((n : ℕ) → g n)


n+0 : ∀ n → (n + 0) ≡ n
n+0 zero    = refl
n+0 (suc n) = suc & n+0 n

f : ℕ → ℕ
f x = x + 0

g : ℕ → ℕ
g x = x

p : 0 ≡ 0
p = (λ f → f 0) & (ext n+0 ◾ ext n+0 ⁻¹)

-- foo : ∀ {A B}(p : A ≡ B) → coe (p ◾ p ⁻¹) ≡ (λ x → x)
-- foo {A}{B} p = J (λ _ p₁ → coe (p₁ ◾ p₁ ⁻¹) ≡ (λ x → x)) (ext (λ a → refl)) _ p

bar : ∀ n (p : ℕ ≡ ℕ) → coe p (suc (suc n)) ≡ suc (suc (coe p n))
bar n p = refl


-- foo : ∀ {A}{x y : A}(p : x ≡ y) → p ◾ p ⁻¹ ≡ refl
-- foo {x = x} {y} p = J (λ _ p → p ◾ p ⁻¹ ≡ refl) refl y p

-- q : p ≡ refl
-- q = {!⟨ i ⟩ !}



