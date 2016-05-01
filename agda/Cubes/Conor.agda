{-# OPTIONS --rewriting #-}

open import Data.Product

Π : ∀ {ℓ ℓ′} (A : Set ℓ) (B : A → Set ℓ′) → Set _
Π A B = (x : A) → B x

infix  0 _↦_
infixl 9 _$_
infixr 9 _∙_ 
infix  4 _≡_

postulate _↦_ : ∀ {a} {A : Set a} → A → A → Set
{-# BUILTIN REWRITE _↦_ #-}

postulate
  I        : Set
  ₀ ₁      : I
  _[_-_]   : I → I → I → I

data _≡_ {ℓ} {A : Set ℓ} : A → A → Set ℓ where
  path : (M : I → A) → M ₀ ≡ M ₁

_$_ : ∀ {ℓ} {A : Set ℓ} {a b : A} → a ≡ b → I → A
path M $ i = M i

postulate
  coerce   : ∀ {ℓ} {S T : Set ℓ} (Q : S ≡ T) (p q : I) → Q $ p → Q $ q
  _∙_      : ∀ {ℓ} {S T U : Set ℓ} → S ≡ T → T ≡ U → S ≡ U

infixr 20 coerce
syntax coerce Q p q a = a [ p ∣ Q ∣ q ⟩

infix 2 path
syntax path (λ i → t) = ⟨ i ⟩ t

postulate
  [-]-left   : ∀ q r → ₀ [ q - r ] ↦ q
  [-]-right  : ∀ q r → ₁ [ q - r ] ↦ r
  $-₀        : ∀ ℓ (A : Set ℓ) (S T : A) (Q : S ≡ T) → Q $ ₀ ↦ S
  $-₁        : ∀ ℓ (A : Set ℓ) (S T : A) (Q : S ≡ T) → Q $ ₁ ↦ T  
  coerce-0-0 : ∀ ℓ (S T : Set ℓ) (Q : S ≡ T) a → a [ ₀ ∣ Q ∣ ₀ ⟩ ↦ a
  coerce-1-1 : ∀ ℓ (S T : Set ℓ) (Q : S ≡ T) a → a [ ₁ ∣ Q ∣ ₁ ⟩ ↦ a

{-# REWRITE [-]-left   #-}
{-# REWRITE [-]-right  #-}
{-# REWRITE $-₀        #-}
{-# REWRITE $-₁        #-}
{-# REWRITE coerce-0-0 #-}
{-# REWRITE coerce-1-1 #-}

postulate
  [₀-₀]      : ∀ p → p [ ₀ - ₀ ] ↦ ₀
  [₀-₁]      : ∀ p → p [ ₀ - ₁ ] ↦ p
  [₁-₁]      : ∀ p → p [ ₁ - ₁ ] ↦ ₁
  path-η     : ∀ ℓ (A : Set ℓ) (S T : A) (Q : S ≡ T) → ⟨ i ⟩ (Q $ i) ↦ Q

{-# REWRITE [₀-₀]  #-}
{-# REWRITE [₀-₁]  #-}
{-# REWRITE [₁-₁]  #-}
{-# REWRITE path-η #-}

-- this is key to J reduction!
-- in cubicaltt there's no J reduction for paths. Why/how is the thing below dodgy?
-- I think that this is sort of the analogue of the stuck coercion erasure hack from
-- OTT, except I find this nicer
postulate
  coerce-const : ∀ ℓ (A : Set ℓ) a p q → a [ p ∣ ⟨ _ ⟩ A ∣ q ⟩ ↦ a

{-# REWRITE coerce-const #-}

postulate
  -- is this even needed, along with composition?
  -- can we just inline this into coerce-≡ ?
  coerce-∙   :
    ∀ ℓ (S T U : Set ℓ) (Q : S ≡ T) (Q' : T ≡ U) (a : S)
    → a [ ₀ ∣ Q ∙ Q' ∣ ₁ ⟩ ↦ ((a [ ₀ ∣ Q ∣ ₁ ⟩) [ ₀ ∣ Q' ∣ ₁ ⟩)
    
  coerce-∙′  :
    ∀ ℓ (S T U : Set ℓ) (Q : S ≡ T) (Q' : T ≡ U) a
    → a [ ₁ ∣ Q ∙ Q' ∣ ₀ ⟩ ↦ ((a [ ₁ ∣ Q' ∣ ₀ ⟩) [ ₁ ∣ Q ∣ ₀ ⟩)

  coerce-Σ   : ∀ ℓ (S : I → Set ℓ) (T : (i : I) → S i → Set ℓ) (s : S ₀) (t : T ₀ s)
             → (s , t) [ ₀ ∣ ⟨ i ⟩ Σ (S i) (T i) ∣ ₁ ⟩ ↦
               let s- : (j : I) → S j
                   s- j = s [ ₀ ∣ ⟨ i ⟩ S i ∣ j ⟩
               in  s- ₁ , t [ ₀ ∣ ⟨ i ⟩ T i (s- i) ∣ ₁ ⟩

  coerce-Σ′  : ∀ ℓ (S : I → Set ℓ) (T : (i : I) → S i → Set ℓ) (s : S ₁) (t : T ₁ s)
             → (s , t) [ ₁ ∣ ⟨ i ⟩ Σ (S i) (T i) ∣ ₀ ⟩ ↦
               let s- : (j : I) → S j
                   s- j = s [ ₁ ∣ ⟨ i ⟩ S i ∣ j ⟩
               in  s- ₀ , t [ ₁ ∣ ⟨ i ⟩ T i (s- i) ∣ ₀ ⟩

  coerce-Π   : ∀ ℓ (S : I → Set ℓ) (T : (i : I) → S i → Set ℓ) (t : Π (S ₀) (T ₀))
             → (λ x → t x) [ ₀ ∣ ⟨ i ⟩ Π (S i) (T i) ∣ ₁ ⟩ ↦ λ x →
               let s- : (j : I) → S j
                   s- j = x [ ₁ ∣ ⟨ i ⟩ S i ∣ j ⟩
               in  t (s- ₀) [ ₀ ∣ ⟨ i ⟩ T i (s- i) ∣ ₁ ⟩

  coerce-Π′  : ∀ ℓ (S : I → Set ℓ) (T : (i : I) → S i → Set ℓ) (t : Π (S ₁) (T ₁))
             → (λ x → t x) [ ₁ ∣ ⟨ i ⟩ Π (S i) (T i) ∣ ₀ ⟩ ↦ λ x →
               let s- : (j : I) → S j
                   s- j = x [ ₀ ∣ ⟨ i ⟩ S i ∣ j ⟩
               in  t (s- ₁) [ ₁ ∣ ⟨ i ⟩ T i (s- i) ∣ ₀ ⟩

  coerce-≡   : ∀ ℓ (S T : I → Set ℓ) (Q : S ₀ ≡ T ₀)
             → Q [ ₀ ∣ ⟨ i ⟩ S i ≡ T i ∣ ₁ ⟩ ↦ 
               (⟨ i ⟩ S (i [ ₁ - ₀ ])) ∙ Q ∙ (⟨ i ⟩ T i)

  coerce-≡′  : ∀ ℓ (S T : I → Set ℓ) (Q : S ₁ ≡ T ₁)
             → Q [ ₁ ∣ ⟨ i ⟩ S i ≡ T i ∣ ₀ ⟩ ↦
               (⟨ i ⟩ S i) ∙ Q ∙ (⟨ i ⟩ T (i [ ₁ - ₀ ]))

{-# REWRITE coerce-∙  #-}
{-# REWRITE coerce-∙′ #-}
{-# REWRITE coerce-Σ  #-}
{-# REWRITE coerce-Σ′ #-}
{-# REWRITE coerce-Π  #-}
{-# REWRITE coerce-Π′ #-}
{-# REWRITE coerce-≡  #-}
{-# REWRITE coerce-≡′ #-}

open import Function using (_∘_)

coe : ∀ {ℓ} {S T : Set ℓ} (Q : S ≡ T) → Q $ ₀ → Q $ ₁
coe Q x = x [ ₀ ∣ Q ∣ ₁ ⟩

_∧_ : ∀ {ℓ}{A : Set ℓ}{x y : A} → (p : x ≡ y) → (i : I) → x ≡ p $ i
p ∧ i = ⟨ j ⟩ (p $ i [ ₀ - j ])

_∨_ : ∀ {ℓ}{A : Set ℓ}{x y : A} → (p : x ≡ y) → (i : I) → p $ i ≡ y
p ∨ i = ⟨ j ⟩ (p $ i [ j - ₁ ])

1-_ : I → I
1- i = i [ ₁ - ₀ ]

refl : ∀ {ℓ} {A : Set ℓ} {a : A} → a ≡ a
refl {a = a} = ⟨ _ ⟩ a

ap : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} (f : A → B)
       {x y : A} → x ≡ y → f x ≡ f y
ap f p = ⟨ i ⟩ f (p $ i)

sym : ∀ {ℓ}{A : Set ℓ}{x y : A} → x ≡ y → y ≡ x
sym p = ⟨ i ⟩ (p $ 1- i)

trans : ∀ {ℓ}{A : Set ℓ}{x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans {x = x}{y}{z} p q = coe (⟨ i ⟩ x ≡ q $ i) p

subst : ∀ {ℓ ℓ'} {A : Set ℓ} (B : A → Set ℓ')
        {x y : A} → x ≡ y → B x → B y
subst B = coe ∘ ap B

apd : ∀ {ℓ ℓ'} {A : Set ℓ} {B : A → Set ℓ'} (f : Π A B)
       {x y : A} → (p : x ≡ y) → subst B p (f x) ≡ f y
apd {B = B} f p = ⟨ i ⟩ subst B (p ∨ i) (f (p $ i)) 

module ApReduce where

  p1 : ∀ {A B : Set}(f : A → B) x → ap f (refl {a = x}) ≡ refl {a = f x}
  p1 _ _ = refl
  
  open import Function hiding (_$_)
  
  p2 : ∀ {A : Set}(x y : A) (p : x ≡ y) → ap id p ≡ p
  p2 _ _ _ = refl
  
  p3 : ∀ {A B C : Set}(f : B → C) (g : A → B){x y} → ap (f ∘ g) {x}{y} ≡ ap f ∘ ap g
  p3 f g = refl

J : ∀ {ℓ ℓ′} {A : Set ℓ} {x : A} (P : (y : A) → x ≡ y → Set ℓ′)
  → P x refl → {y : A} (e : x ≡ y) → P y e
J P refl* e = coe (⟨ i ⟩ P (e $ i) (e ∧ i)) refl*

-- subst-subst : ∀ {ℓ}{A : Set ℓ}(x y : A) → (p : x ≡ y) → subst (_≡ y) p p ≡ refl
-- subst-subst x y p = ⟨ i ⟩ subst (_≡ y) (p ∨ i) (p ∨ i)

-- Contr : ∀ {α} → Set α → Set α
-- Contr A = ∃ λ (a : A) → ∀ a' → a ≡ a'

-- Sing : ∀ {α} → (A : Set α) → A → Set α
-- Sing A a = ∃ λ b → a ≡ b

-- singContr : ∀ {α A} a → Contr {α} (Sing A a)
-- singContr a = (a , refl) , (λ {(_ , p) → ⟨ i ⟩ p $ i , p ∧ i})

-- symInvolutive : ∀ {ℓ}{A : Set ℓ}{x y : A} (p : x ≡ y) → sym (sym p) ≡ p
-- symInvolutive p = ⟨ j ⟩ ⟨ i ⟩ p $ j [ (1- 1- i) - i ]

-- left-id : ∀ {ℓ}{A : Set ℓ}{x y : A}(p : x ≡ y) → refl ≡ trans p (sym p)
-- left-id {x = x}{y} p = ⟨ i ⟩ trans (p ∧ i) (sym (p ∧ i))

-- J-refl : ∀ {ℓ ℓ′} {A : Set ℓ} {x : A} (P : (y : A) → x ≡ y → Set ℓ′)
--        → (p : P x refl) → J P p refl ≡ p
-- J-refl {x = x} P p = {!J P p refl!}

-- funext : ∀ {ℓ ℓ'} {A : Set ℓ} {B : A → Set ℓ'} {f g : (x : A) → B x}
--            → (∀ x → f x ≡ g x) → f ≡ g
-- funext p = ⟨ i ⟩ (λ x → p x $ i)
