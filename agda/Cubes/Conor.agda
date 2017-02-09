{-# OPTIONS --rewriting --type-in-type #-}

open import Data.Product

Π : ∀ {ℓ ℓ′} (A : Set ℓ) (B : A → Set ℓ′) → Set _
Π A B = (x : A) → B x

infix  0 _↦_
infixl 9 _$_
infixr 9 _∙_
infix  3 _≡_

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
  $-₀        : ∀ (A : Set) (S T : A) (Q : S ≡ T) → Q $ ₀ ↦ S
  $-₁        : ∀ (A : Set) (S T : A) (Q : S ≡ T) → Q $ ₁ ↦ T
  coerce-0-0 : ∀ (S T : Set) (Q : S ≡ T) a → a [ ₀ ∣ Q ∣ ₀ ⟩ ↦ a
  coerce-1-1 : ∀ (S T : Set) (Q : S ≡ T) a → a [ ₁ ∣ Q ∣ ₁ ⟩ ↦ a

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
  path-η     : ∀ (A : Set ) (S T : A) (Q : S ≡ T) → ⟨ i ⟩ (Q $ i) ↦ Q

{-# REWRITE [₀-₀]  #-}
{-# REWRITE [₀-₁]  #-}
{-# REWRITE [₁-₁]  #-}
{-# REWRITE path-η #-}

-- this is key to J reduction!
-- in cubicaltt there's no J reduction for paths. Why/how is the thing below dodgy?
-- I think that this is sort of the analogue of the stuck coercion erasure hack from
-- OTT, except I find this nicer

-- question : what's the difference between checking whether:
--   a .) the path is constant in the sense of the I parameter not occurring inside
--   b .) the path is constant in the sense of Q $ ₀ and Q $ ₁ being definitionally equal

postulate
  coerce-const : ∀ (A : Set) a p q → a [ p ∣ ⟨ _ ⟩ A ∣ q ⟩ ↦ a
{-# REWRITE coerce-const #-}

postulate
  coerce-∙   :
    ∀ (S T U : Set) (Q : S ≡ T) (Q' : T ≡ U) (a : S)
    → a [ ₀ ∣ Q ∙ Q' ∣ ₁ ⟩ ↦ ((a [ ₀ ∣ Q ∣ ₁ ⟩) [ ₀ ∣ Q' ∣ ₁ ⟩)

  coerce-∙′  :
    ∀ (S T U : Set) (Q : S ≡ T) (Q' : T ≡ U) a
    → a [ ₁ ∣ Q ∙ Q' ∣ ₀ ⟩ ↦ ((a [ ₁ ∣ Q' ∣ ₀ ⟩) [ ₁ ∣ Q ∣ ₀ ⟩)

  coerce-Σ   : ∀ (S : I → Set) (T : (i : I) → S i → Set) (s : S ₀) (t : T ₀ s)
             → (s , t) [ ₀ ∣ ⟨ i ⟩ Σ (S i) (T i) ∣ ₁ ⟩ ↦
               let s- : (j : I) → S j
                   s- j = s [ ₀ ∣ ⟨ i ⟩ S i ∣ j ⟩
               in  s- ₁ , t [ ₀ ∣ ⟨ i ⟩ T i (s- i) ∣ ₁ ⟩

  coerce-Σ′  : ∀ (S : I → Set) (T : (i : I) → S i → Set) (s : S ₁) (t : T ₁ s)
             → (s , t) [ ₁ ∣ ⟨ i ⟩ Σ (S i) (T i) ∣ ₀ ⟩ ↦
               let s- : (j : I) → S j
                   s- j = s [ ₁ ∣ ⟨ i ⟩ S i ∣ j ⟩
               in  s- ₀ , t [ ₁ ∣ ⟨ i ⟩ T i (s- i) ∣ ₀ ⟩

  coerce-Π   : ∀ (S : I → Set) (T : (i : I) → S i → Set) (t : Π (S ₀) (T ₀))
             → (λ x → t x) [ ₀ ∣ ⟨ i ⟩ Π (S i) (T i) ∣ ₁ ⟩ ↦ λ x →
               let s- : (j : I) → S j
                   s- j = x [ ₁ ∣ ⟨ i ⟩ S i ∣ j ⟩
               in  t (s- ₀) [ ₀ ∣ ⟨ i ⟩ T i (s- i) ∣ ₁ ⟩

  coerce-Π′  : ∀ (S : I → Set) (T : (i : I) → S i → Set) (t : Π (S ₁) (T ₁))
             → (λ x → t x) [ ₁ ∣ ⟨ i ⟩ Π (S i) (T i) ∣ ₀ ⟩ ↦ λ x →
               let s- : (j : I) → S j
                   s- j = x [ ₀ ∣ ⟨ i ⟩ S i ∣ j ⟩
               in  t (s- ₁) [ ₁ ∣ ⟨ i ⟩ T i (s- i) ∣ ₀ ⟩

  coerce-≡   : ∀ (S T : I → Set) (Q : S ₀ ≡ T ₀)
             → Q [ ₀ ∣ ⟨ i ⟩ S i ≡ T i ∣ ₁ ⟩ ↦
               (⟨ i ⟩ S (i [ ₁ - ₀ ])) ∙ Q ∙ (⟨ i ⟩ T i)

  coerce-≡′  : ∀ (S T : I → Set) (Q : S ₁ ≡ T ₁)
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

refl : ∀ {ℓ} {A : Set ℓ} {a : A} → a ≡ a
refl {a = a} = ⟨ _ ⟩ a

coe : ∀ {ℓ} {S T : Set ℓ} (Q : S ≡ T) → Q $ ₀ → Q $ ₁
coe Q x = x [ ₀ ∣ Q ∣ ₁ ⟩

infix 5 _⁻¹
_⁻¹ : ∀ {A}{x y : A} → x ≡ y → y ≡ x
_⁻¹ p = ⟨ i ⟩ (p $ (i [ ₁ - ₀ ]))

infixl 6 _&_
_&_ : ∀ {A B}(f : A → B){x y : A} → x ≡ y → f x ≡ f y
_&_ f p = ⟨ i ⟩ f (p $ i)

infixr 4 _◾_
_◾_ : ∀ {A}{a b c : A} → a ≡ b → b ≡ c → a ≡ c
_◾_ {a = a} {b} {c} p q = coe ((a ≡_) & q) p

transp : ∀ {A}(P : A → Set){a b : A} → a ≡ b → P a → P b
transp P p = coe (P & p)

ext : ∀ {A}{B : A → Set}{f g : ∀ a → B a} → (∀ a → f a ≡ g a) → f ≡ g
ext {f = f} {g} p = ⟨ i ⟩ (λ a → p a $ i)

J : ∀ {A}{a : A}(P : ∀ a' → a ≡ a' → Set) → P a refl → ∀ {a'} (p : a ≡ a') → P a' p
J P refl* p = coe (⟨ i ⟩ P (p $ i) (⟨ j ⟩ (p $ i [ ₀ - j ]))) refl*

J-refl :
  ∀ {A}{a : A}(P : ∀ a' → a ≡ a' → Set) refl* → J P refl* refl ≡ refl*
J-refl P refl* = ⟨ _ ⟩ refl*  

ap2 : ∀ {A B C}(f : A → B → C){a a' b b'} → a ≡ a' → b ≡ b' → f a b ≡ f a' b'
ap2 f {a} {a'} {b} {b'} p q = ⟨ i ⟩ f (p $ i) (q $ i)

bar : (A B : Set)(p : A ≡ B) → p ◾ refl ≡ p
bar A B p = J (λ _ p₁ → p₁ ◾ refl ≡ p₁) {!!} p

foo :
  ∀ (A : Set) A' B B' (p : A ≡ A')(q : B ≡ B')(r : A ≡ B)
  → coe (ap2 _≡_ p q) r ≡ (p ⁻¹) ◾ r ◾ q
foo A A' B B' = 
  J (λ _ p₁ →
       (q₁ : B ≡ B') (r₁ : A ≡ B) →
       coe (ap2 _≡_ p₁ q₁) r₁ ≡ p₁ ⁻¹ ◾ r₁ ◾ q₁)
    (J (λ _ q → (r : A ≡ B) → coe (ap2 _≡_ refl q) r ≡ refl ⁻¹ ◾ r ◾ q)
       (J (λ _ r → coe (ap2 _≡_ refl refl) r ≡ refl ⁻¹ ◾ r ◾ refl)
         {!!}))

-- path (λ i → A) ∙ path (λ _ → A) ∙ path (λ i → A) ≡

-- path (λ i → A) ∙
-- path (λ i → A) ∙ path (λ i → A) ∙ path (λ _ → A) ∙ path (λ i → A)

