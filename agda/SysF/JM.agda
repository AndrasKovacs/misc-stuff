{-# OPTIONS --no-eta #-}

module JM where

open import Level
open import Lib

record _≃_ {i : Level}{A B : Set i}(a : A)(b : B) : Set (suc i) where
  constructor _,≃_
  field
    projT : A ≡ B
    projt : a ≡[ projT ]≡ b

infixl 5 _,≃_
infix 4 _≃_

open _≃_

_◾̃_ : ∀{i}{A B C : Set i}{a : A}{b : B}{c : C}
    → a ≃ b → b ≃ c → a ≃ c
(refl ,≃ refl) ◾̃ (refl ,≃ refl) = refl ,≃ refl

infixl 4 _◾̃_

_⁻¹̃ : ∀{i}{A B : Set i}{a : A}{b : B}
    → a ≃ b → b ≃ a
(refl ,≃ refl) ⁻¹̃ = refl ,≃ refl

infix 5 _⁻¹̃

r̃ : ∀{i}{A : Set i}{a : A} → a ≃ a
r̃ = refl ,≃ refl

_≃⟨_⟩_ : ∀{i}{A B C : Set i}(x : A){y : B}{z : C} → x ≃ y → y ≃ z → x ≃ z
x ≃⟨ x≃y ⟩ y≃z = x≃y ◾̃ y≃z

infixr 2 _≃⟨_⟩_

_∎̃ : ∀{i}{A : Set i}(x : A) → x ≃ x
x ∎̃ = r̃

infix  3 _∎̃

uncoe : ∀{i}{A B : Set i}{a : A}(p : A ≡ B) → a ≃ coe p a
uncoe p = p ,≃ refl

to≃ : ∀{i}{A : Set i}{a a' : A} → a ≡ a' → a ≃ a'
to≃ p = refl ,≃ p

from≃ : ∀{i}{A : Set i}{a a' : A}
      → a ≃ a' → a ≡ a'
from≃ (refl ,≃ refl) = refl

from≡ : ∀{i}{A B : Set i}(p : A ≡ B){a : A}{b : B}
      → a ≡[ p ]≡ b → a ≃ b
from≡ refl refl = refl ,≃ refl

to≡ : ∀{i}{A B : Set i}{a : A}{b : B}
      (p : a ≃ b) → a ≡[ projT p ]≡ b
to≡ (refl ,≃ refl) = refl

&≃ : ∀{i j k}{A : Set i}{B : A → Set j}{C : A → Set k}(f : {x : A} → B x → C x)
      {a₀ a₁ : A}(a₂ : a₀ ≡ a₁)
      {b₀ : B a₀}{b₁ : B a₁}(b₂ : b₀ ≃ b₁)
    → f b₀ ≃ f b₁
&≃ f refl (refl ,≃ refl) = refl ,≃ refl

&≃' : ∀{i j k}{A : Set i}{B : A → Set j}{C : {x : A} → B x → Set k}
       (f : {x : A}(y : B x) → C y)
       {a₀ a₁ : A}(a₂ : a₀ ≡ a₁)
       {b₀ : B a₀}{b₁ : B a₁}(b₂ : b₀ ≃ b₁)
     → f b₀ ≃ f b₁
&≃' f refl (refl ,≃ refl) = refl ,≃ refl

apd≃ : ∀{i j}{A : Set i}{B : A → Set j}(f : (x : A) → B x)
      → {a₀ a₁ : A}(a₂ : a₀ ≡ a₁)
      → f a₀ ≃ f a₁
apd≃ f refl = refl ,≃ refl

apd≃' : ∀{i j}{A₀ A₁ : Set i}
        {B₀ : A₀ → Set j}{B₁ : A₁ → Set j}(B₂ : B₀ ≃ B₁)
        {f₀ : (x : A₀) → B₀ x}{f₁ : (x : A₁) → B₁ x}
        (f₂ : f₀ ≃ f₁)
        {a₀ : A₀}{a₁ : A₁}(a₂ : a₀ ≃ a₁)
      → f₀ a₀ ≃ f₁ a₁
apd≃' (refl ,≃ refl) (refl ,≃ refl) (refl ,≃ refl) = refl ,≃ refl

&≃'' : ∀{i j k}{A : Set i}{B : A → Set j}
        {C₀ C₁ : (x : A) → B x → Set k}(C₂ : C₀ ≡ C₁)
        {f₀ : {x : A}(y : B x) → C₀ x y}{f₁ : {x : A}(y : B x) → C₁ x y}
        (f₂ : (λ {x} → f₀ {x}) ≃ (λ {x} → f₁ {x}))
        {a : A}{b : B a}
      → f₀ b ≃ f₁ b
&≃'' refl (refl ,≃ refl) = refl ,≃ refl

UIP : ∀{i}{A : Set i}{x y : A}(p q : x ≡ y) → p ≡ q
UIP refl refl = refl

UIP-coe : ∀{i}{A B : Set i}(p q : A ≡ B) x → coe p x ≡ coe q x
UIP-coe refl refl _ = refl

loopcoe : ∀{i}{A : Set i}(p : A ≡ A){a : A} → coe p a ≡ a
loopcoe refl = refl

ext≃' :
  ∀ {i j}{A : Set i}{B₀ B₁ : A → Set j}
    {f₀ : (x : A) → B₀ x}{f₁ : (x : A) → B₁ x}
  → ((x : A) → f₀ x ≃ f₁ x)
  → f₀ ≃ f₁
ext≃' {i}{j}{A}{B₀}{B₁}{f₀}{f₁} p =
  (λ z → (x : A) → z x) & ext (λ x → projT (p x))
  ,≃ ext λ x →  coe-$ (λ z b → b z) (ext (λ x → projT (p x))) f₀ &' x
              ◾ UIP-coe ((λ b → b x) & ext (λ x₁ → projT (p x₁))) (projT (p x)) (f₀ x)
              ◾ projt (p x)

exti≃' :
  ∀ {i j}{A : Set i}{B₀ B₁ : A → Set j}
    {f₀ : {x : A} → B₀ x}{f₁ : {x : A} → B₁ x}
  → ((x : A) → f₀ {x} ≃ f₁ {x})
  → (λ {x} → f₀ {x}) ≃ (λ {x} → f₁ {x})
exti≃' {i}{j}{A}{B₀}{B₁}{f₀}{f₁} p =
  (λ z → {x : A} → z x) & ext (λ x → projT (p x))
  ,≃ exti λ x → (λ f → f {x}) & coe-$-i (λ z b → b z) (ext (λ x → projT (p x))) f₀
              ◾ UIP-coe ((λ b → b x) & ext (λ x₁ → projT (p x₁))) (projT (p x)) (f₀ {x})
              ◾ projt (p x)


-- coe-$ ? (ext (λ x → projT (p x))) f₀ x


-- funext≃' :  ∀{i j}{A : Set i}{B₀ B₁ : A → Set j}
--             {f₀ : (x : A) → B₀ x}{f₁ : (x : A) → B₁ x}
--           → ((x : A) → f₀ x ≃ f₁ x)
--           → f₀ ≃ f₁
-- funext≃' {i}{j}{A}{B₀}{B₁}{f₀}{f₁} p

--   = ap (λ z → (x : A) → z x) (funext (λ x → projT (p x)))
--   ,≃ funext (λ x → from≃ ( ap≃ {A = A → Set j}
--                                {λ B → (x : A) → B x}
--                                {λ B → B x}
--                                (λ f → f x)
--                                {B₁}
--                                {B₀}
--                                (funext (λ x → projT (p x) ⁻¹))
--                                (uncoe (ap (λ z → (x : A) → z x) (funext (λ x → projT (p x)))) ⁻¹̃)
--                         ◾̃ p x))

-- funexti≃' : ∀{i j}{A : Set i}{B₀ B₁ : A → Set j}
--             {f₀ : {x : A} → B₀ x}{f₁ : {x : A} → B₁ x}
--           → ((x : A) → f₀ {x} ≃ f₁ {x})
--           → (λ {x} →  f₀ {x}) ≃ (λ {x} → f₁ {x})
-- funexti≃' {i}{j}{A}{B₀}{B₁}{f₀}{f₁} p

--   = ap (λ z → {x : A} → z x) (funext (λ x → projT (p x)))
--   ,≃ funexti (λ x → from≃ ( ap≃ {A = A → Set j}
--                                {λ B → {x : A} → B x}
--                                {λ B → B x}
--                                (λ f → f {x})
--                                {B₁}
--                                {B₀}
--                                (funext (λ x → projT (p x) ⁻¹))
--                                (uncoe (ap (λ z → {x : A} → z x) (funext (λ x → projT (p x)))) ⁻¹̃)
--                         ◾̃ p x))

-- funext≃   : ∀{i j}{A₀ A₁ : Set i}(A₂ : A₀ ≡ A₁)
--             {B₀ : A₀ → Set j}{B₁ : A₁ → Set j}
--             {f₀ : (x : A₀) → B₀ x}{f₁ : (x : A₁) → B₁ x}
--           → ({x₀ : A₀}{x₁ : A₁}(x₂ : x₀ ≃ x₁) → f₀ x₀ ≃ f₁ x₁)
--           → f₀ ≃ f₁
-- funext≃ {i}{j}{A} refl {B₀}{B₁}{f₀}{f₁} p

--   = ap (λ z → (x : A) → z x) (funext (λ x → projT (p {x} r̃)))
--   ,≃ funext (λ x → from≃ ( ap≃ {A = A → Set j}
--                               {λ B → (x : A) → B x}
--                               {λ B → B x}
--                               (λ f → f x)
--                               {B₁}
--                               {B₀}
--                               (funext (λ x → projT (p {x} r̃) ⁻¹))
--                               (uncoe (ap (λ z → (x : A) → z x) (funext (λ x₁ → projT (p r̃)))) ⁻¹̃)
--                         ◾̃ p {x} r̃))

-- funexti≃  : ∀{i j}{A₀ A₁ : Set i}(A₂ : A₀ ≡ A₁)
--             {B₀ : A₀ → Set j}{B₁ : A₁ → Set j}
--             {f₀ : {x : A₀} → B₀ x}{f₁ : {x : A₁} → B₁ x}
--           → ({x₀ : A₀}{x₁ : A₁}(x₂ : x₀ ≃ x₁) → f₀ {x₀} ≃ f₁ {x₁})
--           → (λ {x} →  f₀ {x}) ≃ (λ {x} → f₁ {x})
-- funexti≃ {i}{j}{A} refl {B₀}{B₁}{f₀}{f₁} p

--   = (ap (λ z → {x : A} → z x) ((funext (λ x → projT (p {x} r̃)))))
--   ,≃ funexti (λ x → from≃ ( ap≃ {A = A → Set j}
--                                {λ B → {x : A} → B x}
--                                {λ B → B x}
--                                (λ f → f {x})
--                                {B₁}
--                                {B₀}
--                                (funext (λ x → projT (p {x} r̃) ⁻¹))
--                                (uncoe (ap (λ z → {x : A} → z x) (funext (λ x₁ → projT (p r̃)))) ⁻¹̃)
--                          ◾̃ p {x} r̃))

→≃ : ∀{i j}{A₀ A₁ : Set i}(A₂ : A₀ ≡ A₁)
     {B₀ : A₀ → Set j}{B₁ : A₁ → Set j}(B₂ : B₀ ≃ B₁)
   → ((x : A₀) → B₀ x) ≡ ((x : A₁) → B₁ x)
→≃ refl (refl ,≃ refl) = refl

→i≃ : ∀{i j}{A₀ A₁ : Set i}(A₂ : A₀ ≡ A₁)
      {B₀ : A₀ → Set j}{B₁ : A₁ → Set j}(B₂ : B₀ ≃ B₁)
    → ({x : A₀} → B₀ x) ≡ ({x : A₁} → B₁ x)
→i≃ refl (refl ,≃ refl) = refl

Σ≃ : ∀{i j}{A₀ A₁ : Set i}(A₂ : A₀ ≡ A₁)
     {B₀ : A₀ → Set j}{B₁ : A₁ → Set j}(B₂ : B₀ ≃ B₁)
   → Σ A₀ B₀ ≡ Σ A₁ B₁
Σ≃ refl (refl ,≃ refl) = refl

≡≃ : ∀{i}{A₀ A₁ : Set i}(A₂ : A₀ ≡ A₁)
     {a₀₀ a₀₁ : A₀}{a₁₀ a₁₁ : A₁}
     (a₂₀ : a₀₀ ≃ a₁₀)(a₂₁ : a₀₁ ≃ a₁₁)
   → (a₀₀ ≡ a₀₁) ≃ (a₁₀ ≡ a₁₁)
≡≃ refl (refl ,≃ refl) (refl ,≃ refl) = refl ,≃ refl

,Σ≃≃ : ∀{i j}{A₀ A₁ : Set i}
     {B₀ : A₀ → Set j}{B₁ : A₁ → Set j}(B₂ : B₀ ≃ B₁)
     {a₀ : A₀}{a₁ : A₁}(a₂ : a₀ ≃ a₁)
     {b₀ : B₀ a₀}{b₁ : B₁ a₁}(b₂ : b₀ ≃ b₁)
   → _≃_
     {A = Σ A₀ B₀}
     {B = Σ A₁ B₁}
     (a₀ , b₀)
     (a₁ , b₁)
,Σ≃≃ (refl ,≃ refl) (refl ,≃ refl) (refl ,≃ refl) = refl ,≃ refl

,Σ≃' : ∀{i j}{A : Set i}{B : A → Set j}
     {a₀ a₁ : A}(a₂ : a₀ ≡ a₁)
     {b₀ : B a₀}{b₁ : B a₁}(b₂ : b₀ ≃ b₁)
   → _≡_ {A = Σ A B} (a₀ , b₀) (a₁ , b₁)
,Σ≃' refl (refl ,≃ refl) = refl

proj₁coe : {A₀ A₁ : Set}(A₂ : A₀ ≡ A₁)
           {B₀ : A₀ → Set}{B₁ : A₁ → Set}(B₂ : B₀ ≡[ (λ z → z → Set) & A₂ ]≡ B₁)
           (p : Σ A₀ B₀ ≡ Σ A₁ B₁)
           {a₀ : A₀}{b₀ : B₀ a₀}
         → a₀ ≃ proj₁ (coe p (a₀ , b₀))
proj₁coe refl refl refl = refl ,≃ refl

UIP' : ∀{i}{A B : Set i}{a : A}{b : B}
       (p q : A ≡ B) → a ≡[ p ]≡ b → a ≡[ q ]≡ b
UIP' refl refl refl = refl
