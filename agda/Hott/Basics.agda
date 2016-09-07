{-# OPTIONS --without-K --rewriting #-}

module Basics where

open import Level
open import Function
open import Data.Product
open import Relation.Binary.PropositionalEquality hiding (trans; sym) public

{-# BUILTIN REWRITE _≡_ #-}

coe : ∀ {α}{A B : Set α} → A ≡ B → A → B
coe refl = id

_⁻¹ : ∀ {α}{A : Set α}{a a' : A} → a ≡ a' → a' ≡ a
refl ⁻¹ = refl

_≡[_]_ : ∀{i}{A B : Set i} → A → A ≡ B → B → Set i
x ≡[ p ] y = coe p x ≡ y
infix 4 _≡[_]_

infixr 5 _∙_
_∙_ : ∀{a} {A : Set a} {i j k : A} → i ≡ j → j ≡ k → i ≡ k
refl ∙ q = q

ap : ∀ {a b}{A : Set a} {B : Set b} (f : A → B) {x y : A} → x ≡ y → f x ≡ f y
ap f refl = refl

apd : ∀{i j}{A : Set i}{B : A → Set j}(f : (x : A) → B x){a₀ a₁ : A}(a₂ : a₀ ≡ a₁)
    → f a₀ ≡[ ap B a₂ ] f a₁
apd f refl = refl

trans : ∀ {α β}{A : Set α} (P : A → Set β) {x y : A} → x ≡ y → P x → P y
trans P p = coe (ap P p)

coe-inv-r : ∀ {α}{A B : Set α} p a → coe {α}{A}{B} (p ⁻¹) (coe p a) ≡ a
coe-inv-r refl a = refl

coe-inv-l : ∀ {α}{A B : Set α} p a → coe {α}{A}{B} p (coe (p ⁻¹) a) ≡ a
coe-inv-l refl a = refl

_~_ : ∀ {α β} → Set α → Set β → Set (α ⊔ β)
A ~ B = ∃₂ λ (f : B → A) (g : A → B) → (∀ a → f (g a) ≡ a) × (∀ b → g (f b) ≡ b)

~sym : ∀ {α β}{A : Set α}{B : Set β} → A ~ B → B ~ A
~sym (f , g , fg , gf) = g , f , gf , fg

~trans : ∀ {α β γ}{A : Set α}{B : Set β}{C : Set γ} → A ~ B → B ~ C → A ~ C
~trans (f , g , fg , gf) (f' , g' , fg' , gf') =
  f ∘ f' ,
  g' ∘ g  ,
  (λ a → ap f (fg' (g a)) ∙ fg a) ,
  (λ b → ap g' (gf (f' b)) ∙ gf' b)

idtoeqv : ∀ {α} {A B : Set α} → A ≡ B → A ~ B
idtoeqv p = coe (p ⁻¹) , coe p , coe-inv-r p , coe-inv-l p

⟶ : ∀ {α β A B} → _~_ {α}{β} A B → (A → B)
⟶ = proj₁ ∘ proj₂

⟵ : ∀ {α β A B} → _~_ {α}{β} A B → (B → A)
⟵ = proj₁

postulate
  funext : ∀ {α β}            → Extensionality α β -- not bothering with derived funext
  ua     : ∀ {α}{A B : Set α} → A ~ B → A ≡ B
  ua-β   : ∀ {α A B} eqv      → idtoeqv {α}{A}{B} (ua eqv) ≡ eqv
  ua-η   : ∀ {α A B} p        → ua (idtoeqv {α}{A}{B} p)   ≡ p

J :
  ∀ {α β}{A : Set α}(C : {x y : A} → x ≡ y → Set β)
  → (∀ {a} → C {a} refl) → ∀ {a a'} p → C {a}{a'} p
J C refl* refl = refl*

coe-pre-∘ :
  ∀ {α β}{A : Set α}{B B' : Set β} (eqv : B ~ B')
  → trans (λ x → A → x) (ua eqv) ≡ (⟶ eqv ∘_)
coe-pre-∘ {A = A} eqv =
  J (λ p → trans (λ x → A → x) p ≡ (coe p ∘_)) refl (ua eqv) ∙
  ap (λ x → ⟶ x ∘_) (ua-β eqv)

coe-post-∘ :
  ∀ {α β}{A : Set α}{B B' : Set β} (eqv : B ~ B')
  → trans (λ x → x → A) (ua eqv) ≡ (λ f → f ∘ (⟵ eqv))
coe-post-∘ {A = A} eqv =
  J (λ p → trans (λ x → x → A) p ≡ (λ f → f ∘ coe (p ⁻¹))) refl (ua eqv) ∙
  ap (λ e f → f ∘ (⟵ e)) (ua-β eqv)

Σ-≡ :
  ∀ {α β}{A : Set α}{B : A → Set β}{a a' : A}{b : B a}{b' : B a'}
  → ((Σ A B ∋ (a , b)) ≡ (a' , b')) ~ (∃ λ (p : a ≡ a') → trans B p b ≡ b')
Σ-≡ {A = A}{B} = f , g , fg , gf where
  f : ∀ {a a' b b'} → ∃ (λ p → trans B p b ≡ b') → (Σ A B ∋ a , b) ≡ (a' , b')
  f (refl , q) = ap (,_) q

  g : ∀ {a a' b b'} → (Σ A B ∋ a , b) ≡ (a' , b') → ∃ (λ p → trans B p b ≡ b')
  g refl = refl , refl

  fg : ∀ {a a' b b'} → (p : (Σ A B ∋ a , b) ≡ (a' , b')) → f (g p) ≡ p
  fg refl = refl

  gf : ∀ {a a' b b'} → (p : ∃ (λ (p : a ≡ a') → trans B p b ≡ b')) → g (f p) ≡ p
  gf (refl , refl) = refl


