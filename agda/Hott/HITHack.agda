{-
 Agda HIT's :

- https://github.com/HoTT/HoTT-Agda/blob/master/lib/types/HIT_README.txt
- Bad absurd patterns again possible with Agda 2.5.1
- REWRITE seems usable

-}

{-# OPTIONS --rewriting --without-K #-}

open import Relation.Binary.PropositionalEquality

{-# BUILTIN REWRITE _≡_ #-}

coe : ∀{i}{A B : Set i} → A ≡ B → A → B
coe refl a = a

_≡[_]≡_ : ∀{i}{A B : Set i} → A → A ≡ B → B → Set i
x ≡[ α ]≡ y = coe α x ≡ y

infix 4 _≡[_]≡_

ap : ∀{i j}{A : Set i}{B : Set j}(f : A → B){a₀ a₁ : A}(a₂ : a₀ ≡ a₁)
    → f a₀ ≡ f a₁
ap f refl = refl

apd : ∀{i j}{A : Set i}{B : A → Set j}(f : (x : A) → B x){a₀ a₁ : A}(a₂ : a₀ ≡ a₁)
    → f a₀ ≡[ ap B a₂ ]≡ f a₁
apd f refl = refl

postulate
  I     : Set
  left  : I
  right : I
  seg   : left ≡ right

  I-elim :
    ∀ {i} (P : I → Set i) (left* : P left) (right* : P right)
    (seg* : left* ≡[ ap P seg ]≡ right*)(i : I) → P i

postulate
  β-left :
    ∀ {i} (P : I → Set i) (left* : P left) (right* : P right)
    (seg* : left* ≡[ ap P seg ]≡ right*)(i : I) → I-elim P left* right* seg* left ≡ left*    
{-# REWRITE β-left #-}

postulate
  β-right :
    ∀ {i} (P : I → Set i) (left* : P left) (right* : P right)
    (seg* : left* ≡[ ap P seg ]≡ right*)(i : I) → I-elim P left* right* seg* right ≡ right*
{-# REWRITE β-right #-}    

postulate
  β-seg :
    ∀ {i} (P : I → Set i) (left* : P left) (right* : P right)
    (seg* : left* ≡[ ap P seg ]≡ right*)(i : I) → apd (I-elim P left* right* seg*) seg ≡ seg*
{-# REWRITE β-seg #-}

open import Function

const-subst :
  ∀ {i j}{A : Set i}{B : Set j}{b b' : B}{a a' : A}(p : a ≡ a')
  → b ≡ b' → coe (ap (const B) p) b ≡ b'
const-subst refl q = q

I-rec :
  ∀ {i} {I* : Set i} (left* right* : I*)
  (seg* : left* ≡ right*) → I → I*
I-rec {I* = I*} left* right* seg* =
  I-elim (λ _ → I*) left* right* (const-subst seg seg*)

open import Data.Nat

test : apd (I-elim (const ℕ) 10 10 (const-subst seg refl)) seg ≡ const-subst seg refl
test = refl

-- this is alright
bad1 : left ≢ right
bad1 p = {!!}

postulate
  P : I → Set
  l : P left
  r : P right
  s s' : l ≡[ ap P seg ]≡ r

-- this is alright too
bad2 : I-elim P l r s ≡ I-elim P l r s'
bad2 = {!!}

ext : (A B : Set) (f g : A -> B) (α : (x : A) -> f x ≡ g x) -> f ≡ g
ext A B f g ht = ap (λ i x → I-elim _ (f x) (g x) (const-subst seg (ht x)) i) seg

ext' : (A B : Set) (f g : A -> B) (α : (x : A) -> f x ≡ g x) -> f ≡ g
ext' A B f g ht = ap (λ i x → I-rec (f x) (g x) (ht x) i) seg

-- I is contractible (see HoTT book 6.3.1 )

open import Data.Product

IsContr : ∀ {α} → Set α → Set α
IsContr A = ∃ λ (a : A) → ∀ a' → a' ≡ a

lem :
  ∀ {α}{A : Set α} (a x x' : A)(p : x ≡ x')(q : x ≡ a)
  →  coe (ap (λ x → x ≡ a) p) q ≡ trans (sym p) q
lem a x .x refl q = refl

lem2 : ∀ {α}{A : Set α}{a a' : A} (p : a ≡ a') → trans (sym p) p ≡ refl
lem2 refl = refl

p : IsContr I
p = right , (I-elim (λ i → i ≡ right) seg refl (trans (lem _ _ _ seg seg) (lem2 seg)))
