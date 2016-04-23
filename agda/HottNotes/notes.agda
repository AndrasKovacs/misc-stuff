

-- TT in TT :
--   higher induction in agda-hott
--   add El to TT-in-TT
--   n-ary heteroindexed equality
--   type-directed congruences

-- effectfully's TT checker with termination and positivity

-- chapman's "tt should eat itself"

{-
 Agda HIT's :

- https://github.com/HoTT/HoTT-Agda/blob/master/lib/types/HIT_README.txt

- possibly: use Agda REWRITE pragma for path constructor reduction (?)

- Bad absurd patterns again possible with Agda 2.5.1

-}

{-# OPTIONS --rewriting --without-K #-}

module notes where

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
const-subst refl p = p

I-rec :
  ∀ {i} {I* : Set i} (left* right* : I*)
  (seg* : left* ≡ right*) → I → I*
I-rec {I* = I*} left* right* seg* = I-elim (λ _ → I*) left* right* (const-subst seg seg*)

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



-- module Interval where
--   private
--     data I' : Set where
--       Zero : I'
--       One  : I'

--   I : Set
--   I = I'

--   {-# DISPLAY I' = I #-}

--   zero : I
--   zero = Zero

--   one : I
--   one = One

--   I-rec : {C : Set} 
--          -> (a b : C)
--          -> (p : a ≡ b)
--          -> I -> C
--   I-rec a b _ Zero = a
--   I-rec a b _ One = b

--   postulate 
--     seg : zero ≡ one
--     βseg : {C : Set} 
--          -> (a b : C)
--          -> (p : a ≡ b)
--          -> cong (I-rec a b p) seg ≡ p

-- module Example where
--   open Interval
  
--   ext : (A B : Set) (f g : A -> B) (α : (x : A) -> f x ≡ g x) -> f ≡ g
--   ext A B f g ht = cong (λ i x → I-rec (f x) (g x) (ht x) i) seg
    
--   -- inconsistency :
  
--   open import Data.Empty
  
--   oops : zero ≢ one
--   oops ()

--   bad : ⊥
--   bad = oops seg


-- data Phantom {α}{A : Set α}(a : A) : Set where
--   phantom : Phantom a

-- module _ where

--   private
--     data #I : Set where
--       #zero : #I
--       #one : #I

--   I = #I

--   zero : I
--   zero = #zero

--   one : I
--   one = #one

--   postulate
--     seg : zero ≡ one

--   I-elim : ∀ {i} (P : I → Set i) (zero* : P zero) (one* : P one)
--            (seg* : subst P seg zero* ≡ one*) → (i : I) → P i
--   I-elim {_} P zero* one* seg* = go phantom where
--     go : Phantom seg* → ∀ i → P i
--     go phantom #zero = zero*
--     go phantom #one  = one*

--   postulate
--     seg-β :
--       ∀ {i} (P : I → Set i) (zero* : P zero) (one* : P one)
--       (seg* : subst P seg zero* ≡ one*) → (i : I)
--       → apd (I-elim P zero* one* seg*) seg ≡ seg*
      
-- {-# REWRITE seg-β #-}




-- postulate
--   P : I → Set
--   z : P zero
--   o : P one
--   s s' : subst P seg z ≡ o

-- absurd : I-elim z o s ≡ I-elim z o s'
-- absurd = refl


-- Doesn't actually fail with Agda 2.5.1!
-- open import Data.Unit

-- module _ where

--   private
--     data #I-aux : Set where
--       #zero : #I-aux
--       #one : #I-aux

--     data #I : Set where
--       #i : #I-aux → (⊤ → ⊤) → #I

--   I : Set
--   I = #I

--   zero : I
--   zero = #i #zero _

--   one : I
--   one = #i #one _

--   postulate
--     seg : zero ≡ one

-- -- Fails
-- absurd : zero ≢ one
-- absurd ()
