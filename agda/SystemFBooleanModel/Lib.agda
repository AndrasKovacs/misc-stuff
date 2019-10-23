{-# OPTIONS --without-K --postfix-projections #-}

module Lib where

open import Relation.Binary.PropositionalEquality
open import Relation.Binary.PropositionalEquality public using (refl; _≡_; [_]; inspect)
open import Data.Bool public
open import Data.Unit using (tt; ⊤) public
open import Data.Product renaming (proj₁ to ₁; proj₂ to ₂) public
open import Data.Empty public
open import Relation.Nullary public using (¬_)
open import Data.Sum public using (inj₁; inj₂; _⊎_)

_&_ = cong;  infixl 9 _&_; {-# DISPLAY _&_ = cong  #-}
_◾_ = trans; infixr 4 _◾_; {-# DISPLAY _◾_ = trans #-}
_⁻¹ = sym;   infix  6 _⁻¹; {-# DISPLAY _⁻¹ = sym   #-}

coe : ∀{i}{A B : Set i} → A ≡ B → A → B
coe refl a = a

_⊗_ : ∀ {α β}{A : Set α}{B : Set β}
        {f g : A → B}(p : f ≡ g){a a'}
      → a ≡ a' → f a ≡ g a'
refl ⊗ refl = refl
infixl 8 _⊗_
