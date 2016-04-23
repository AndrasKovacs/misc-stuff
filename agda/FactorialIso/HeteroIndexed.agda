
module FactorialIso.HeteroIndexed where

import Relation.Binary.PropositionalEquality as P
open import Function
open import Data.Product

data [_]_≅_ {ι α} {I : Set ι} {i} (A : I -> Set α) (x : A i) : ∀ {j} -> A j -> Set where
  refl : [ A ] x ≅ x

trans :
  ∀ {ι α}{I : Set ι}{A : I → Set α}{i i' i''}{x : A i}{y : A i'}{z : A i''}
  → [ A ] x ≅ y → [ A ] y ≅ z → [ A ] x ≅ z
trans refl p2 = p2

sym :
  ∀ {ι α}{I : Set ι}{A : I → Set α}{i i'}{x : A i}{y : A i'}
  → [ A ] x ≅ y → [ A ] y ≅ x
sym refl = refl

cong :
  ∀ {ι α}{I : Set ι}{A : I → Set α}{i i'}{x : A i}{y : A i'}
  → {g : I → I}
  → (f : ∀ {i} → A i → A (g i))
  → [ A ] x ≅ y → [ A ] (f x) ≅ (f y)
cong f refl = refl

cong' :
  ∀ {ι α γ}{I : Set ι}{A : I → Set α}{B : I → Set γ}{i i'}{x : A i}{y : A i'}
  → (f : ∀ {i} → A i → B i)
  → [ A ] x ≅ y → [ B ] (f x) ≅ (f y)
cong' f refl = refl

subst :
  ∀ {ι α γ}{I : Set ι}{A : I → Set α}{i i'}{x : A i}{y : A i'}
  → (P : ∀ {i} → A i → Set γ)
  → [ A ] x ≅ y → P x → P y
subst P refl px = px

≅→Σ :
  ∀ {ι α}{I : Set ι}{A : I → Set α}{i i'}{x : A i}{y : A i'}
  → [ A ] x ≅ y → (Σ I A ∋ (i , x)) P.≡ (i' , y)
≅→Σ refl = P.refl

Σ→≅ :
  ∀ {ι α}{I : Set ι}{A : I → Set α}{i i'}{x : A i}{y : A i'}
  → (Σ I A ∋ (i , x)) P.≡ (i' , y) → [ A ] x ≅ y
Σ→≅ P.refl = refl  

≅→≡ :
  ∀ {ι α}{I : Set ι}{A : I → Set α}{i}{x y : A i}
  → [ A ] x ≅ y → x P.≡ y
≅→≡ refl = P.refl

≡→≅ :
  ∀ {ι α}{I : Set ι}{A : I → Set α}{i}{x y : A i}
  → x P.≡ y → [ A ] x ≅ y
≡→≅ P.refl = refl  


