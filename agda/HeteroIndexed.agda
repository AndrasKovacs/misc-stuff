
module HeteroIndexed where

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
  ∀ {ι α γ}{I : Set ι}{A : I → Set α}{B : I → Set γ}{i i'}{x : A i}{y : A i'}
  → (f : ∀ {i} → A i → B i)
  → [ A ] x ≅ y → [ B ] (f x) ≅ (f y)
cong f refl = refl

subst :
  ∀ {ι α γ}{I : Set ι}{A : I → Set α}{i i'}{x : A i}{y : A i'}
  → (P : ∀ {i} → A i → Set γ)
  → [ A ] x ≅ y → P x → P y
subst P refl px = px  






