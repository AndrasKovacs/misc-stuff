{-# OPTIONS --type-in-type #-}

open import Data.Empty
open import Data.Unit

P = λ A → A → Set

postulate
  peirce : ∀ A B → ((A → B) → A) → A
  peirce' :
    ∀ A (A' : P A) B (B' : P B)
      (f : (A → B) → A)(f' : (g : A → B)(g' : ∀ a → A' a → B' (g a)) → A' (f g))
    → A' (peirce A B f)

bot : ⊥
bot = peirce' ⊤ (λ _ → ⊥) ⊥ (λ _ → ⊥) (λ _ → tt) (λ f _ → f tt)







{-

{-# OPTIONS --type-in-type #-}
-- parametricity inconsistent with classical logic

open import Function

Eq : (A : Set) → A → A → Set
Eq A x y = (P : A → Set) → P x → P y

refl : ∀ {A} x → Eq A x x
refl x P px = px

_⁻¹ : ∀ {A x y} → Eq A x y → Eq A y x
p ⁻¹ = λ P → p (λ z → P z → P _) (λ x → x)

_◾_ : ∀ {A x y z} → Eq A x y → Eq A y z → Eq A x z
p ◾ q = λ P z → q P (p P z)

_&_ : ∀ {A B x y}(f : A → B) → Eq A x y → Eq B (f x) (f y)
f & p = λ P → p (λ z → P (f z))

infixr 5 _◾_
infixl 6 _⁻¹
infixl 4 _&_

------------------------------------------------------------

record Nat : Set where
  constructor con
  field
    C : Set
    z : C
    s : C → C
open Nat

record Nat⇒ (N N' : Nat) : Set where
  constructor con
  open Nat
  field
    rec  : C N → C N'
    recz : Eq _ (rec (z N)) (z N')
    recs : ∀ n → Eq _ (rec (s N n)) (s N' (rec n))
open Nat⇒

data ⊥ : Set where

record ⊤ : Set where
  constructor tt

Nat∘ : ∀ {N N' N'' : Nat} → Nat⇒ N' N'' → Nat⇒ N N' → Nat⇒ N N''
Nat∘ (con rec recz recs) (con rec' recz' recs') =
  con (rec ∘ rec') ((rec & recz') ◾ recz) (λ n → (rec & recs' n) ◾ (recs (rec' n)))

Nat-id : (N : Nat) → Nat⇒ N N
Nat-id (con C z s) = con id (refl z) (λ n → refl (s n))

record Initial (N : Nat) : Set where
  constructor con
  field
    init : (N' : Nat) → Nat⇒ N N'
    univ : (N' : Nat) → (f : Nat⇒ N N') → Eq _ f (init N')
open Initial

init-id : (N : Nat)(iN : Initial N)(f : Nat⇒ N N) → Eq _ f (Nat-id N)
init-id N i f = univ i N f ◾ univ i N (Nat-id N) ⁻¹

-- rec-id : {N : Nat}{f : Nat⇒ N N} → Eq _ f (Nat-id N) → Eq _ (rec f) id
-- rec-id p = rec & p

-- open import Data.Product

-- init-ind :
--   (ℕ : Nat)(i : Initial ℕ)(P : C ℕ → Set) → (∀ n → P n → P (s ℕ n)) → P (z ℕ) → ∀ n → P n
-- init-ind ℕ i P ps pz n =
--   subst P (cong (_$ n) (rec-id _ (init-id ℕ i fromTo))) (proj₂ (rec to n))
--   where
--     ℕP : Nat
--     ℕP = con (∃ P) (z ℕ , pz) (λ {(n , pn) → (s ℕ n , ps n pn)})

--     to : Nat⇒ ℕ ℕP
--     to = init i ℕP

--     from : Nat⇒ ℕP ℕ
--     from = con proj₁ refl (λ n → refl)

--     fromTo : Nat⇒ ℕ ℕ
--     fromTo = Nat∘ from to

------------------------------------------------------------

CNat = ∀ N → (N → N) → N → N

cz : CNat
cz N s z = z

cs : CNat → CNat
cs n N s z = s (n _ s z)

postulate
  CNat' :
    ∀ N           (N' : N → Set)
      (s : N → N) (s' : (n : N) → N' n → N' (s n))
      z           (z' : N' z)
      (n : CNat)
    → N' (n N s z)

cnat : Nat
cnat = con CNat cz cs

open import Data.Product

init-cnat : Initial cnat
init-cnat =
  con
    (λ {(con N z s) → con (λ n → n N s z) (refl z) (λ n → refl (s (n N s z)))})
    (λ {(con N z s) f P pf → {!!}} )


open import Relation.Binary.PropositionalEquality

-- foo : ∀ N (s : N → N) z (n : CNat) → n N s z ≡ n CNat cs cz N s z
-- foo N s z n = {!CNat' N!}

-- foo : (n : CNat) → Eq CNat n (n CNat cs cz)
-- foo n P pn = CNat' CNat P cs {!!} cz {!!} n

-- CNat-ind : (P : CNat → Set)(cs' : ∀ n → P n → P (cs n)) → P cz → (n : CNat) → P n
-- CNat-ind P cs' cz' n = {!CNat' CNat P cs cs' cz cz' n!}

CNat-ind : (P : CNat → Set)(cs' : ∀ n → P n → P (cs n)) → P cz → (n : CNat) → P n
CNat-ind P cs' cz' n = {!CNat' CNat P cs cs' cz cz' n!}


Id = ∀ A → A → A

postulate Id' : ∀ (f : Id) A (A' : A → Set) a → A' a → A' (f A a)

postulate
  ext : ∀ {a b} → Extensionality a b


idid : ∀ (f : Id) → f ≡ (λ A x → x)
idid f = {!Id' f Id (_≡ (λ A x → x)) f!}
  -- ext λ A → ext λ a → Id' f A (_≡ a) a _≡_.refl


Sum = λ A B → ∀ S → (A → S) → (B → S) → S

postulate
  Sum' :
    ∀ A B (s : Sum A B) → ∀ S (S' : S → Set) l (l' : ∀ a → S' (l a)) r (r' : ∀ b → S' (r b))
    → S' (s S l r)

inj₁ : ∀ A B → A → Sum A B
inj₁ A B a _ l r = l a

inj₂ : ∀ A B → B → Sum A B
inj₂ A B b _ l r = r b

import Data.Sum as S

-- sum-unique : ∀ A B (s : Sum A B) → (∃ λ a → inj₁ _ _ a ≡ s) S.⊎ (∃ λ b → inj₂ _ _ b ≡ s)
-- sum-unique A B s = {!!}



-- postulate
--   peirce  : ∀ (A B : Set) → ((A → B) → A) → B
--   peirce' :
--     ∀ A (A' : A → Set)
--       B (B' : B → Set)
--       (f : (A → B) → A)(f' : (g : A → B)(g' : ∀ a (a' : A' a) → B' (g a)) → A' (f g))
--     → B' (peirce A B f)


-- bot : ⊥
-- bot = {!!}



      
      
-}




