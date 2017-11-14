

{-# OPTIONS --without-K #-}

open import Relation.Binary.PropositionalEquality

transp : {A : Set}(P : A → Set){x y : A} → x ≡ y → P x → P y
transp P refl x = x

transp₂ : {A : Set}{B : A → Set}(C : ∀ a (b : B a) → Set){x y : A}{b : B x}(p : x ≡ y)
          → C x b → C y (transp B p b)
transp₂ C refl x = x

contract : {A : Set}(P : A → Set){x y : A}(p : x ≡ y) → transp (x ≡_) p refl ≡ p
contract P refl = refl

J : {A : Set} {x : A} (P : (y : A) → x ≡ y → Set) → P _ refl → {y : A} → (w : x ≡ y) → P _ w
J P pr eq = transp (P _) (contract (λ _ → P _ refl) eq) (transp₂ P eq pr)


path-ext :
  (A : Set)(x y : A)(p q : x ≡ y)
  → ((P : ∀ y → x ≡ y → Set)(px : P x refl)(h : p ≡ q) → transp (P y) h (J P px p) ≡ J P px q) → p ≡ q
path-ext A x y p q h = {!!}

-- path-ext :
--   (A : Set)(x y : A)(p q : x ≡ y)
--   → ((P : A → Set)(px : P x) → transp P p px ≡ transp P q px) → p ≡ q
-- path-ext A x y p q h = {!!}





-- {-# OPTIONS --without-K #-}

-- open import Relation.Binary.PropositionalEquality
-- open import Data.Product
-- open import Data.Bool

-- postulate ext : ∀ {α β} → Extensionality α β

-- contr : Set → Set
-- contr A = Σ A λ a → ∀ a' → a ≡ a'

-- if' : ∀ {A : Set}(b : Bool) → (b ≡ true → A) → (b ≡ false → A) → A
-- if' {A} false t f = f refl
-- if' {A} true  t f = t refl

-- if'-true : ∀ {A} b t f (p : b ≡ true) → if' {A} b t f ≡ t p
-- if'-true false t f ()
-- if'-true true t f refl = refl

-- thm : ∀ A B (P : A → Bool) → contr (A → B) → contr ((Σ A λ a → P a ≡ true) → B)
-- thm A B P (f , fp) =
--   (λ w → f (proj₁ w)) ,
--   λ g → ext λ {(a , pa) →
--     trans
--       (cong (λ f → f a) (fp λ a → if' (P a) (λ pa → g (a , pa)) (λ _ → f a)))
--       (if'-true (P a) (λ pa → g (a , pa)) (λ _ →  f a) pa ) }
