
-- Univalence implies function extensionality, based on
-- https://homotopytypetheory.org/2014/02/17/another-proof-that-univalence-implies-function-extensionality/

{-# OPTIONS --without-K #-}

open import Relation.Binary.PropositionalEquality
open import Data.Product
open import Function
open import Level

_~_ : ∀ {α β} → Set α → Set β → Set (α ⊔ β)
A ~ B = ∃ λ (p : (B → A) × (A → B)) → let (f , g) = p in (∀ a → f (g a) ≡ a) × (∀ b → g (f b) ≡ b)

~sym : ∀ {α β}{A : Set α}{B : Set β} → A ~ B → B ~ A
~sym ((f , g) , fg , gf) = (g , f) , gf , fg

~trans : ∀ {α β γ}{A : Set α}{B : Set β}{C : Set γ} → A ~ B → B ~ C → A ~ C
~trans ((f , g) , fg , gf) ((f' , g') , fg' , gf') =
  (f ∘ f' ,
  g' ∘ g ) ,
  (λ a → trans (cong f (fg' (g a))) (fg a)) ,
  (λ b → trans (cong g' (gf (f' b))) (gf' b))

coe : ∀ {α}{A B : Set α} → A ≡ B → A → B
coe = subst id

coe-inv-r : ∀ {α}{A B : Set α} p a → coe {α}{A}{B} (sym p) (coe p a) ≡ a
coe-inv-r refl a = refl

coe-inv-l : ∀ {α}{A B : Set α} p a → coe {α}{A}{B} p (coe (sym p) a) ≡ a
coe-inv-l refl a = refl

idtoeqv : ∀ {α} {A B : Set α} → A ≡ B → A ~ B
idtoeqv p = (coe (sym p) , coe p) , coe-inv-r p , coe-inv-l p

⟶ : ∀ {α β A B} → _~_ {α}{β} A B → (A → B)
⟶ = proj₂ ∘ proj₁

⟵ : ∀ {α β A B} → _~_ {α}{β} A B → (B → A)
⟵ = proj₁ ∘ proj₁

backwards-preserves₁ :
  ∀ {α β γ}{A : Set α}{B : A → Set β}{B' : A → Set γ}
  → (eq : Σ A B ~ Σ A B')
  → (∀ p → proj₁ (⟶ eq p) ≡ proj₁ p)
  → (∀ p → proj₁ (⟵ eq p) ≡ proj₁ p)
backwards-preserves₁ ((f , _) , _ , gf) preserves₁ p
  = sym (trans (cong proj₁ (sym (gf p))) (preserves₁ (f p)))

Paths : ∀ {α} → Set α → Set α
Paths A = ∃ λ (p : A × A) → proj₁ p ≡ proj₂ p

Homotopies : ∀ {α β} → Set α → Set β → Set (α ⊔ β)
Homotopies A B = ∃ λ (p : (A → B) × (A → B)) → ∀ a → proj₁ p a ≡ proj₂ p a

contract : ∀ {α} (A : Set α) → Paths A ~ A
contract A = ((λ a → (a , a) , refl) , proj₁ ∘ proj₁) , (λ {((_ , _) , refl) → refl}) , (λ _ → refl)

postulate
  ua   : ∀ {α}{A B : Set α} → A ~ B → A ≡ B
  ua-β : ∀ {α A B} eqv      → idtoeqv {α}{A}{B} (ua eqv) ≡ eqv
  ua-η : ∀ {α A B} p        → ua (idtoeqv {α}{A}{B} p)   ≡ p

J :
  ∀ {α β}{A : Set α}(C : {x y : A} → x ≡ y → Set β)
  → (∀ {a} → C {a} refl) → ∀ {a a'} p → C {a}{a'} p
J C refl* refl = refl*

coe-∘ :
  ∀ {α β}{A : Set α}{B B' : Set β} (eqv : B ~ B')
  → coe (cong (λ x → A → x) (ua eqv)) ≡ (⟶ eqv ∘_)
coe-∘ {A = A} eqv =
  trans
    (J (λ p → coe (cong (λ x → A → x) p) ≡ (coe p ∘_)) refl (ua eqv))
    (cong (λ x → ⟶ x ∘_) (ua-β eqv))

Σ-lem :
  ∀ {α β}{A : Set α}{B : A → Set β} (p : Σ A B)(a : A)
  → (eq : proj₁ p ≡ a) → B a
Σ-lem p .(proj₁ p) refl = proj₂ p

module _ {α β}{A : Set α}{B : Set β} where

  eq1 : Paths (A → B) ~ (A → B)
  eq1 = contract (A → B)

  eq2 : (A → B) ~ (A → Paths B)
  eq2 = idtoeqv (cong (λ x → A → x) (ua (~sym (contract B))))

  eq3 : (A → Paths B) ~ Homotopies A B
  eq3 =
    ((λ {((f , g) , p) a → (f a , g a) , p a}) ,
    (λ f → (proj₁ ∘ proj₁ ∘ f , proj₂ ∘ proj₁ ∘ f) , proj₂ ∘ f)) ,
    (λ f → refl) ,
    (λ b → refl)

  eq4 :  Paths (A → B) ~ Homotopies A B
  eq4 = ~trans eq1 (~trans eq2 eq3)

  eq4-preserves₁ : ∀ p → proj₁ (⟶ eq4 p) ≡ proj₁ p
  eq4-preserves₁ ((f , .f) , refl) 
    rewrite
      coe-∘ {A = A} (~sym (contract (A → B)))
    | coe-∘ {A = A} (~sym (contract B))
    = refl

  funext : ∀ {f g : A → B} → (∀ a → f a ≡ g a) → f ≡ g
  funext {f}{g} p =
    Σ-lem (⟵ eq4 ((f , g) , p)) (f , g) (backwards-preserves₁ eq4 eq4-preserves₁ _)
  
