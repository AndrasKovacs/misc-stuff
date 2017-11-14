
{-# OPTIONS --type-in-type --rewriting #-}

postulate _↦_ : {A : Set} → A → A → Set
{-# BUILTIN REWRITE _↦_ #-}
infix 3 _↦_

postulate
  I : Set
  ₀ ₁ : I
  ~ : I → I
  _∧_ _∨_ : I → I → I

infix 3 _≡_
data _≡_ {A : Set} : A → A → Set where
  path : (f : I → A) → f ₀ ≡ f ₁

syntax path (λ i → t) = ⟨ i ⟩ t

_$_ : ∀ {A}{x y : A} → x ≡ y → I → A
path f $ i = f i
infixl 8 _$_

{-# DISPLAY path f = f #-}

refl : ∀ {A}{a : A} → a ≡ a
refl {_}{a} = ⟨ _ ⟩ a

postulate
  $-₀ : ∀ {A}{x y : A}(p : x ≡ y) → p $ ₀ ↦ x
  $-₁ : ∀ {A}{x y : A}(p : x ≡ y) → p $ ₁ ↦ y
{-# REWRITE $-₀ $-₁ #-}

postulate
  ₀∧ : ∀ i → ₀ ∧ i ↦ ₀
  ∧₀ : ∀ i → i ∧ ₀ ↦ ₀
  ₁∧ : ∀ i → ₁ ∧ i ↦ i
  ∧₁ : ∀ i → i ∧ ₁ ↦ i
  ₀∨ : ∀ i → ₀ ∨ i ↦ i
  ∨₀ : ∀ i → i ∨ ₀ ↦ i
  ₁∨ : ∀ i → ₁ ∨ i ↦ ₁
  ∨₁ : ∀ i → i ∨ ₁ ↦ ₁
  ~₀ : ~ ₀ ↦ ₁
  ~₁ : ~ ₁ ↦ ₀
{-# REWRITE ₀∧ ∧₀ ₁∧ ∧₁ ₀∨ ∨₀ ₁∨ ∨₁ ~₀ ~₁ #-}

postulate
  path-η : ∀ (A : Set) (S T : A) (Q : S ≡ T) → ⟨ i ⟩ (Q $ i) ↦ Q
{-# REWRITE path-η #-}

record Σ (A : Set) (B : A → Set) : Set where
  constructor _,_
  field
    proj₁ : A
    proj₂ : B proj₁
open Σ
infixr 5 _,_

infixr 5 _◾_
postulate
  _◾_        : {A : Set}{x y z : A} → x ≡ y → y ≡ z → x ≡ z
  coe        : {A B : Set} → A ≡ B → A → B
  regularity : (A : Set) (a : A) → coe (⟨ _ ⟩ A) a ↦ a
{-# REWRITE regularity #-}

postulate
  coe-Π :
    (A : I → Set)(B : (i : I) → A i → Set)(f : (a : A ₀) → B ₀ a)
    → coe (⟨ i ⟩ ((a : A i) → B i a)) f
    ↦ (λ a₁ → coe (⟨ i ⟩ B i (coe (⟨ j ⟩ A (i ∨ (~ j))) a₁)) (f (coe (⟨ i ⟩ A (~ i)) a₁)))

  coe-Σ :
    (A : I → Set)(B : ∀ i → A i → Set)(p : Σ (A ₀) (B ₀))
    → coe (⟨ i ⟩ (Σ (A i) (B i))) p
    ↦ ((coe (path A) (proj₁ p)) ,
       coe (⟨ i ⟩ B i (coe (⟨ j ⟩ A (i ∧ j)) (proj₁ p))) (proj₂ p))

  coe-≡ :
      (A : I → Set)(x y : ∀ i → A i)(p : x ₀ ≡ y ₀)
    → coe (⟨ i ⟩ (_≡_ {A i} (x i) (y i))) p ↦
       ⟨ i ⟩ coe (⟨ j ⟩ (A (~ i ∨ j))) (x (~ i))
     ◾ ⟨ i ⟩ coe (path A) (p $ i)
     ◾ ⟨ i ⟩ coe (⟨ j ⟩ (A (i ∨ j))) (y i)

{-# REWRITE coe-Π coe-Σ coe-≡ #-}

J : ∀ {A}{a : A}(P : ∀ a' → a ≡ a' → Set) → P a refl → ∀ {a'} (p : a ≡ a') → P a' p
J P refl* p = coe (⟨ i ⟩ P (p $ i) (⟨ j ⟩ (p $ i ∧ j))) refl*

ext : ∀ {A}{B : A → Set}{f g : ∀ a → B a} → (∀ a → f a ≡ g a) → f ≡ g
ext {f = f} {g} p = ⟨ i ⟩ (λ a → p a $ i)

infix 6 _⁻¹
_⁻¹ : ∀ {A}{x y : A} → x ≡ y → y ≡ x
_⁻¹ p = ⟨ i ⟩ (p $ ~ i)

ap : ∀ {A B}(f : A → B){x y : A} → x ≡ y → f x ≡ f y
ap f p = ⟨ i ⟩ f (p $ i)

_×_ : Set → Set → Set
A × B = Σ A λ _ → B
infixr 4 _×_

-- Equality from quasi-inverses
--------------------------------------------------------------------------------

qinv : {A B : Set} → (A → B) → Set
qinv {A}{B} f = Σ (B → A) λ g → (∀ x → f (g x) ≡ x) × (∀ x → g (f x) ≡ x)

postulate
  iso : ∀ {A B} → Σ (A → B) qinv → A ≡ B
  coe-iso : ∀ {A B}(a : A) (e : Σ _ (qinv {A}{B})) → coe (iso e) ↦ proj₁ e
  iso$~i  :
    ∀ {A B}(f : A → B)(g : B → A)(p : ∀ x → f (g x) ≡ x)(q : ∀ x → g (f x) ≡ x) i
             →
             (iso (f , g , p , q) $ ~ i) ↦ (iso (g , f , q , p) $ i)

  iso-regularity :
    ∀ {A}
    → iso {A}{A} ((λ x → x) , (λ x → x) , (λ x → refl) , λ x → refl) ↦ refl

{-# REWRITE coe-iso iso$~i iso-regularity #-}

postulate
  refl-◾ : (A : Set)(x y : A)(p : x ≡ y) → refl ◾ p ↦ p
  coe-◾ : (A B C : Set)(p : A ≡ B)(q : B ≡ C) (a : A)
           → coe (p ◾ q) a ↦ coe q (coe p a)
{-# REWRITE refl-◾ coe-◾ #-}

-- Univalence
------------------------------------------------------------

eqv : {A B : Set} → (A → B) → Set
eqv {A}{B} f =
  Σ (B → A) λ g → Σ (B → A) λ h → (∀ x → g (f x) ≡ x) × (∀ x → f (h x) ≡ x)

eqv-prop : ∀ {A B : Set} (f : A → B)(p q : eqv f) → p ≡ q
eqv-prop {A}{B} f (g , h , p , q) (g' , h' , p' , q') = {!!}

coe-inv : ∀ {A B}(p : A ≡ B) x → coe p (coe (p ⁻¹) x) ≡ x
coe-inv {A}{B} p x = ⟨ i ⟩ coe (⟨ j ⟩ (p $ (i ∨ j))) (coe (⟨ j ⟩ (p $ (i ∨ ~ j))) x)

coe-inv⁻¹ : ∀ {A B}(p : A ≡ B) x → coe (p ⁻¹) (coe p x) ≡ x
coe-inv⁻¹ {A}{B} p x = ⟨ i ⟩ coe (⟨ j ⟩ (p $ (~ i ∧ ~ j))) (coe (⟨ j ⟩ (p $ (~ i ∧ j))) x)

idToEqv : ∀ {A B} → A ≡ B → Σ _ (eqv {A}{B})
idToEqv {A}{B} p = coe p , coe (p ⁻¹) , coe (p ⁻¹) , coe-inv⁻¹ p , coe-inv p

eqvToId : ∀ {A B} → Σ _ (eqv {A}{B}) → A ≡ B
eqvToId (f , g , h , p , q) =
  iso (f , g , (λ x → ap f (ap g (q x ⁻¹) ◾ p (h x)) ◾ q x) ,
      (λ x → p x))

to : ∀ {A B} p → eqvToId (idToEqv {A}{B} p) ≡ p
to {A}{B} p = J (λ B p → eqvToId (idToEqv p) ≡ p) refl p

from :
  ∀ {A B}
    (f : A → B)(g h : B → A)(p : ∀ x → g (f x) ≡ x)(q : ∀ x → f (h x) ≡ x)
  → idToEqv (eqvToId (f , g , h , p , q)) ≡ (f , g , h , p , q)
from {A}{B} f g h p q = ap (_,_ f) (eqv-prop f _ _)

univalence : ∀ {A B} → eqv (idToEqv {A}{B})
univalence {A}{B} = eqvToId , eqvToId , to , (λ {(f , g , h , p , q) → from f g h p q})
