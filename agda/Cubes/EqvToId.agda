{-# OPTIONS --type-in-type --rewriting --without-K #-}

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
  -- ~~ : ∀ i → ~ (~ i) ↦ i
{-# REWRITE ₀∧ ∧₀ ₁∧ ∧₁ ₀∨ ∨₀ ₁∨ ∨₁ ~₀ ~₁ #-}

postulate
  path-η : ∀ (A : Set) (S T : A) (Q : S ≡ T) → ⟨ i ⟩ (Q $ i) ↦ Q
{-# REWRITE path-η #-}

infixr 5 _◾_
postulate
  _◾_        : {A : Set}{x y z : A} → x ≡ y → y ≡ z → x ≡ z
  coe        : {A B : Set} → A ≡ B → A → B
  regularity : (A : Set) (a : A) → coe (⟨ _ ⟩ A) a ↦ a
{-# REWRITE regularity #-}

------------------------------------------------------------------------

record Σ (A : Set) (B : A → Set) : Set where
  constructor _,_
  field
    proj₁ : A
    proj₂ : B proj₁
open Σ
infixr 5 _,_

_×_ : Set → Set → Set
A × B = Σ A λ _ → B
infixr 4 _×_

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

infix 6 _⁻¹
_⁻¹ : ∀ {A}{x y : A} → x ≡ y → y ≡ x
_⁻¹ p = ⟨ i ⟩ (p $ ~ i)

ap : ∀ {A B}(f : A → B){x y : A} → x ≡ y → f x ≡ f y
ap f p = ⟨ i ⟩ f (p $ i)

J : ∀ {A}{a : A}(P : ∀ a' → a ≡ a' → Set) → P a refl → ∀ {a'} (p : a ≡ a') → P a' p
J P refl* p = {!!} -- coe (⟨ i ⟩ P (p $ i) (⟨ j ⟩ (p $ i ∧ j))) refl*

tr : ∀ {A}(P : A → Set){x y : A}(p : x ≡ y) → P x → P y
tr P p = coe (ap P p)

------------------------------------------------------------

open import Data.Nat

postulate
  A     : Set
  left  : A
  right : A
  seg   : left ≡ right

  Aind :
    (Aᴹ : A → Set)(leftᴹ : Aᴹ left)(rightᴹ : Aᴹ right)
    (segᴹ : tr Aᴹ seg leftᴹ ≡ rightᴹ)
    → (a : A) → Aᴹ a

postulate
  leftβ :
    (Aᴹ : A → Set)(leftᴹ : Aᴹ left)(rightᴹ : Aᴹ right)
    (segᴹ : tr Aᴹ seg leftᴹ ≡ rightᴹ)
    → Aind Aᴹ leftᴹ rightᴹ segᴹ left ↦ leftᴹ
{-# REWRITE leftβ #-}

postulate
  rightβ :
    (Aᴹ : A → Set)(leftᴹ : Aᴹ left)(rightᴹ : Aᴹ right)
    (segᴹ : tr Aᴹ seg leftᴹ ≡ rightᴹ)
    → Aind Aᴹ leftᴹ rightᴹ segᴹ right ↦ rightᴹ
{-# REWRITE rightβ #-}

postulate
  segβ :
    (Aᴹ : A → Set)(leftᴹ : Aᴹ left)(rightᴹ : Aᴹ right)
    (segᴹ : tr Aᴹ seg leftᴹ ≡ rightᴹ) (i : I)
    → Aind Aᴹ leftᴹ rightᴹ segᴹ (seg $ i) ↦
      tr Aᴹ (⟨ j ⟩ (seg $ i ∨ ~ j)) (segᴹ $ i)
{-# REWRITE segβ #-}

postulate
  B    : A → Set
  con₁ : ℕ → B left
  con₂ : ℕ → ℕ → B right

  Brec : (Bᴹ : A → Set)
         (con₁ᴹ : ℕ → Bᴹ left)
         (con₂ᴹ : ℕ → ℕ → Bᴹ right)
         → ∀ a (b : B a) → Bᴹ a

  coeB₁ : ∀ (p : left  ≡ left) n → coe (⟨ i ⟩ B (p $ i)) (con₁ n) ↦ con₁ n
  coeB₂ : ∀ (p : right ≡ right) n m → coe (⟨ i ⟩ B (p $ i)) (con₂ n m) ↦ con₂ n m

  Brec-coe :
         (Bᴹ : A → Set)
         (con₁ᴹ : ℕ → Bᴹ left)
         (con₂ᴹ : ℕ → ℕ → Bᴹ right)
         (p : I → A)
         (b₀ : B (p ₀))
         → Brec Bᴹ con₁ᴹ con₂ᴹ (p ₁) (coe (⟨ i ⟩ B (p i)) b₀) ↦
           coe (⟨ i ⟩ Bᴹ (p i)) (Brec Bᴹ con₁ᴹ con₂ᴹ (p ₀) b₀)
         -- Question : what to do here?

         -- → Bind Bᴹ con₁ᴹ con₂ᴹ (p ₁) (coe (ap B (path p)) b₀) ↦
         --   coe {!!} (Bind Bᴹ con₁ᴹ con₂ᴹ (p ₀) b₀)

  -- Bind : (Bᴹ : ∀ a → B a → Set)
  --        (con₁ᴹ : ∀ n → Bᴹ left (con₁ n))
  --        (con₂ᴹ : ∀ n m → Bᴹ right (con₂ n m))
  --        → ∀ a (b : B a) → Bᴹ a b

  -- coeB₁ : ∀ (p : left  ≡ left) n → coe (⟨ i ⟩ B (p $ i)) (con₁ n) ↦ con₁ n
  -- coeB₂ : ∀ (p : right ≡ right) n m → coe (⟨ i ⟩ B (p $ i)) (con₂ n m) ↦ con₂ n m

  -- Bind-coe :
  --        (Bᴹ : ∀ a → B a → Set)
  --        (con₁ᴹ : ∀ n → Bᴹ left (con₁ n))
  --        (con₂ᴹ : ∀ n m → Bᴹ right (con₂ n m))
  --        (p : I → A)
  --        (b₀ : B (p ₀))
  --        → Bind Bᴹ con₁ᴹ con₂ᴹ (p ₁) (coe (ap B (path p)) b₀) ↦
  --          coe {!!} (Bind Bᴹ con₁ᴹ con₂ᴹ (p ₀) b₀)


-- Bᴹ    : A → Set
-- con₁ᴹ : Bᴹ left
-- con₂ᴹ : ℕ → Bᴹ right
-- f : B right → ℕ

-- infixr 5 _◾'_
-- _◾'_ : {A : Set}{x y z : A} → x ≡ y → y ≡ z → x ≡ z
-- _◾'_ {x = x} {y} {z} p q = tr (x ≡_) q p

-- ext : ∀ {A}{B : A → Set}{f g : ∀ a → B a} → (∀ a → f a ≡ g a) → f ≡ g
-- ext {f = f} {g} p = ⟨ i ⟩ (λ a → p a $ i)

-- apdₗ : ∀ {A : Set}{B : A → Set}(f : ∀ a → B a){x y : A}(p : x ≡ y) → tr B p (f x) ≡ f y
-- apdₗ {A} {B} f {x} {y} p = ⟨ i ⟩ coe (⟨ j ⟩ B (p $ i ∨ j)) (f (p $ i))

-- apdᵣ : ∀ {A : Set}{B : A → Set}(f : ∀ a → B a){x y : A}(p : x ≡ y) → f x ≡ tr B (p ⁻¹) (f y)
-- apdᵣ {A} {B} f {x} {y} p = ⟨ i ⟩ coe (⟨ j ⟩ B (p $ i ∧ ~ j)) (f (p $ i))

-- -- Equality from qinv
-- --------------------------------------------------------------------------------

-- qinv : {A B : Set} → (A → B) → Set
-- qinv {A}{B} f = Σ (B → A) λ g → (∀ x → f (g x) ≡ x) × (∀ x → g (f x) ≡ x)

-- postulate
--   iso : ∀ {A B} → Σ (A → B) qinv → A ≡ B

-- postulate
--   coe-iso : ∀ {A B}(a : A) (e : Σ _ (qinv {A}{B})) → coe (iso e) ↦ proj₁ e
--   iso$~i  :
--     ∀ {A B}(f : A → B)(g : B → A)(p : ∀ x → f (g x) ≡ x)(q : ∀ x → g (f x) ≡ x) i
--              →
--              (iso (f , g , p , q) $ ~ i) ↦ (iso (g , f , q , p) $ i)

--   -- What we consider canonical gets somewhat complicated in the
--   -- presence of higher constructors and iso. For a higher constructor
--   -- "c", "c" itself in the empty context is meaningful, and possibly
--   -- "c ◾ c" and transports over "c". So we necessarily have closed
--   -- unreduced J/transport/◾ expressions over higher constructors.

--   -- But! We don't want closed unreduced J/transport/◾ expressions
--   -- over iso.  In the absence of HIT's, the only closed equality
--   -- proofs should be refl and iso. The way we can use equalities is
--   -- ◾ and coe. Coe reduces on refl and iso. ◾ reduces on refl (see
--   -- rules a bit below), and on iso because of the rule just below.
--   ◾-iso :
--     ∀ {A B C}(f : A → B)(g : B → A)(p : ∀ x → f (g x) ≡ x)(q : ∀ x → g (f x) ≡ x)
--              (f' : B → C)(g' : C → B)(p' : ∀ x → f' (g' x) ≡ x)(q' : ∀ x → g' (f' x) ≡ x)
--     → (iso (f , g , p , q) ◾ iso (f' , g' , p' , q')) ↦
--        iso ((λ x → f' (f x)) , (λ x → g (g' x))
--             , (λ x → ap f' (p (g' x)) ◾ p' x)
--             , (λ x → ap g (q' (f x))  ◾ q x ))

--   iso-refl :
--     ∀ {A}
--     → iso {A}{A} ((λ x → x) , (λ x → x) , (λ x → refl) , λ x → refl) ↦ refl

-- {-# REWRITE coe-iso iso$~i iso-refl #-}

-- postulate
--   refl-◾ : (A : Set)(x y : A)(p : x ≡ y) → refl ◾ p ↦ p
--   ◾-refl : (A : Set)(x y : A)(p : x ≡ y) → p ◾ refl ↦ p

--   -- ◾-◾    : (A : Set)(a b c d : A)(p : a ≡ b)(q : b ≡ c)(r : c ≡ d)
--   --          → (p ◾ q) ◾ r ↦ p ◾ (q ◾ r)

--   coe-◾ : (A B C : Set)(p : A ≡ B)(q : B ≡ C) (a : A)
--            → coe (p ◾ q) a ↦ coe q (coe p a)
-- {-# REWRITE coe-◾ refl-◾ ◾-refl #-}

-- -- Univalence
-- ------------------------------------------------------------

-- -- bi-invertible eqivalence
-- eqv : {A B : Set} → (A → B) → Set
-- eqv {A}{B} f =
--   Σ (B → A) λ g → Σ (B → A) λ h → (∀ x → g (f x) ≡ x) × (∀ x → f (h x) ≡ x)

-- -- todo: copy from HoTT book (must be provable since we have J)
-- eqv-prop : ∀ {A B : Set} (f : A → B)(p q : eqv f) → p ≡ q
-- eqv-prop {A}{B} f (g , h , p , q) (g' , h' , p' , q') = {!!}

-- coe-inv : ∀ {A B}(p : A ≡ B) x → coe p (coe (p ⁻¹) x) ≡ x
-- coe-inv {A}{B} p x = ⟨ i ⟩ coe (⟨ j ⟩ (p $ (i ∨ j))) (coe (⟨ j ⟩ (p $ (i ∨ ~ j))) x)

-- coe-inv⁻¹ : ∀ {A B}(p : A ≡ B) x → coe (p ⁻¹) (coe p x) ≡ x
-- coe-inv⁻¹ {A}{B} p x = ⟨ i ⟩ coe (⟨ j ⟩ (p $ (~ i ∧ ~ j))) (coe (⟨ j ⟩ (p $ (~ i ∧ j))) x)

-- idToEqv : ∀ {A B} → A ≡ B → Σ _ (eqv {A}{B})
-- idToEqv {A}{B} p = coe p , coe (p ⁻¹) , coe (p ⁻¹) , coe-inv⁻¹ p , coe-inv p

-- eqvToId : ∀ {A B} → Σ _ (eqv {A}{B}) → A ≡ B
-- eqvToId (f , g , h , p , q) =
--   iso (f , g , (λ x → ap f (ap g (q x ⁻¹) ◾ p (h x)) ◾ q x) ,
--       (λ x → p x))

-- to : ∀ {A B} p → eqvToId (idToEqv {A}{B} p) ≡ p
-- to {A}{B} p = J (λ B p → eqvToId (idToEqv p) ≡ p) refl p

-- from :
--   ∀ {A B}
--     (f : A → B)(g h : B → A)(p : ∀ x → g (f x) ≡ x)(q : ∀ x → f (h x) ≡ x)
--   → idToEqv (eqvToId (f , g , h , p , q)) ≡ (f , g , h , p , q)
-- from {A}{B} f g h p q = ap (_,_ f) (eqv-prop f _ _)

-- univalence : ∀ {A B} → eqv (idToEqv {A}{B})
-- univalence {A}{B} = eqvToId , eqvToId , to , (λ {(f , g , h , p , q) → from f g h p q})

-- -- Tests
-- --------------------------------------------------------------------------------

-- open import Data.Bool using (Bool; true; false)
-- open import Data.Nat  using (ℕ; zero; suc)

-- negate≡ : Bool ≡ Bool
-- negate≡ = iso (
--   (λ {true → false; false → true}) ,
--   (λ {true → false; false → true}) ,
--   (λ {true → refl;  false → refl}) ,
--   (λ {true → refl;  false → refl})
--   )

-- A² : {A : Set} → (Bool → A) ≡ (A × A)
-- A² {A} = iso (
--   (λ f → f true , f false) ,
--   (λ {(a₁ , a₂) → λ {true → a₁; false → a₂}}) ,
--   (λ x → refl) ,
--   (λ f → ext λ {true → refl; false → refl})
--   )

-- foo = negate≡ ◾ negate≡
-- bar = coe foo true

-- swap : ∀ {A} → A × A → A × A
-- swap {A} = coe (A² ⁻¹ ◾ ap (λ x → x → A) negate≡ ◾ A²)

-- test1 : ∀ {A} → swap {A} ≡ (λ {(a₁ , a₂) → a₂ , a₁})
-- test1 = refl

-- postulate
--   S¹   : Set
--   base : S¹
--   loop : base ≡ base

-- postulate
--   S¹-ind :
--     (S¹ᴹ : S¹ → Set)
--     (baseᴹ : S¹ᴹ base)
--     (loopᴹ : coe (ap S¹ᴹ loop) baseᴹ ≡ baseᴹ)
--     → ∀ s → S¹ᴹ s
--   baseβ :
--     (S¹ᴹ   : S¹ → Set)
--     (baseᴹ : S¹ᴹ base)
--     (loopᴹ : coe (ap S¹ᴹ loop) baseᴹ ≡ baseᴹ)
--     → S¹-ind S¹ᴹ baseᴹ loopᴹ base ↦ baseᴹ
-- {-# REWRITE baseβ #-}
-- postulate
--   loopβ :
--     (S¹ᴹ   : S¹ → Set)
--     (baseᴹ : S¹ᴹ base)
--     (loopᴹ : tr S¹ᴹ loop baseᴹ ≡ baseᴹ)
--     (i : I)
--     → S¹-ind S¹ᴹ baseᴹ loopᴹ (loop $ i) ↦ coe {!!} (loopᴹ $ i)
-- -- {-# REWRITE loopβ #-}

-- -- We generally need a ◾ distribution and a coe computation rule for
-- -- each eliminator. Here we can skip coe computation because S¹ does
-- -- not have any visible coercible index or parameter.

-- -- The purpose of ◾ distribution is to allow β rules for higher
-- -- constructors to apply. In the "mobius"  example below, "coe (ap mobius (loop ◾ loop))"
-- -- only reduces if we distribute to "coe (ap mobius loop ◾ ap mobius loop)".
-- -- We could add ◾ distribution for functions in general, but ATM it does not
-- -- seem useful to me.

-- -- However, in full generality we need ◾ distribution rule for (p ◾
-- -- q) $ i $ j , (p ◾ q) $ i $ j $ k , and so on. It seems doable
-- -- though. For S¹ only the 1-dimensional case is needed since S¹ is a
-- -- groupoid and specifically there are no constructors higher than
-- -- "loop".

-- postulate
--   S¹-ind-◾ :
--     (S¹ᴹ : S¹ → Set)
--     (baseᴹ : S¹ᴹ base)
--     (loopᴹ : coe (ap S¹ᴹ loop) baseᴹ ≡ baseᴹ)
--     (s₁ s₂ s₃ : S¹)
--     (p : s₁ ≡ s₂)(q : s₂ ≡ s₃)
--     (i : I)
--     → S¹-ind S¹ᴹ baseᴹ loopᴹ ((p ◾ q) $ i) ↦
--       tr S¹ᴹ (⟨ j ⟩ (((⟨ k ⟩ (p $ ~ j ∨ k)) ◾ q) $ j ∧ i))
--              ((apdₗ (S¹-ind S¹ᴹ baseᴹ loopᴹ) p ◾ apdᵣ (S¹-ind S¹ᴹ baseᴹ loopᴹ) q) $ i)
-- {-# REWRITE S¹-ind-◾ #-}

-- data ⊥ : Set where

-- record ⊤ : Set where
--   constructor tt

-- mobius : S¹ → Set
-- mobius = S¹-ind (λ _ → Set) Bool negate≡

-- loopN  : ℕ → base ≡ base
-- loopN zero    = refl
-- loopN (suc n) = loop ◾ loopN n

-- flipN : ℕ → Bool → Bool
-- flipN n = tr mobius (loopN n)

-- flipN² : ℕ → (Bool × Bool) → (Bool × Bool)
-- flipN² n = tr (λ s → mobius s × mobius s) (loopN n)

-- -- test2 : flipN 3 true ≡ false
-- -- test2 = refl

-- -- if_then_else_ : {A : Set} → Bool → A → A → A
-- -- if false then t else f = t
-- -- if true  then t else f = f

-- -- loop≢refl : loop ≡ refl → ⊥
-- -- loop≢refl p = tr (λ q → if (tr mobius q true) then ⊤ else ⊥) p tt

-- -- -- -- foo : (s : S¹) → s ≡ s
-- -- -- -- foo = S¹-ind (λ s → s ≡ s) refl (⟨ i ⟩ ((⟨ j ⟩ (loop $ i ∨ ~ j)) ◾ (⟨ j ⟩ (loop $ i ∨ j))))


-- -- -- -- Integers
-- -- -- ------------------------------------------------------------

-- -- -- postulate
-- -- --   ℤ   : Set
-- -- --   zz  : ℤ
-- -- --   zs  : ℤ → ℤ
-- -- --   zp  : ℤ → ℤ
-- -- --   zsp : ∀ z → zs (zp z) ≡ z
-- -- --   zps : ∀ z → zp (zs z) ≡ z

-- -- --   ℤ-ind :
-- -- --     (ℤᴹ   : ℤ → Set)
-- -- --     (zzᴹ  : ℤᴹ zz)
-- -- --     (zsᴹ  : ∀ {z} → ℤᴹ z → ℤᴹ (zs z))
-- -- --     (zpᴹ  : ∀ {z} → ℤᴹ z → ℤᴹ (zp z))
-- -- --     (zspᴹ : ∀ {z}(zᴹ : ℤᴹ z) → tr ℤᴹ (zsp z) (zsᴹ (zpᴹ zᴹ)) ≡ zᴹ)
-- -- --     (zpsᴹ : ∀ {z}(zᴹ : ℤᴹ z) → tr ℤᴹ (zps z) (zpᴹ (zsᴹ zᴹ)) ≡ zᴹ)
-- -- --     (z : ℤ) → ℤᴹ z

-- -- --   zzβ :
-- -- --     (ℤᴹ   : ℤ → Set)
-- -- --     (zzᴹ  : ℤᴹ zz)
-- -- --     (zsᴹ  : ∀ {z} → ℤᴹ z → ℤᴹ (zs z))
-- -- --     (zpᴹ  : ∀ {z} → ℤᴹ z → ℤᴹ (zp z))
-- -- --     (zspᴹ : ∀ {z}(zᴹ : ℤᴹ z) → tr ℤᴹ (zsp z) (zsᴹ (zpᴹ zᴹ)) ≡ zᴹ)
-- -- --     (zpsᴹ : ∀ {z}(zᴹ : ℤᴹ z) → tr ℤᴹ (zps z) (zpᴹ (zsᴹ zᴹ)) ≡ zᴹ)
-- -- --     → ℤ-ind ℤᴹ zzᴹ zsᴹ zpᴹ zspᴹ zpsᴹ zz ↦ zzᴹ

-- -- --   zsβ :
-- -- --     (ℤᴹ   : ℤ → Set)
-- -- --     (zzᴹ  : ℤᴹ zz)
-- -- --     (zsᴹ  : ∀ {z} → ℤᴹ z → ℤᴹ (zs z))
-- -- --     (zpᴹ  : ∀ {z} → ℤᴹ z → ℤᴹ (zp z))
-- -- --     (zspᴹ : ∀ {z}(zᴹ : ℤᴹ z) → tr ℤᴹ (zsp z) (zsᴹ (zpᴹ zᴹ)) ≡ zᴹ)
-- -- --     (zpsᴹ : ∀ {z}(zᴹ : ℤᴹ z) → tr ℤᴹ (zps z) (zpᴹ (zsᴹ zᴹ)) ≡ zᴹ)
-- -- --     → ∀ z
-- -- --     → ℤ-ind ℤᴹ zzᴹ zsᴹ zpᴹ zspᴹ zpsᴹ (zs z) ↦ zsᴹ (ℤ-ind ℤᴹ zzᴹ zsᴹ zpᴹ zspᴹ zpsᴹ z)

-- -- --   zpβ :
-- -- --     (ℤᴹ   : ℤ → Set)
-- -- --     (zzᴹ  : ℤᴹ zz)
-- -- --     (zsᴹ  : ∀ {z} → ℤᴹ z → ℤᴹ (zs z))
-- -- --     (zpᴹ  : ∀ {z} → ℤᴹ z → ℤᴹ (zp z))
-- -- --     (zspᴹ : ∀ {z}(zᴹ : ℤᴹ z) → tr ℤᴹ (zsp z) (zsᴹ (zpᴹ zᴹ)) ≡ zᴹ)
-- -- --     (zpsᴹ : ∀ {z}(zᴹ : ℤᴹ z) → tr ℤᴹ (zps z) (zpᴹ (zsᴹ zᴹ)) ≡ zᴹ)
-- -- --     → ∀ z
-- -- --     → ℤ-ind ℤᴹ zzᴹ zsᴹ zpᴹ zspᴹ zpsᴹ (zp z) ↦ zpᴹ (ℤ-ind ℤᴹ zzᴹ zsᴹ zpᴹ zspᴹ zpsᴹ z)

-- -- -- {-# REWRITE zsβ zpβ #-}

-- -- -- -- todo
