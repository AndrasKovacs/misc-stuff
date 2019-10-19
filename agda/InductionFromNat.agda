

-- Library
--------------------------------------------------------------------------------

open import Agda.Primitive hiding (_⊔_)
open import Data.Empty
open import Data.Nat hiding (_<_; _^_)
open import Data.Product renaming (proj₁ to ₁; proj₂ to ₂)
open import Data.Sum
open import Data.Unit
open import Function
open import Relation.Binary.PropositionalEquality
open import Data.Nat.Properties

_◾_ = trans; infixr 4 _◾_
_⁻¹ = sym; infix 6 _⁻¹
ap  = cong
tr  = subst

J : ∀ {α β}{A : Set α} {x : A}
      (P : {y : A} → x ≡ y → Set β) → P refl → ∀ {y}(p : x ≡ y) → P p
J P pr refl = pr

hedberg :
  ∀ {α}{A : Set α}
  → ((x y : A) → (x ≡ y) ⊎ (x ≢ y))
  → ∀ {x y : A}(p q : x ≡ y) → p ≡ q
hedberg {_}{A} eq? {x}{y} p q =
  f-inv p ⁻¹ ◾ ap (_◾ f refl ⁻¹) (f-const p q) ◾ f-inv q
  where
    f : {x y : A} → x ≡ y → x ≡ y
    f {x}{y} p with eq? x y
    ... | inj₁ eq   = eq
    ... | inj₂ ¬eq  = ⊥-elim (¬eq p)

    f-const : ∀ {x y} p q → f {x}{y} p ≡ f q
    f-const {x}{y} p q  with eq? x y
    ... | inj₁ eq  = refl
    ... | inj₂ ¬eq = ⊥-elim (¬eq q)

    f-inv : ∀ {x y} p → (f {x}{y} p ◾ f refl ⁻¹) ≡ p
    f-inv refl = J (λ p → (p ◾ p ⁻¹) ≡ refl) refl (f refl)

-- data ABC (A B C : Set) : Set where
--   inᵃ : A → ABC A B C
--   inᵇ : B → ABC A B C
--   inᶜ : C → ABC A B C

-- infix 3 _<_
-- data _<_ : ℕ → ℕ → Set where  -- also definable by recursion on ℕ
--   here  : ∀ {n} → n < suc n
--   there : ∀ {n m} → n < m → n < suc m

-- <-trs : ∀ {n m k} → n < m → m < k → n < k
-- <-trs p here      = there p
-- <-trs p (there q) = there (<-trs p q)

-- pred< : ∀ {n m} → suc n < m → n < m
-- pred< here = there here
-- pred< (there p) = there (pred< p)

-- 0<s : ∀ n → 0 < suc n
-- 0<s zero    = here
-- 0<s (suc n) = there (0<s n)

-- s<s : ∀ {n m} → n < m → suc n < suc m
-- s<s here      = here
-- s<s (there p) = there (s<s p)

-- pred<pred : ∀ {n m} → suc n < suc m → n < m
-- pred<pred here = here
-- pred<pred {m = suc m} (there p) = there (pred<pred p)

-- <-irrefl : ∀ {n} → n < n → ⊥
-- <-irrefl {suc n} p = <-irrefl {n} (pred<pred p)

-- ℕ-set : ∀ {n : ℕ}(p : n ≡ n) → p ≡ refl
-- ℕ-set p = hedberg dec p refl
--   where
--     open import Relation.Nullary
--     dec : (x y : ℕ) → x ≡ y ⊎ x ≢ y
--     dec x y with Data.Nat._≟_ x y
--     dec x y | yes p = inj₁ p
--     dec x y | no ¬p = inj₂ ¬p

-- <-prop : ∀ {n m}(p q : n < m) → p ≡ q
-- <-prop p here = lem refl p where
--   lem : ∀ {n m}(e : n ≡ m) → (p : n < suc m) → p ≡ tr (λ x → n < suc x) e here
--   lem e here rewrite ℕ-set e = refl
--   lem refl (there p) = ⊥-elim (<-irrefl p)
-- <-prop here (there q) = ⊥-elim (<-irrefl q)
-- <-prop (there p) (there q) = ap there (<-prop p q)

-- cmp : ∀ n m → ABC (n < m) (m < n) (n ≡ m)
-- cmp zero zero = inᶜ refl
-- cmp zero (suc m) = inᵃ (0<s m)
-- cmp (suc n) zero = inᵇ (0<s n)
-- cmp (suc n) (suc m) with cmp n m
-- ... | inᵃ p = inᵃ (s<s p)
-- ... | inᵇ p = inᵇ (s<s p)
-- ... | inᶜ p = inᶜ (ap suc p)

-- cmp-refl : ∀ n → cmp n n ≡ inᶜ refl
-- cmp-refl zero = refl
-- cmp-refl (suc n) rewrite cmp-refl n = refl


-- -- Part 1
-- --------------------------------------------------------------------------------

-- module InductiveTypesFromBinaryTree where

--   data Tree : Set where
--     leaf : Tree
--     node : Tree → Tree → Tree

--   -- Ty, Con, Var are also constructible from Tree
--   infix 2 ι⇒_
--   data Ty : Set where     -- as linear trees
--     ι : Ty
--     ι⇒_ : Ty → Ty

--   infixl 3 _▶_
--   data Con : Set where    -- as lists (Ty-annotated linear tree)
--     ∙   : Con
--     _▶_ : Con → Ty → Con

--   data Var : Con → Ty → Set where   -- definable by recursion on Con
--     vz : ∀ {Γ A} → Var (Γ ▶ A) A
--     vs : ∀ {Γ A B} → Var Γ A → Var (Γ ▶ B) A

--   -- Terms. The intrinsic inductive definition would be the following:

--   -- data Tm n (Γ : Con n) : Ty → Set
--   -- data Sp n (Γ : Con n) : Ty → Ty → Set

--   -- data Sp n Γ where
--   --   []  : ∀ {A} → Sp n Γ A A
--   --   _∷_ : ∀ {A B} → Tm n Γ zero → Sp n Γ A B → Sp n Γ (suc A) B

--   -- data Tm n Γ where
--   --   ne : ∀ {A} → Var n Γ A → Sp n Γ A zero → Tm n Γ zero

--   -- well-formedness predicates
--   Tmw : Con → Ty → Tree → Set
--   Spw : Con → Ty → Ty → Tree → Set
--   Tmw Γ i t = ∃ λ A → Var Γ A × Spw Γ A ι t × i ≡ ι
--   Spw Γ A   B leaf        = A ≡ B
--   Spw Γ ι⇒A B (node t sp) = ∃ λ A → Tmw Γ ι t × Spw Γ A B sp × ι⇒A ≡ (ι⇒ A)

--   Tm : Con → Ty → Set
--   Tm Γ A = ∃ (Tmw Γ A)

--   Sp : Con → Ty → Ty → Set
--   Sp Γ A B = ∃ (Spw Γ A B)

--   [] : ∀ {Γ A} → Sp Γ A A
--   [] = leaf , refl

--   infixr 5 _∷_
--   _∷_ : ∀ {Γ A B} → Tm Γ ι → Sp Γ A B → Sp Γ (ι⇒ A) B
--   _∷_ (t , p) (sp , q) = node t sp , _ , p , q , refl

--   ne : ∀ {Γ A} → Var Γ A → Sp Γ A ι → Tm Γ ι
--   ne v (sp , p) = sp , _ , v , p , refl

--   -- Example: construction of natural numbers from Tm. This is possible for any
--   -- signature.
--   NatSig : Con
--   NatSig = ∙ ▶ ι ▶ (ι⇒ ι)  -- ∙ ▶ zero : Nat ▶ suc : Nat → Nat

--   Nat : Set
--   Nat = Tm NatSig ι

--   Zero : Nat
--   Zero = ne (vs vz) []

--   Suc : Nat → Nat
--   Suc n = ne vz (n ∷ [])

--   NatElim : ∀ {i}(P : Nat → Set i) → P Zero → (∀ n → P n → P (Suc n)) → ∀ n → P n
--   NatElim P z s (node t leaf , _ , vz , (_ , t* , refl , refl) , refl) =
--     s (t , t*) (NatElim P z s (t , t*))
--   NatElim P z s (node t (node _ _) , _ , vz , (_ , t* , (_ , _ , _ , ()) , refl) , refl)
--   NatElim P z s (leaf , _ , vs vz , refl , refl) = z
--   NatElim P z s (sp   , _ , vs (vs ()) , sp* , refl)


-- Part 2
--------------------------------------------------------------------------------

F : Set → Set
F X = ⊤ ⊎ (X × X)

Tree' : ℕ → Set
Tree' zero    = ⊥
Tree' (suc n) = ⊤ ⊎ Tree' n × Tree' n

depth : ∀ n → Tree' n → ℕ
depth (suc n) (inj₁ _)       = 1
depth (suc n) (inj₂ (l , r)) = depth n l ⊔ depth n r

-- lift : ∀ {n m} → Tree' n → Tree' (m ⊔ n)
-- lift {n} {zero}  t = t
-- lift {n} {suc m} t = {!t!}

Tree : Set
Tree = ∃₂ λ n (t : Tree' n) → depth n t ≡ n

leaf : Tree
leaf = 1 , inj₁ tt , refl

-- node : Tree → Tree → Tree
-- node (n , l , p) (m , r , q) = (n ⊔ m) ,
--   tr (λ n → Tree' n → ∃ (λ t → depth (n ⊔ m) t ≡ n ⊔ m))
--       p (λ l' → tr (λ m → Tree' m → ∃ (λ t → depth (depth n l ⊔ m) t ≡ depth n l ⊔ m)) q (λ r' → {!inj₂ (l ,!} , {!!}) r) l
  -- tr λ n → (l : Tree' n) → ∃ (λ t → depth (n ⊔ m) t ≡ n ⊔ m))
  --    p (λ l' → {!!}) l
