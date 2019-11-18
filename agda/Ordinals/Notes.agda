{-# OPTIONS --postfix-projections --cubical #-}

open import Agda.Builtin.FromNat
open import Data.Nat hiding (_⊔_; _<_)
open import Data.Unit
open import Data.Empty
open import Function
open import Data.Sum
open import Level renaming (suc to lsuc; zero to lzero)
-- open import Relation.Binary.PropositionalEquality using (refl; _≡_)
-- import Relation.Binary.PropositionalEquality as Eq

open import Data.Product renaming (proj₁ to ₁; proj₂ to ₂)
open import Cubical.Core.Everything
import Cubical.Foundations.Prelude as P

instance
  Numberℕ : Number ℕ
  Numberℕ .Number.Constraint _ = ⊤
  Numberℕ .Number.fromNat    m = m

resolve : ∀ {i}{A : Set i}{{ _ : A}} → A
resolve {{a}} = a

tr  = P.subst;               {-# DISPLAY P.subst = tr  #-}
ap  = P.cong;                {-# DISPLAY P.cong  = ap  #-}
_⁻¹ = P.sym;   infix 6 _⁻¹;  {-# DISPLAY P.sym   = _⁻¹ #-}
_◾_ = P._∙_; infixr 5 _◾_;   {-# DISPLAY P._∙_   = _◾_ #-}

coe : ∀ {i}{A B : Set i} → A ≡ B → A → B
coe = tr id


data Acc {i j}{A : Set i}(R : A → A → Set j)(a : A) : Set (i ⊔ j) where
  acc : (∀ b → R b a → Acc R b) → Acc R a

Wf : ∀ {i j}{A : Set i}(R : A → A → Set j) → Set _
Wf R = ∀ {a} → Acc R a

AccProp : ∀ {i j A R a}(p q : Acc {i}{j}{A} R a) → p ≡ q
AccProp (acc f) (acc g) ᵢ = acc λ a p → AccProp (f a p) (g a p) ᵢ

record TTO (i : Level) : Set (lsuc i) where
  infix 3 _<_
  field
    !           : Set i
    _<_         : ! → ! → Set i
    instance wf : Wf _<_
    trans       : ∀ {x y z} → x < y → y < z → x < z
    zero!       : !
    zero!<      : ∀ j → (zero! < j) ⊎ (zero! ≡ j)

  <-irrefl : ∀ {i} → i < i → ⊥
  <-irrefl p = go wf p where
    go : ∀ {i} → Acc _<_ i → i < i → ⊥
    go (acc f) p = go (f _ p) p

module Omega (α : TTO lzero) where
  open TTO α
  data Ω' (i : !)(El : ∀ j → j < i → Set) : Set where
    zero : Ω' i El
    suc  : Ω' i El → Ω' i El
    lim  : ∀ j p → (El j p → Ω' i El) → Ω' i El

  El : ∀ i (_ : Acc _<_ i) j → j < i → Set
  El i (acc f) j p = Ω' j λ k q → El j (f j p) _ q

  Ω : ! → Set
  Ω i = Ω' i (λ j p → El i wf _ p)

  El≡ : ∀ {i}{a : Acc _<_ i}{j p} → El i a j p ≡ Ω j
  El≡ {i} {acc f}{j}{p} ᵢ = Ω' j (λ k → El j (AccProp (f j p) wf ᵢ) k)

  ⇑ : ∀ {i j} → i < j → Ω i → Ω j
  ⇑ p zero        = zero
  ⇑ p (suc a)     = suc (⇑ p a)
  ⇑ p (lim j q a) = lim j (trans q p) λ b → ⇑ p (a (coe (El≡ ◾ El≡ ⁻¹) b ))

  iterΩ : ∀ {i} → Ω i → (Ω i → Ω i) → Ω i → Ω i
  iterΩ zero        f = id
  iterΩ (suc a)     f = f ∘ iterΩ a f
  iterΩ (lim j p a) f = λ b → lim j p λ i → iterΩ (a i) f b

  lfp : ∀ {i} → (Ω i → Ω i) → Ω i
  lfp {i} f = lim zero! {!zero!< i !} {!!}

  F : ∀ {i j} → i < j →  Ω j → Ω i → Ω i
  F p zero b = suc b
  F p (suc a) b = iterΩ b (F p a) b
  F p (lim k q a) b = {!F ?!}    -- comparison!

  -- φ : ∀ {i j} → i < j → Ω j → Ω i
  -- φ p zero        = zero
  -- φ p (suc a)     = suc (φ p a)
  -- φ p (lim k q a) = lfp {!a!}


-- -- generalized fast-growing hierarchy
-- F : ∀ {i} → Ω (suc i) → Ω i → Ω i
-- F zero              b = suc b
-- F (suc a)           b = iterΩ b (F a) b
-- F (lim j here a)    b = F (a b) b
-- F (lim j (suc p) a) b = lim j p λ i → F (a i) b

-- iterΩ zero        f = id
-- iterΩ (suc a)     f = f ∘ iterΩ a f
-- iterΩ (lim j p a) f = λ b → lim j p λ i → iterΩ (a i) f b













-- ------------------------------------------------------------
-- -- Omega function on small type-theoretic ordinals
-- -- i.e. Omega 0 ≈ ω₀ ≈ ℕ
-- --      Omega 1 ≈ ω₁
-- --      etc.
-- ------------------------------------------------------------

-- !↓ : ∀ {ℓ}(α : TTO ℓ) → TTO.! α → Set ℓ
-- !↓ α i = Σ (TTO.! α) λ j → TTO._<_ α j i

-- <↓ : ∀ {ℓ}(α : TTO ℓ) i → !↓ α i → !↓ α i → Set ℓ
-- <↓ α i (j , p) (k , q) = TTO._<_ α j k

-- wf↓' : ∀{ℓ}(α : TTO ℓ) i j → Acc (TTO._<_ α) (j .₁)  → Acc (<↓ α i) j
-- wf↓' α i j (acc f) = acc (λ k p → wf↓' α i k (f (k .₁) p))

-- wf↓ : ∀ {ℓ}(α : TTO ℓ) i → Wf (<↓ α i)
-- wf↓ α i = acc (λ j p → wf↓' α i j (TTO.wf α))

-- trans↓ : ∀ {ℓ}(α : TTO ℓ) i {x y z} → <↓ α i x y → <↓ α i y z → <↓ α i x z
-- trans↓ α i {x , _} {y , _} {z , _} p q = TTO.trans α p q

-- Ord↓ : ∀ {ℓ}(α : TTO ℓ) → TTO.! α → TTO ℓ
-- Ord↓ α i = record {
--     !     = !↓ α i
--   ; _<_   = <↓ α i
--   ; wf    = wf↓ α i
--   ; trans = λ {x}{y}{z} → trans↓ α i {x}{y}{z}
--   }

-- data Omega' (α : TTO 0)(El : TTO.! α → Set 0) : Set 0 where
--   zero : Omega' α El
--   suc  : Omega' α El → Omega' α El
--   lim  : ∀ {j : TTO.! α} → (El j → Omega' α El) → Omega' α El

-- postulate
--   cheat : ∀{i}{A : Set i} → A

-- {-# TERMINATING #-} -- need: well-foundedness of Ord↓
-- El↓ : ∀ (α : TTO 0)(i : TTO.! α) → Set 0
-- El↓ α i = Omega' (Ord↓ α i) (El↓ (Ord↓ α i))

-- Omega : TTO 0 → Set 0
-- Omega α = Omega' α (El↓ α)

  -- El↓ : ∀ {i}{{ _ : Acc _<_ i}} j → j < i → Set 0
  -- El↓ {{acc f}} j p = Omega' j (El↓ {{f j p}})

  -- El : ! → Set
  -- El i = Omega' i (El↓ {i})

  -- El↓β : ∀ {i a j p} → El↓ {i}{{a}} j p → El j
  -- El↓β {i} {acc f} {j} {p} x = {!x!}

  -- data Omega' (i : !)(El : ∀ j → j < i → Set 0) : Set 0 where
  --   zero : Omega' i El
  --   suc  : Omega' i El → Omega' i El
  --   lim  : ∀ {j : !} p → (El j p → Omega' i El) → Omega' i El

  -- El↓ : ∀ {i}{{ _ : Acc _<_ i}} j → j < i → Set 0
  -- El↓ {{acc f}} j p = Omega' j (El↓ {{f j p}})

  -- El : ! → Set
  -- El i = Omega' i (El↓ {i})

  -- El↓β : ∀ {i a j p} → El↓ {i}{{a}} j p → El j
  -- El↓β {i} {acc f} {j} {p} x = {!x!}

-- ω : TTO 0 0 → TTO 0 0
-- ω ord = {!!}
