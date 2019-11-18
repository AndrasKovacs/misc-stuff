
{-# OPTIONS --postfix-projections #-}

open import Agda.Builtin.FromNat
open import Data.Nat hiding (_⊔_; _<_; _≤_)
open import Data.Unit hiding (_≤_)
open import Data.Empty
open import Data.Product renaming (proj₁ to ₁; proj₂ to ₂)
open import Function
open import Data.Maybe
open import Data.Sum
open import Level renaming (zero to lzero; suc to lsuc)

instance
  Numberℕ : Number ℕ
  Numberℕ .Number.Constraint _ = ⊤
  Numberℕ .Number.fromNat    m = m

  NumberLevel : Number Level
  NumberLevel .Number.Constraint _    = ⊤
  NumberLevel .Number.fromNat zero    = lzero
  NumberLevel .Number.fromNat (suc m) = lsuc (fromNat m)

iterℕ : ∀{i}{A : Set i} → ℕ → (A → A) → A → A
iterℕ zero    f = id
iterℕ (suc n) f = f ∘ iterℕ n f

Fam : Set₁
Fam = Σ Set λ A → A → Set

-- ⊥ᶠ : Fam
-- ⊥ᶠ = ⊥ , λ ()

-- _⇒ᶠ_ : Fam → Fam → Set _; infixr 3 _⇒ᶠ_
-- F ⇒ᶠ G = Σ (F .₁ → G .₁) λ f → ∀ s → G .₂ (f s) → F .₂ s

-- Σᶠ : (A : Set) → (A → Fam) → Fam
-- Σᶠ A B = (Σ A λ a → B a .₁) , (λ ab → B (ab .₁) .₂ (ab .₂))

data UU (F : Fam) : Set where
  U' : F .₁ → UU F
  ⊤' : UU F
  ⊥' : UU F
  Π' : (A : F .₁) → (F .₂ A → UU F) → UU F

El : ∀ {F} → UU F → Set
El {F} (U' i)   = F .₂ i
El {F} ⊤'       = ⊤
El {F} ⊥'       = ⊥
El {F} (Π' A B) = (x : F .₂ A) → El (B x)

U  : ℕ → Set
U↓ : ℕ → Fam
U  n       = UU (U↓ n)
U↓ zero    = ⊥ , ⊥-elim
U↓ (suc n) = U n , El

-- ⇑ : ∀ {n} → U n → U (suc n)
-- ⇑ (U' x) = U' {!x!}
-- ⇑ ⊤' = {!!}
-- ⇑ ⊥' = {!!}
-- ⇑ (Π' A x) = {!!}

-- data T {i}(F : Fam i) : Set i where
--   zero : T F
--   suc  : T F → T F
--   lim  : ∀ s → (F .₂ s → T F) → T F
