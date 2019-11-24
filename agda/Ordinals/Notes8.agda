
{-# OPTIONS --postfix-projections #-}

open import Agda.Builtin.FromNat
open import Data.Nat
open import Data.Product renaming (proj₁ to ₁; proj₂ to ₂) hiding (∃)
open import Function
open import Data.Maybe
open import Level renaming (zero to lzero; suc to lsuc)
open import Relation.Binary.PropositionalEquality

record ⊤ {i} : Set i where
  instance constructor tt

data ⊥ {i} : Set i where

instance
  Numberℕ : Number ℕ
  Numberℕ .Number.Constraint _ = ⊤
  Numberℕ .Number.fromNat n    = n


iterℕ : ∀ {i}{A : Set i} → ℕ → (A → A) → A → A
iterℕ zero    f = id
iterℕ (suc n) f = f ∘ iterℕ n f

∃ : ∀ {i} j {A : Set i} → (A → Set j) → Set _
∃ i {A} B = Σ A B

--------------------------------------------------------------------------------

Fam : ∀ i → Set (lsuc i)
Fam i = Σ (Set i) λ A → A → Set i

_⇒ᶠ_ : ∀ {i j} → Fam i → Fam j  → Set _; infixr 3 _⇒ᶠ_
F ⇒ᶠ G = Σ (F .₁ → G .₁) λ f → ∀ s → G .₂ (f s) → F .₂ s

Σᶠ : ∀ {i} → (A : Set i) → (A → Fam i) → Fam _
Σᶠ A B = (Σ A λ a → B a .₁) , (λ ab → B (ab .₁) .₂ (ab .₂))

mkΣᶠ : ∀ {i}{A : Set i}{B : A → Fam i} → (a : A) → B a ⇒ᶠ Σᶠ A B
mkΣᶠ a = (λ b → a , b) , λ s p → p

data T {i}(F : Fam i) : Set i where
  zero : T F
  suc  : T F → T F
  lim  : (ℕ → T F) → T F
  Lim  : ∀ s → (F .₂ s → T F) → T F

instance
  NumberF : ∀ {i F} → Number (T {i} F)
  NumberF .Number.Constraint _    = ⊤
  NumberF .Number.fromNat zero    = zero
  NumberF .Number.fromNat (suc n) = suc (fromNat n)

  NumberLevel : Number Level
  NumberLevel .Number.Constraint _ = ⊤
  NumberLevel .Number.fromNat zero = lzero
  NumberLevel .Number.fromNat (suc n) = lsuc (fromNat n)

tmap : ∀ {i j}{F : Fam i}{G : Fam j} → F ⇒ᶠ G → T F → T G
tmap (f , g) zero      = zero
tmap (f , g) (suc a)   = suc (tmap (f , g) a)
tmap (f , g) (lim a)   = lim (λ n → tmap (f , g) (a n))
tmap (f , g) (Lim s a) = Lim (f s) (λ p → tmap (f , g) (a (g s p)))

∃suc : ∀ {i} → ∃ i T → ∃ i T
∃suc (_ , a) = _ , suc a

-- ∃lim : ∀{i} → (ℕ → ∃ i T) → ∃ i T
-- ∃lim a = Σᶠ (Lift _ ℕ) (λ n → a (lower n) .₁)
--       , lim (λ n → tmap (mkΣᶠ (lift n)) (a n .₂))

-- ∃Lim : ∀ {i}{F : Fam i} s → (F .₂ s → ∃ i T) → ∃ i T
-- ∃Lim {_}{F} s a =
--     ( Maybe (Σ (F .₂ s) (λ p → a p .₁ .₁))
--     , maybe (λ xp → a (xp .₁) .₁ .₂ (xp .₂)) (F .₂ s))
--   , Lim nothing λ p → tmap ((λ x → just (p , x)) , λ _ p → p) (a p .₂)

instance
  Number∃T : ∀ {i} → Number (∃ i T)
  Number∃T .Number.Constraint _    = ⊤
  Number∃T .Number.fromNat zero    = (⊥ , λ ()) , 0
  Number∃T .Number.fromNat (suc n) = ∃suc (fromNat n)

-- Branching type of next admissible ordinal
ωᶠ+ : ∀ {i} → Fam i → Fam i
ωᶠ+ (S , P) = Maybe S , maybe P (T (S , P))

ωᶠ : ∀ {i} → ∃ i T → Fam i
ωᶠ (F , zero)    = ⊥ , λ ()
ωᶠ (F , suc a)   = ωᶠ+ (ωᶠ (F , a))
ωᶠ (F , lim a)   = Σᶠ (Lift _ ℕ) λ n → ωᶠ (F , a (lower n))
ωᶠ (F , Lim s a) = Σᶠ (F .₂ s) λ p → ωᶠ (F , a p)

-- enumeration of admissibles
ω : ∀ {i} → ∃ i T → ∃ i T
ω a = ωᶠ+ (ωᶠ a) , Lim nothing (tmap (just , (λ s p → p)))

-- inaccessible ordinals
κ : ∀ i → ∃ (lsuc i) T
κ i = ((Maybe (Σ (Fam i) λ F → F .₁)) , maybe (λ fs → Lift _ (fs .₁ .₂ (fs .₂))) (∃ i T))
    , Lim nothing λ a → tmap ((λ x → just (a .₁ , x)) , λ _ → lower) (a .₂)
