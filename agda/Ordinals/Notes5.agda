{-# OPTIONS --postfix-projections #-}

open import Agda.Builtin.FromNat
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit hiding (_≤_)
open import Data.Empty
open import Data.Product renaming (proj₁ to ₁; proj₂ to ₂)
open import Function
open import Data.Maybe
open import Level renaming (zero to lzero; suc to lsuc)
open import Relation.Binary.PropositionalEquality

instance
  NumberLevel : Number Level
  NumberLevel .Number.Constraint _    = ⊤
  NumberLevel .Number.fromNat zero    = lzero
  NumberLevel .Number.fromNat (suc m) = lsuc (fromNat m)

--------------------------------------------------------------------------------

Fam : Set₁
Fam = Σ Set λ A → A → Set

0ᶠ : Fam
0ᶠ = ⊥ , λ ()

_⇒ᶠ_ : Fam → Fam  → Set _; infixr 3 _⇒ᶠ_
F ⇒ᶠ G = Σ (F .₁ → G .₁) λ f → ∀ s → G .₂ (f s) → F .₂ s

Σᶠ : (A : Set) → (A → Fam) → Fam
Σᶠ A B = (Σ A λ a → B a .₁) , (λ ab → B (ab .₁) .₂ (ab .₂))

mkΣᶠ : ∀ {A : Set}{B : A → Fam} → (a : A) → B a ⇒ᶠ Σᶠ A B
mkΣᶠ a = (λ b → a , b) , λ s p → p

data T (F : Fam) : Set where
  zero : T F
  suc  : T F → T F
  lim  : ∀ s → (F .₂ s → T F) → T F

instance
  liftInst : ∀ {i j}{A : Set i}{{a : A}} → Lift j A
  liftInst {{a}} = lift a

  NumberF : ∀ {F} → Number (T F)
  NumberF .Number.Constraint _    = ⊤
  NumberF .Number.fromNat zero    = zero
  NumberF .Number.fromNat (suc n) = suc (fromNat n)

_+_ : ∀ {F} → T F → T F → T F; infixl 6 _+_
a + zero    = a
a + suc b   = suc (a + b)
a + lim s b = lim s λ i → a + b i

_*_ : ∀ {F} → T F → T F → T F; infixl 7 _*_
a * zero    = 0
a * suc b   = a * b + a
a * lim s b = lim s λ i → a * b i

exp : ∀ {F} → T F → T F → T F
exp a zero      = 1
exp a (suc b)   = exp a b * a
exp a (lim s b) = lim s λ i → exp a (b i)

tmap : ∀ {F G} → F ⇒ᶠ G → T F → T G
tmap (f , g) zero      = zero
tmap (f , g) (suc a)   = suc (tmap (f , g) a)
tmap (f , g) (lim s a) = lim (f s) (λ p → tmap (f , g) (a (g s p)))

T+ : Fam → Fam
T+ (S , P) = Maybe S , maybe P (T (S , P))

ω : ∀ {F} → T (T+ F)
ω = lim nothing (tmap (just , (λ s p → p)))

-- countable limit support
--------------------------------------------------------------------------------

has-limℕ : Fam → Set₁
has-limℕ (S , P) = ∃ λ s → P s ≡ T 0ᶠ

ω₁≤ : Set₁
ω₁≤ = ∃ λ F → has-limℕ F × T F

Ωᶠ : ∃ T → Fam
Ωᶠ (F , zero)    = 0ᶠ
Ωᶠ (F , suc a)   = T+ (Ωᶠ (F , a))
Ωᶠ (F , lim s a) = Σᶠ (F .₂ s) λ p → Ωᶠ (F , a p)

Ωᶠ-limℕ : ∀ {F} a → has-limℕ (Ωᶠ (F , suc a))
Ωᶠ-limℕ zero      = nothing , refl
Ωᶠ-limℕ (suc a)   = just (Ωᶠ-limℕ a .₁) , Ωᶠ-limℕ a .₂
Ωᶠ-limℕ (lim s a) = ? , ?

Ω : ∃ T → ∃ T
Ω a = T+ (Ωᶠ a) , ω

-- ∃0 : ∃ T
-- ∃0 = 0ᶠ , 0

-- ∃ω₀ : ∃ T
-- ∃ω₀ = Ω ∃0

-- ∃ω₁ : ∃ T
-- ∃ω₁ = Ω (Ω ∃0)

-- Nat : Set
-- Nat = T (Ωᶠ ∃0)

-- iter : ∀ {i}{A : Set i} → Nat → (A → A) → A → A
-- iter zero    f = id
-- iter (suc n) f = f ∘ iter n f




-- -- Omega fixpoints
-- --------------------------------------------------------------------------------

-- lfp : (f : ∃ T → ∃ T) → (∃ λ (s : f ∃0 .₁ .₁) → f ∃0 .₁ .₂ s ≡ Nat) → ∃ T
-- lfp f (s , eq) =
--         (Σᶠ Nat λ n → iter n f ∃0 .₁)
--       , lim (1 , s) λ n → tmap ((λ x → (subst id eq n) , x) , λ s' p' → p')
--                                (iter (subst id eq n) f ∃0 .₂)

-- I₀ = lfp Ω (nothing , refl)

-- fix≥ω₀ : (∃ T → ∃ T) → ∃ T
-- fix≥ω₀ f = (Σᶠ Nat λ n → iter n f ∃ω₀ .₁)
--       , lim (0 , nothing) λ n → tmap (mkΣᶠ n) (iter n f ∃ω₀ .₂)

-- Iᶠ₀ : Fam
-- Iᶠ₀ = Σᶠ Nat λ n → iter n Ω ∃0 .₁

-- I₀ : T Iᶠ₀
-- I₀ = lim (1 , nothing) λ n → tmap (mkΣᶠ n) (iter n Ω ∃0 .₂)

-- Iᶠ₁ : Fam
-- Iᶠ₁ = Σᶠ Nat λ n → iter n Ω (_ , suc I₀) .₁

-- I₁ : T Iᶠ₁
-- I₁ = lim (0 , 1 , nothing) (λ n → tmap (mkΣᶠ n) (iter n Ω (_ , suc I₀) .₂))

-- Iᶠ₂ : Fam
-- Iᶠ₂ = Σᶠ Nat λ n → iter n Ω (_ , suc I₁) .₁

-- I₂ : T Iᶠ₂
-- I₂ = lim (0 , 0 , 1 , nothing) λ n → tmap (mkΣᶠ n) (iter n Ω (_ , suc I₁) .₂)

-- Iᶠ₃ : Fam
-- Iᶠ₃ = Σᶠ Nat λ n → iter n Ω (_ , suc I₂) .₁

-- I₃ : T Iᶠ₃
-- I₃ = lim (0 , 0 , 0 , 1 , nothing) λ n → tmap (mkΣᶠ n) (iter n Ω (_ , suc I₂) .₂)
