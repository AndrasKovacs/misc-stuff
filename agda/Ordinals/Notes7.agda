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
  Numberℕ : Number ℕ
  Numberℕ = record { Constraint = λ _ → ⊤ ; fromNat = λ x → x }

iterℕ : ∀ {i}{A : Set i} → ℕ → (A → A) → A → A
iterℕ zero    f = id
iterℕ (suc n) f = f ∘ iterℕ n f

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
  lim  : (ℕ → T F) → T F
  Lim  : ∀ s → (F .₂ s → T F) → T F

instance
  NumberF : ∀ {F} → Number (T F)
  NumberF .Number.Constraint _    = ⊤
  NumberF .Number.fromNat zero    = zero
  NumberF .Number.fromNat (suc n) = suc (fromNat n)

tmap : ∀ {F G} → F ⇒ᶠ G → T F → T G
tmap (f , g) zero      = zero
tmap (f , g) (suc a)   = suc (tmap (f , g) a)
tmap (f , g) (lim a)   = lim (λ n → tmap (f , g) (a n))
tmap (f , g) (Lim s a) = Lim (f s) (λ p → tmap (f , g) (a (g s p)))

ω₀ : ∀{F} → T F
ω₀ = lim (λ n → iterℕ n suc zero)

-- small-branching ordinals
--------------------------------------------------------------------------------

∃suc : ∃ T → ∃ T
∃suc (_ , a) = _ , suc a

∃lim : (ℕ → ∃ T) → ∃ T
∃lim a = (Σᶠ ℕ (λ n → a n .₁)) , lim (λ n → tmap (mkΣᶠ n) (a n .₂))

∃Lim : ∀ {F : Fam} s → (F .₂ s → ∃ T) → ∃ T
∃Lim {F} s a =
    ( Maybe (Σ (F .₂ s) (λ p → a p .₁ .₁))
    , maybe (λ xp → a (xp .₁) .₁ .₂ (xp .₂)) (F .₂ s))
  , Lim nothing λ p → tmap ((λ x → just (p , x)) , λ _ p → p) (a p .₂)

∃ω₀ : ∃ T
∃ω₀ = 0ᶠ , ω₀

instance
  liftInst : ∀{i j}{A : Set i}{{_ : A}} → Lift j A
  liftInst {{a}} = lift a

  Number∃T : Number (∃ T)
  Number∃T .Number.Constraint _    = Lift _ ⊤
  Number∃T .Number.fromNat zero    = 0ᶠ , 0
  Number∃T .Number.fromNat (suc n) = ∃suc (fromNat n)

-- ω function. ω n = (n + 1)-th recursively admissible ordinal
Lim+ : Fam → Fam
Lim+ (S , P) = Maybe S , maybe P (T (S , P))

ωᶠ : ∃ T → Fam
ωᶠ (F , zero)    = 0ᶠ
ωᶠ (F , suc a)   = Lim+ (ωᶠ (F , a))
ωᶠ (F , lim a)   = Σᶠ ℕ λ n → ωᶠ (F , a n)
ωᶠ (F , Lim s a) = Σᶠ (F .₂ s) λ p → ωᶠ (F , a p)

ω : ∃ T → ∃ T
ω a = Lim+ (ωᶠ a) , Lim nothing (tmap (just , (λ s p → p)))

-- small-branching iteration
iter : ∃ T → (∃ T → ∃ T) → ∃ T → ∃ T
iter (_ , zero)    f = id
iter (_ , suc a)   f = f ∘ iter (_ , a) f
iter (_ , lim a)   f = λ b → ∃lim (λ n → iter (_ , a n) f b)
iter (F , Lim s a) f = λ b → ∃Lim {F} s (λ i → iter (_ , a i) f b)

iter2 : ∃ T → ((∃ T → ∃ T) → (∃ T → ∃ T)) → (∃ T → ∃ T) → (∃ T → ∃ T)
iter2 (_ , zero)    f = id
iter2 (_ , suc a)   f = f ∘ iter2 (_ , a) f
iter2 (_ , lim a)   f = λ g b → ∃lim λ n → iter2 (_ , a n) f g b
iter2 (F , Lim s a) f = λ g b → ∃Lim {F} s λ i → iter2 (_ , a i) f g b

--  least fixpoint above given value
lfpAbove : (∃ T → ∃ T) → ∃ T → ∃ T
lfpAbove f a = ∃lim (λ n → iterℕ n f a)

-- leaft fixpoint
lfp : (∃ T → ∃ T) → ∃ T
lfp f = lfpAbove f 0

-- enumeration of fixpoints
enumFixes : (∃ T → ∃ T) → ∃ T → ∃ T
enumFixes f a = iter a (lfpAbove f ∘ ∃suc) (lfp f)

--------------------------------------------------------------------------------

Fam1 : Set₂
Fam1 = Σ Set₁ λ A → A → Set₁

data T1 (F : Fam1) : Set₁ where
  zero : T1 F
  suc  : T1 F → T1 F
  lim  : (ℕ → T1 F) → T1 F
  Lim  : ∀ s → (F .₂ s → T1 F) → T1 F

Iᶠ : Fam1
Iᶠ = (Maybe (Σ Fam λ F → F .₁)) , (maybe (λ fs → Lift _ (fs .₁ .₂ (fs .₂))) (∃ T))

T↑ : ∃ T → T1 Iᶠ
T↑ (_ , zero)    = zero
T↑ (_ , suc a)   = suc (T↑ (_ , a))
T↑ (_ , lim a)   = lim (λ n → T↑ (_ , a n))
T↑ (F , Lim s a) = Lim (just (F , s)) λ b → T↑ (F , a (lower b))

I : T1 Iᶠ
I = Lim nothing T↑
