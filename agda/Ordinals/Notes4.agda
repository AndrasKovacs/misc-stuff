
{-# OPTIONS --postfix-projections --cubical #-}

open import Agda.Builtin.FromNat
open import Data.Nat hiding (_⊔_; _<_; _≤_)
open import Data.Unit hiding (_≤_)
open import Data.Empty
open import Data.Product renaming (proj₁ to ₁; proj₂ to ₂)
open import Function
open import Data.Maybe

instance
  Numberℕ : Number ℕ
  Numberℕ .Number.Constraint _ = ⊤
  Numberℕ .Number.fromNat    m = m

iterℕ : ∀{i}{A : Set i} → ℕ → (A → A) → A → A
iterℕ zero    f = id
iterℕ (suc n) f = f ∘ iterℕ n f

Fam = Σ Set λ A → A → Set

⊥ᶠ : Fam
⊥ᶠ = ⊥ , ⊥-elim

_⇒ᶠ_ : Fam → Fam → Set; infixr 3 _⇒ᶠ_
F ⇒ᶠ G = Σ (F .₁ → G .₁) λ f → ∀ s → G .₂ (f s) → F .₂ s

data T (F : Fam) : Set where
  zero : T F
  suc  : T F → T F
  lim  : ∀ s → (F .₂ s → T F) → T F

instance
  NumberF : ∀ {F} → Number (T F)
  NumberF .Number.Constraint _    = ⊤
  NumberF .Number.fromNat n       = iterℕ n suc zero

tmap : ∀ {F G} → F ⇒ᶠ G → T F → T G
tmap (f , g) zero      = zero
tmap (f , g) (suc a)   = suc (tmap (f , g) a)
tmap (f , g) (lim s a) = lim (f s) (λ p → tmap (f , g) (a (g s p)))

T+ : Fam → Fam
T+ (S , P) = Maybe S , maybe P (T (S , P))

U : ℕ → Fam
U zero    = ⊥ᶠ
U (suc n) = T+ (U n)

Ω : ℕ → Set
Ω n = T (U n)

ω : ∀ n → T (U (suc n))
ω n = lim nothing (tmap (just , λ s p → p))

iterΩ : ∀ {n} → Ω n → (Ω n → Ω n) → Ω n → Ω n
iterΩ zero      f = id
iterΩ (suc a)   f = f ∘ iterΩ a f
iterΩ (lim s a) f = λ b → lim s (λ i → iterΩ (a i) f b)

F : ∀ {n} → Ω (suc n) → Ω n → Ω n
F zero             b = suc b
F (suc a)          b = iterΩ b (F a) b
F (lim nothing a)  b = F (a b) b
F (lim (just s) a) b = lim s (λ i → F (a i) b)

F↓ : ∀ {i} → Ω (suc i) → Ω 1
F↓ {zero}  a = a
F↓ {suc i} a = F↓ {i} (F {suc i} a (ω i))

Ω₀→ℕ : Ω 0 → ℕ
Ω₀→ℕ zero    = zero
Ω₀→ℕ (suc a) = suc (Ω₀→ℕ a)

τ : Ω 1
τ = lim nothing (λ i → F↓ {Ω₀→ℕ i} 3)

mynumber : ℕ
mynumber = Ω₀→ℕ (F {0} τ 20)
