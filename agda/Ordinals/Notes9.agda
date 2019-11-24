{-# OPTIONS --postfix-projections #-}

open import Agda.Builtin.FromNat
open import Data.Empty
open import Data.Maybe
open import Data.Nat using (ℕ; zero; suc; _≟_)
open import Data.Product renaming (proj₁ to ₁; proj₂ to ₂)
open import Data.Unit using (⊤; tt)
open import Function
open import Level renaming (zero to lzero; suc to lsuc)
open import Relation.Binary.Definitions
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Relation.Nullary.Decidable

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

-- branching type of next admissible ordinal
ωᶠ+ : Fam → Fam
ωᶠ+ (S , P) = Maybe S , maybe P (T (S , P))

ωᶠ : T 0ᶠ → Fam
ωᶠ (zero)  = 0ᶠ
ωᶠ (suc a) = ωᶠ+ (ωᶠ a)
ωᶠ (lim a) = Σᶠ ℕ (ωᶠ ∘ a)

ω : T 0ᶠ → ∃ T
ω a = ωᶠ+ (ωᶠ a) , Lim nothing (tmap (just , (λ s p → p)))

lfp : ∀ {F} → (T F → T F) → T F
lfp {F} f = lim λ n → iterℕ n f 0

ω' : ∀ a → T (ωᶠ a)
ω' zero    = lim λ n → iterℕ n suc 0
ω' (suc a) = ω a .₂
ω' (lim a) = lim (λ n → tmap (mkΣᶠ n) (ω' (a n)))

iter : ∀ {F} → T F → (T F → T F) → T F → T F
iter zero f = id
iter (suc a) f = f ∘ iter a f
iter (lim a) f = λ b → lim λ n → iter (a n) f b
iter (Lim s a) f = λ b → Lim s λ c → iter (a c) f b

add = λ {F} a b → iter {F} b suc a
mul = λ {F} a b → iter {F} b (flip add a) 0
exp = λ {F} a b → iter {F} b (flip mul a) 1

φ- : ∀ {a} → T (ωᶠ (suc a)) → T (ωᶠ a)
φ- zero             = lfp (exp (ω' _))
φ- (suc a)          = lfp (exp (φ- a))
φ- (lim a)          = lim (λ n → φ- (a n))
φ- (Lim nothing a)  = lfp (φ- ∘ a)
φ- (Lim (just s) a) = Lim s (φ- ∘ a)

φ↓ : ∀ f {n} → T (ωᶠ (lim f)) → T (ωᶠ (f n))
φ↓ f zero      = lfp (exp (ω' _))
φ↓ f (suc a)   = lfp (exp (φ↓ f a))
φ↓ f (lim a)   = lim (φ↓ f ∘ a)
φ↓ f {n} (Lim (m , x) a) = {!!}

φ : ∀ a → T (ωᶠ a) → T 0ᶠ
φ zero    b = b
φ (suc a) b = φ a (φ- b)
φ (lim a) b = lim λ n → φ (a n) (φ↓ a b)


-- F- : ∀ {F} → T (ωᶠ+ F) → T F → T F
-- F- {F} zero b = suc b
-- F- {F} (suc a) b = iter b (F- a) b
-- F- {F} (lim a) b = lim λ n → F- (a n) b
-- F- {F} (Lim nothing a) b = F- (a b) b
-- F- {F} (Lim (just s) a) b = Lim s λ c → F- (a c) b

-- foo : ∀ {a} → T (ωᶠ a)
-- foo {zero}    = lim λ n → iterℕ n suc zero
-- foo {suc a}   = Lim nothing (tmap (just , (λ s p → p)))
-- foo {lim a}   = lim (λ n → tmap ((λ x → n , x) , λ s p → p) (foo {a n}))

-- F↓ : ∀ {n f} → T (Σᶠ ℕ (ωᶠ ∘ f)) → T (ωᶠ (f n)) → T (ωᶠ (f n))
-- F↓ zero       b = suc b
-- F↓ {n} {f} (suc a) b = iter b (F↓ {n}{f} a) b
-- F↓ {n'}{f}(lim a)   b = lim λ n → F↓ {n'}{f}(a n) b
-- F↓ {n}{f} (Lim (n' , bn') a) b with n ≟ n'
-- ... | yes refl = Lim bn' (λ p → F↓ {n}{f}(a p) b)
-- ... | no p     = b  --- This looks stupid

-- φ : ∀ a → T (ωᶠ a) → T 0ᶠ
-- φ zero b = b
-- φ (suc a) b = φ a (F- b foo)
-- φ (lim a) b = lim (λ n → φ (a n) (F↓ {_}{a} b foo))
