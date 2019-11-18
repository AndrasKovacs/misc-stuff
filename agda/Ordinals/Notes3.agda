
{-# OPTIONS --postfix-projections --cubical #-}

open import Agda.Builtin.FromNat
open import Data.Nat hiding (_⊔_; _<_; _≤_)
open import Data.Unit hiding (_≤_)
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

open import Data.Maybe

iterℕ : ∀{i}{A : Set i} → ℕ → (A → A) → A → A
iterℕ zero    f = id
iterℕ (suc n) f = f ∘ iterℕ n f

-- ordinal: a set of smaller ordinals, a set of even smaller ordinals
Fam = Σ Set λ A → A → Set

zeroᶠ : Fam
zeroᶠ = ⊥ , ⊥-elim

data T {A : Set}(F : A → Fam) : Set where
  lim : {a : A}(s : F a .₁) → (F a .₂ s → T F) → T F
  Lim : (∀ a → F a .₁ → T F) → T F

< : ∀ {A F} → T {A} F → Set
< (lim b f) = ∃ λ p → Maybe (< (f p))
< (Lim f)   = ∃₂ λ a s → Maybe (< (f a s))

Ω : ∀ {A F} → T {A} F → Fam
Ω {A} {F} (lim {a} s f) = T (Ω ∘ f) , <
Ω {A} {F} (Lim f)       = T {∃ λ a → F a .₁}(λ ab → Ω (f (ab .₁) (ab .₂))) , <

open import Data.Fin using (zero; suc; Fin)

Tω = T {⊤} λ _ → ℕ , Fin

instance
  NumberTω : Number Tω
  NumberTω .Number.Constraint _ = ⊤
  NumberTω .Number.fromNat n = go n
    where go : ℕ → Tω
          go zero    = lim 0 λ ()
          go (suc n) = lim 1 λ _ → go n

Ω₀ = Ω (Tω ∋ 0) .₁
Ω₁ = Ω (Tω ∋ 1) .₁

z₀ : Ω₀
z₀ = Lim (λ ())

z₁ : Ω₁
z₁ = lim {_}{_}{zero} z₀ (λ ())

s₁ : Ω₁ → Ω₁
s₁ a = Lim λ _ _ → a
