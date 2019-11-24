
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
open import Data.Sum

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

∘ᶠ : ∀ {F G H} → G ⇒ᶠ H → F ⇒ᶠ G → F ⇒ᶠ H
∘ᶠ f g = (f .₁ ∘ g .₁) , (λ s p → g .₂ s (f .₂ (g .₁ s) p))

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

iter : ∀ {F} → T F → (T F → T F) → T F → T F
iter zero f = id
iter (suc a) f = f ∘ iter a f
iter (lim a) f = λ b → lim λ n → iter (a n) f b
iter (Lim s a) f = λ b → Lim s λ c → iter (a c) f b

-- branching type of next admissible ordinal
Ad+ : Fam → Fam
Ad+ (S , P) = Maybe S , maybe P (T (S , P))

U : ℕ → Fam
U zero = 0ᶠ
U (suc n) = Ad+ (U n)

infix 3 _<_
data _<_ : ℕ → ℕ → Set where
  here : ∀ {n} → n < suc n
  suc  : ∀ {n m} → n < m → n < suc m

<-trans : ∀ {x y z} → x < y → y < z → x < z
<-trans p here = suc p
<-trans p (suc q) = suc (<-trans p q)

0< : ∀ n → 0 < suc n
0< zero    = here
0< (suc n) = suc (0< n)

s<s : ∀ {n m} → n < m → suc n < suc m
s<s here    = here
s<s (suc p) = suc (s<s p)

pattern injᵃ x = inj₁ x
pattern injᵇ x = inj₂ (inj₁ x)
pattern injᶜ x = inj₂ (inj₂ x)


compare : ∀ n m → (n < m) ⊎ (m < n) ⊎ (n ≡ m)
compare zero zero    = injᶜ refl
compare zero (suc m) = injᵃ (0< _)
compare (suc n) zero = injᵇ (0< _)
compare (suc n) (suc m) with compare n m
... | injᵃ p = injᵃ (s<s p)
... | injᵇ p = injᵇ (s<s p)
... | injᶜ p = injᶜ (cong suc p)

U-lift : ∀ {n m} → n < m → U n .₁ → U m .₁
U-lift here    s = just s
U-lift (suc p) s = just (U-lift p s)

U-liftP : ∀ {n m}(p : n < m) s → U m .₂ (U-lift p s) ≡ U n .₂ s
U-liftP here    s = refl
U-liftP (suc p) s = U-liftP p s

U-cont : ∀ {n m} → n < m → U n ⇒ᶠ U m
U-cont here                = just , λ s p → p
U-cont {n} (suc {m = m} p) =
  ∘ᶠ {U n}{U m}{Ad+ (U m)} (just , λ s p → p) (U-cont p)

-- U' : Maybe ℕ → Fam
-- U' nothing  = Σᶠ ℕ U
-- U' (just n) = U n

lfp : ∀ {F} → (T F → T F) → T F
lfp {F} f = lim λ n → iterℕ n f 0

-- "true" arity
str : ∀ {n} x → ∃₂ λ m (p : m < n) → (U n .₂ x ≡ T (U m))
str {suc n} nothing  = n , (here , refl)
str {suc n} (just x) with str {n} x
... | m , p , q = m , suc p , q

point : ∀ n → T (U n)
point zero    = lim λ i → fromNat i
point (suc n) = Lim nothing (tmap (just , λ _ p → p))

-- strengthen : ∀ {n}(s : U n .₁) → ∃ λ m →
-- strengthen a = {!!}

F↓ : ∀ {n} → T (Σᶠ ℕ U) → T (U n) → T (U n)
F↓ zero      b = suc b
F↓ (suc a)   b = iter b (F↓ a) b
F↓ (lim a)   b = lim (λ n → F↓ (a n) b)
F↓ {n} (Lim (m , x) a) b with compare n m
... | injᵇ p    = Lim (U-cont p .₁ x) λ i → F↓ (a (U-cont p .₂ _ i)) b
... | injᶜ refl = Lim x (λ i → F↓ (a i) b)
... | injᵃ p with str {m} x
... |  m' , r , s with compare n m'
... | injᵃ t = F↓ (a (subst id (sym s) (tmap {U n}{U m'}(U-cont t) b))) b
... | injᶜ refl = F↓ (a (subst id (sym s) b)) b
... | injᵇ t with m'
   -- ugliness because of the possibility of m' being 0
... | 0   = lim λ i → F↓ (a (subst id (sym s) (fromNat i))) b
... | suc m'' = Lim (U-lift t nothing) λ i
              → F↓ (a (subst id (sym s) (tmap {U m''}{U (suc m'')} (U-cont {m''}{suc m''} here) (subst id (U-liftP t nothing) i)))) b

F- : ∀ {n} → T (U (suc n)) → T (U n) → T (U n)
F- zero             b = suc b
F- (suc a)          b = iter b (F- a) b
F- (lim a)          b = lim (λ i → F- (a i) b)
F- (Lim nothing a)  b = F- (a b) b
F- (Lim (just s) a) b = Lim s (λ i → F- (a i) b)

F : ∀ {n} → T (U n) → T (U 0)
F {zero}  a = a
F {suc n} a = F {n} (F- a (point n))

Fω : T (Σᶠ ℕ U) → T (U 0)
Fω a = lim (λ i → F {i} (F↓ {i} a (point i)))
