{-# OPTIONS --postfix-projections #-}

open import Agda.Builtin.FromNat
open import Data.Empty
open import Data.Maybe using (Maybe; nothing; just; maybe)
open import Data.Nat using (ℕ; zero; suc; _≟_)
open import Data.Product renaming (proj₁ to ₁; proj₂ to ₂)
open import Data.Unit using (⊤; tt)
open import Function
open import Level renaming (zero to lzero; suc to lsuc)
open import Relation.Binary.Definitions
open import Relation.Binary.PropositionalEquality
  renaming (trans to infixr 5 _◾_; sym to infix 6 _⁻¹; cong to ap; subst to tr)
open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Data.Sum

instance
  Numberℕ : Number ℕ
  Numberℕ = record { Constraint = λ _ → ⊤ ; fromNat = λ x → x }

iterℕ : ∀ {i}{A : Set i} → ℕ → (A → A) → A → A
iterℕ zero    f = id
iterℕ (suc n) f = f ∘ iterℕ n f

coe : ∀ {i}{A B : Set i} → A ≡ B → A → B
coe refl x = x

pattern injᵃ x = inj₁ x
pattern injᵇ x = inj₂ (inj₁ x)
pattern injᶜ x = inj₂ (inj₂ x)

infix 4 _<ℕ_
data _<ℕ_ : ℕ → ℕ → Set where
  suc* : ∀ {n} → n <ℕ suc n
  suc  : ∀ {n m} → n <ℕ m → n <ℕ suc m

<ℕ-◾ : ∀ {x y z} → x <ℕ y → y <ℕ z → x <ℕ z
<ℕ-◾ p suc*    = suc p
<ℕ-◾ p (suc q) = suc (<ℕ-◾ p q)

0<ℕ : ∀ n → 0 <ℕ suc n
0<ℕ zero    = suc*
0<ℕ (suc n) = suc (0<ℕ n)

s<ℕs : ∀ {n m} → n <ℕ m → suc n <ℕ suc m
s<ℕs suc*    = suc*
s<ℕs (suc p) = suc (s<ℕs p)

cmpℕ : ∀ a b → (a <ℕ b) ⊎ (b <ℕ a) ⊎ (a ≡ b)
cmpℕ zero zero = injᶜ refl
cmpℕ zero (suc b) = injᵃ (0<ℕ b)
cmpℕ (suc a) zero = injᵇ (0<ℕ a)
cmpℕ (suc a) (suc b) with cmpℕ a b
... | injᵃ p = injᵃ (s<ℕs p)
... | injᵇ p = injᵇ (s<ℕs p)
... | injᶜ p = injᶜ (ap suc p)

--------------------------------------------------------------------------------

Fam : Set₁
Fam = Σ Set λ A → A → Set

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

-- branching type of next admissible ordinal
Fam+ : Fam → Fam
Fam+ (S , P) = Maybe S , maybe P (T (S , P))

instance
  liftInst : ∀{i j}{A : Set i}{{_ : A}} → Lift j A
  liftInst {{a}} = lift a

  instance
   NumberFam : Number Fam
   NumberFam .Number.Constraint _ = Lift _ ⊤
   NumberFam .Number.fromNat zero    = (⊥ , ⊥-elim)
   NumberFam .Number.fromNat (suc n) = Fam+ (fromNat n)

iter : ∀ {F} → T F → (T F → T F) → T F → T F
iter zero f = id
iter (suc a) f = f ∘ iter a f
iter (lim a) f = λ b → lim λ n → iter (a n) f b
iter (Lim s a) f = λ b → Lim s λ c → iter (a c) f b

infix 3 _<_
data _<_ : T 0 → T 0 → Set where
  suc* : ∀ {a} → a < suc a
  suc  : ∀ {a b} → a < b → a < suc b
  lim* : ∀ {f} n → f n < lim f
  lim  : ∀ {f n a} → a < f n → a < lim f

_≤_ : T 0 → T 0 → Set; infix 3 _≤_
a ≤ b = a ≡ b ⊎ a < b

<-◾ : ∀ {a b c} → a < b → b < c → a < c
<-◾ p suc*     = suc p
<-◾ p (suc  q) = suc (<-◾ p q)
<-◾ p (lim* q) = lim p
<-◾ p (lim  q) = lim (<-◾ p q)

T0w : T 0 → Set
T0w zero    = ⊤
T0w (suc a) = T0w a
T0w (lim a) = ∀ n → (a n < a (suc n)) × T0w (a n)

lim< : ∀ f → T0w (lim f) → ∀ {a b} → a <ℕ b → f a < f b
lim< f fw {a} suc*            = fw a .₁
lim< f fw {a} (suc {m = m} p) = <-◾ (lim< f fw p) (fw m .₁)

cmpT0 : ∀ {a b c} → T0w c → a < c → b < c → (a < b) ⊎ (b < a) ⊎ (a ≡ b)
cmpT0 cw suc*     suc*     = injᶜ refl
cmpT0 cw suc*     (suc q)  = injᵇ q
cmpT0 cw (suc p)  suc*     = injᵃ p
cmpT0 cw (suc p)  (suc q)  = cmpT0 cw p q
cmpT0 cw (lim* n) (lim* m) with cmpℕ n m
... | injᵃ p = injᵃ (lim< _ cw p)
... | injᵇ p = injᵇ (lim< _ cw p)
... | injᶜ p = injᶜ (ap _ p)
cmpT0 {a}{b} cw (lim* n) (lim {f} {m} q) with cmpℕ n m
... | injᵃ p = cmpT0 (cw m .₂) (lim< f cw p) q
... | injᵇ p = injᵇ (<-◾ q (lim< _ cw p))
... | injᶜ p = injᵇ (tr (λ x → b < f x) (p ⁻¹) q)
cmpT0 {a}{b} cw (lim {f}{n} p) (lim* m) with cmpℕ n m
... | injᵃ q = injᵃ (<-◾ p (lim< _ cw q))
... | injᵇ q = cmpT0 (cw n .₂) p (lim< _ cw q)
... | injᶜ q = injᵃ (tr (λ x → a < f x) q p)
cmpT0 {a}{b} cw (lim {f}{n = n} p) (lim {n = m} q) with cmpℕ n m
... | injᵃ r = cmpT0 (cw m .₂) (<-◾ p (lim< _ cw r)) q
... | injᵇ r = cmpT0 (cw n .₂) p (<-◾ q (lim< _ cw r))
... | injᶜ r = cmpT0 (cw n .₂) p (tr (λ x → b < f x) (r ⁻¹) q)

U : T 0 → Fam
U zero    = 0
U (suc n) = Fam+ (U n)
U (lim a) = Σᶠ ℕ (U ∘ a)

ω : ∀ a → T (U a)
ω zero    = lim λ n → fromNat n
ω (suc a) = Lim nothing (tmap (just , λ s p → p))
ω (lim a) = lim λ n → tmap (mkΣᶠ n) (ω (a n))

Uwk : ∀ {a b} → a < b → U a .₁ → U b .₁
Uwk suc*     s = just s
Uwk (suc p)  s = just (Uwk p s)
Uwk (lim* n) s = n , s
Uwk (lim p)  s = _ , Uwk p s

Uwk≡ : ∀ {a b}(p : a < b) s → U b .₂ (Uwk p s) ≡ U a .₂ s
Uwk≡ suc*     s = refl
Uwk≡ (suc p)  s = Uwk≡ p s
Uwk≡ (lim* n) s = refl
Uwk≡ (lim p)  s = Uwk≡ p s

U-cont : ∀ {a b} → a < b → U a ⇒ᶠ U b
U-cont q = (Uwk q) , (λ s → coe (Uwk≡ q s))

U-cont≤ : ∀ {a b} → a ≤ b → U a ⇒ᶠ U b
U-cont≤ (inj₁ refl) = (λ s → s) , (λ s p → p)
U-cont≤ (inj₂ p)    = U-cont p

U↓ : ∀ a → U a .₁ → T 0
U↓ (suc a) nothing  = a
U↓ (suc a) (just s) = U↓ a s
U↓ (lim a) (n , s)  = U↓ (a n) s

Uwk↓ : ∀ {a b} p s → U↓ b (Uwk {a}{b} p s) ≡ U↓ a s
Uwk↓ suc*     s = refl
Uwk↓ (suc p)  s = Uwk↓ p s
Uwk↓ (lim* n) s = refl
Uwk↓ (lim p)  s = Uwk↓ p s

U↓< : ∀ a (s : U a .₁) → U↓ a s < a
U↓< (suc a) nothing  = suc*
U↓< (suc a) (just s) = suc (U↓< a s)
U↓< (lim a) (n , s)  = lim (U↓< (a n) s)

U↓≡ : ∀ a (s : U a .₁) → U a .₂ s ≡ T (U (U↓ a s))
U↓≡ (suc a) nothing  = refl
U↓≡ (suc a) (just s) = U↓≡ a s
U↓≡ (lim a) (n , s)  = U↓≡ (a n) s

U↑ : ∀ {a b} → a < b → U b .₁
U↑ suc*         = nothing
U↑ (suc p)      = just (U↑ p)
U↑ (lim* {f} n) = n , {!!}
U↑ (lim p)      = _ , U↑ p

-- U↓↑ : ∀ {a b} p → U↓ b (U↑ {suc a}{b} p nothing) ≡ a
-- U↓↑ {a} {suc .(suc a)} suc* = refl
-- U↓↑ {a} {suc b} (suc p) = U↓↑ p
-- U↓↑ {a} {lim b} p = {!!}

-- Fam+map : ∀ {F G} → F ⇒ᶠ G → Fam+ F ⇒ᶠ Fam+ G
-- Fam+map (f , g) = Data.Maybe.map f , λ {nothing p → {!!}; (just s) p → g s p}

Lim< : ∀ {a b}(p : a < b) → T0w b → (T (U a) → T (U b)) → T (U b)
Lim< {a}{b} p bw f = {!!}

-- Lim< {zero}     p bw f =
--   lim (λ i → f (fromNat i))
-- Lim< {suc a}{b} p bw f =
--   Lim (U↑ p nothing) λ i → f (tmap (just , λ _ p → p) (coe (U↑≡ p nothing) i))
-- Lim< {lim a} {suc .(lim a)} suc* bw f = Lim nothing f
-- Lim< {lim a} {suc b} (suc p) bw f =
--   tmap (Fam+map (U-cont p)) (Lim {U (suc (lim a))} nothing ({!!} ∘ f))
-- Lim< {lim a} {lim x} p bw f = {!!}
-- Lim< {lim a} {suc .(lim a)} suc* bw f =
--   Lim nothing f
-- Lim< {lim a} {suc b} (suc p) bw f =
--   {!!}
-- Lim< {lim a} {lim b} p bw f = {!!}

-- Lim< : ∀ {a b c} → a < c → b ≤ c → (T (U a) → T (U b)) → T (U c)
-- Lim< {zero}  p q f = lim (λ n → tmap (U-cont≤ q) (f (fromNat n)))
-- Lim< {suc a}{b} p q f = {!Lim {U (suc b)} (U↑ p nothing)!}
-- Lim< {lim a}{b} p q f = {!!}


F↓ : ∀ f {n} → T0w (lim f) → T (U (lim f)) → T (U (f n)) → T (U (f n))
F↓ f fw zero    b = suc b
F↓ f fw (suc a) b = iter b (F↓ f fw a) b
F↓ f fw (lim a) b = lim λ n → F↓ f fw (a n) b
F↓ f {n*} fw (Lim s a) b rewrite U↓≡ (lim f) s
  with cmpT0 {f n*}{U↓ (lim f) s} fw (lim* n*) (U↓< (lim f) s)
... | injᵃ p = F↓ f fw (a (tmap (U-cont p) b)) b
... | injᵇ p = {!!} -- Lim< p (fw n* .₂) λ i → F↓ f fw (a i) b
... | injᶜ p = F↓ f fw (a (tr (T ∘ U) p b)) b
