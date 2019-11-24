

{-# OPTIONS --postfix-projections #-}

open import Agda.Builtin.FromNat
open import Data.Empty
open import Data.Maybe using (Maybe; nothing; just; maybe)
open import Data.Nat using (ℕ; zero; suc; _≟_)
open import Data.Product renaming (proj₁ to ₁; proj₂ to ₂; map to Σmap)
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

Σᶠ : (A : Set) → (A → Fam) → Fam
Σᶠ A B = (Σ A λ a → B a .₁) , (λ ab → B (ab .₁) .₂ (ab .₂))

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


infix 3 _<1_
data _<1_ : T 1 → T 1 → Set where
  suc* : ∀ {a} → a <1 suc a
  suc  : ∀ {a b} → a <1 b → a <1 suc b
  lim* : ∀ {f} n → f n <1 lim f
  lim  : ∀ {f n a} → a <1 f n → a <1 lim f
  Lim* : ∀ {f} n → T0w n → f n <1 Lim nothing f
  Lim  : ∀ {f n a} → T0w n → a <1 f n → a <1 Lim nothing f

T1w : T 1 → Set
T1w zero            = ⊤
T1w (suc a)         = T1w a
T1w (lim a)         = ∀ n → (a n <1 a (suc n)) × T1w (a n)
T1w (Lim nothing a) = (∀ {x y} → T0w x → T0w y → x < y → a x <1 a y)
                    × (∀ x → T0w x → T1w (a x))

cmpT1 : ∀ {a b c} → T1w c → a <1 c → b <1 c → (a <1 b) ⊎ (b <1 a) ⊎ (a ≡ b)
cmpT1 cw suc* suc* = injᶜ refl
cmpT1 cw suc* (suc q) = injᵇ q
cmpT1 cw (suc p) suc* = injᵃ p
cmpT1 cw (suc p) (suc q) = cmpT1 cw p q

cmpT1 cw (lim* n) (lim* m) = {!!}
cmpT1 cw (lim* n) (lim q) = {!!}
cmpT1 cw (lim p) (lim* n) = {!!}
cmpT1 cw (lim p) (lim q) = {!!}

cmpT1 cw (Lim* {f} n nw) (Lim* m mw) = {!!}



cmpT1 cw (Lim* n x) (Lim x₁ q) = {!!}
cmpT1 cw (Lim x p) (Lim* n x₁) = {!!}
cmpT1 cw (Lim x p) (Lim x₁ q) = {!!}



U : T 0 → Fam
U zero    = 0
U (suc n) = Fam+ (U n)
U (lim a) = Σᶠ ℕ (Fam+ ∘ U ∘ a)

Uwk : ∀ {a b} → a < b → U a .₁ → U b .₁
Uwk suc*     s = just s
Uwk (suc p)  s = just (Uwk p s)
Uwk (lim* n) s = n , just s
Uwk (lim p)  s = _ , just (Uwk p s)

Uwk≡ : ∀ {a b}(p : a < b) s → U b .₂ (Uwk p s) ≡ U a .₂ s
Uwk≡ suc*     s = refl
Uwk≡ (suc p)  s = Uwk≡ p s
Uwk≡ (lim* n) s = refl
Uwk≡ (lim p)  s = Uwk≡ p s

U-cont : ∀ {a b} → a < b → U a ⇒ᶠ U b
U-cont q = (Uwk q) , (coe ∘ Uwk≡ q)

↓ : ∀ b → U b .₁ → ∃ (_< b)
↓ (suc b) nothing       = b , suc*
↓ (suc b) (just s)      = Σmap id suc (↓ b s)
↓ (lim b) (n , nothing) = b n , lim* n
↓ (lim b) (n , just s)  = Σmap id lim (↓ (b n) s)

↑ : ∀ {b} → ∃ (_< b) → U b .₁
↑ (a , suc*)   = nothing
↑ (a , suc p)  = just (↑ (a , p))
↑ (_ , lim* n) = n , nothing
↑ (a , lim p)  = _ , just (↑ (a , p))

↓↑ : ∀ {a b} (p : a < b) → ↓ b (↑ (a , p)) .₁ ≡ a
↓↑ suc*     = refl
↓↑ (suc p)  = ↓↑ p
↓↑ (lim* n) = refl
↓↑ (lim p)  = ↓↑ p

U₂≡ : ∀ a s → U a .₂ s ≡ T (U (↓ a s .₁))
U₂≡ (suc a) nothing       = refl
U₂≡ (suc a) (just s)      = U₂≡ a s
U₂≡ (lim a) (n , nothing) = refl
U₂≡ (lim a) (n , just s)  = U₂≡ (a n) s

Lim< : ∀ {a b}(p : a < b) → (T (U a) → T (U b)) → T (U b)
Lim< {a}{b} p f =
  Lim (↑ (_ , p)) λ i → f (coe (U₂≡ b (↑ (a , p)) ◾ ap (T ∘ U) (↓↑ p)) i)

ω : ∀ a → T (U a)
ω zero    = lim λ n → fromNat n
ω (suc a) = Lim< (suc* {a}) (tmap (U-cont (suc* {a})))
ω (lim a) = lim λ n → tmap (U-cont (lim* {a} n)) (ω (a n))

-- generalized fast-growing function
F : ∀ {l₁ l₂} → T0w l₂ → l₁ < l₂ → T (U l₂) → T (U l₁) → T (U l₁)
F l₂w p zero      b = suc b
F l₂w p (suc a)   b = iter b (F l₂w p a) b
F l₂w p (lim a)   b = lim (λ i → F l₂w p (a i) b)
F {l₁}{l₂} l₂w p (Lim s a) b with cmpT0 l₂w (↓ l₂ s .₂) p
... | injᵃ q = Lim< q λ i → F l₂w p (a (coe (U₂≡ l₂ s ⁻¹) i)) b
... | injᵇ q = F l₂w p (a (coe (U₂≡ l₂ s ⁻¹) (tmap (U-cont q) b))) b
... | injᶜ q = F l₂w p (a (coe (U₂≡ l₂ s ⁻¹) (tr (T ∘ U) (q ⁻¹) b))) b

-- collapse
φ : ∀ l → T0w l → T (U l) → T 0
φ zero    lw a = a
φ (suc l) lw a = φ l lw (F lw (suc* {l}) a (ω l))
φ (lim l) lw a = lim (λ i → φ (l i) (lw i .₂) (F lw (lim* i) a (ω (l i))))

--------------------------------------------------------------------------------

fromNatw : ∀ n → T0w (fromNat n)
fromNatw zero    = tt
fromNatw (suc n) = fromNatw n

ω0w : T0w (ω 0)
ω0w i = suc* , fromNatw i

F0 : T 0 → ℕ → ℕ
F0 zero    b = suc b
F0 (suc a) b = iterℕ b (F0 a) b
F0 (lim a) b = F0 (a b) b

-- larger than Takeuti-Feferman-Buchholz
myfun : ℕ → ℕ
myfun = F0 (φ (suc (ω 0)) ω0w (ω (suc (ω 0))))

mynumber : ℕ
mynumber = myfun 10
