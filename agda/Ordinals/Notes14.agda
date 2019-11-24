{-# OPTIONS --postfix-projections #-}

open import Agda.Builtin.FromNat
open import Data.Empty
open import Data.Nat using (ℕ; zero; suc; _≟_)
open import Data.Product renaming (proj₁ to ₁; proj₂ to ₂; map to Σmap)
open import Data.Unit using (⊤; tt)
open import Function
open import Relation.Binary.PropositionalEquality
  renaming (trans to infixr 5 _◾_; sym to infix 6 _⁻¹; cong to ap; subst to tr)
  hiding ([_])
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


-- Well-formed countable ordinals
--------------------------------------------------------------------------------

infix 3 _<_
data O₁ : Set
data _<_ : O₁ → O₁ → Set

lim-incr : (ℕ → O₁) → Set
lim-incr f = ∀ {n m} → n <ℕ m → f n < f m

data O₁ where
  zero : O₁
  suc  : O₁ → O₁
  lim  : (f : ℕ → O₁)(fw : lim-incr f) → O₁

data _<_ where
  suc* : ∀ {a} → a < suc a
  suc  : ∀ {a b} → a < b → a < suc b
  lim* : ∀ {f}{fw : lim-incr f} n → f n < lim f fw
  lim  : ∀ {f a}{fw : lim-incr f} n → a < f n → a < lim f fw

instance
  NumberO₁ : Number O₁
  NumberO₁ .Number.Constraint _    = ⊤
  NumberO₁ .Number.fromNat zero    = zero
  NumberO₁ .Number.fromNat (suc n) = suc (fromNat n)

<-◾ : ∀ {a b c} → a < b → b < c → a < c
<-◾ p suc*      = suc p
<-◾ p (suc q)   = suc (<-◾ p q)
<-◾ p (lim* n)  = lim n p
<-◾ p (lim n q) = lim n (<-◾ p q)

cmpO₁ : ∀ {a b c} → a < c → b < c → (a < b) ⊎ (b < a) ⊎ (a ≡ b)
cmpO₁ suc* suc* = injᶜ refl
cmpO₁ suc* (suc q) = injᵇ q
cmpO₁ (suc p) suc* = injᵃ p
cmpO₁ (suc p) (suc q) = cmpO₁ p q
cmpO₁ (lim* {f} {fw} n) (lim* m) with cmpℕ n m
... | injᵃ p = injᵃ (fw p)
... | injᵇ p = injᵇ (fw p)
... | injᶜ p = injᶜ (ap f p)
cmpO₁ (lim* {f} {fw} n) (lim m q) with cmpℕ n m
... | injᵃ p = cmpO₁ (fw p) q
... | injᵇ p = injᵇ (<-◾ q (fw p))
... | injᶜ p = injᵇ (tr (λ x → _ < f x) (p ⁻¹) q)
cmpO₁ (lim {f} {fw = fw} n p) (lim* m) with cmpℕ n m
... | injᵃ q = injᵃ (<-◾ p (fw q))
... | injᵇ q = cmpO₁ p (fw q)
... | injᶜ q = injᵃ (tr (λ x → _ < f x) q p)
cmpO₁ (lim {f} {fw = fw} n p) (lim m q) with cmpℕ n m
... | injᵃ r = cmpO₁ (<-◾ p (fw r)) q
... | injᵇ r = cmpO₁ p (<-◾ q (fw r))
... | injᶜ r = cmpO₁ p (tr (λ x → _ < f x) (r ⁻¹) q)

fromNat-incr : lim-incr (λ n → fromNat n)
fromNat-incr suc*    = suc*
fromNat-incr (suc p) = suc (fromNat-incr p)

ω₀ : O₁
ω₀ = lim (λ n → fromNat n) fromNat-incr

O₁-incr : (O₁ → O₁) → Set
O₁-incr f = ∀ {a b} → a < b → f a < f b

add   : O₁ → O₁ → O₁
add-< : ∀ {a} → O₁-incr (add a)
add zero b       = b
add a zero       = a
add a (suc b)    = suc (add a b)
add a (lim b bw) = lim (λ n → add a (b n)) (λ p → add-< {a} (bw p))
add-< {zero}     p         = p
add-< {suc a}    suc*      = suc*
add-< {suc a}    (suc p)   = suc (add-< {suc a} p)
add-< {suc a}    (lim* n)  = lim* n
add-< {suc a}    (lim n p) = lim n (add-< {suc a} p)
add-< {lim f fw} suc*      = suc*
add-< {lim f fw} (suc p)   = suc (add-< {lim f fw} p)
add-< {lim f fw} (lim* n)  = lim* n
add-< {lim f fw} (lim n p) = lim n (add-< {lim f fw} p)

not0 : O₁ → Set
not0 zero = ⊥
not0 _    = ⊤

<not0 : ∀ {a b} → a < b → not0 b
<not0 suc* = _
<not0 (suc p) = _
<not0 (lim* n) = _
<not0 (lim n p) = _

_≤_ : O₁ → O₁ → Set
a ≤ b = a ≡ b ⊎ a < b

0< : ∀ a → not0 a → 0 < a
0< (suc zero)       p = suc*
0< (suc (suc a))    p = suc (0< (suc a) p)
0< (suc (lim f fw)) p = suc (0< (lim f fw) _)
0< (lim f fw)       p = lim 1 (0< (f 1) (<not0 (fw suc*)))

0≤ : ∀ a → 0 ≤ a
0≤ zero       = inj₁ refl
0≤ (suc a)    = inj₂ (0< (suc a) _)
0≤ (lim f fw) = inj₂ (0< (lim f fw) _)

add≤ : ∀ a b → a ≤ add a b
add≤ zero       b = 0≤ b
add≤ a@(suc _)    zero = inj₁ refl
add≤ a@(suc _)    (suc b) = inj₂ (case add≤ a b of λ {
  (inj₁ p) → tr (_< suc (add a b)) (p ⁻¹) suc*;
  (inj₂ p) → suc p})
add≤ a@(suc _)    (lim b bw) = inj₂ (case add≤ a (b 0) of λ {
  (inj₁ p) → tr (_< add a (lim b bw)) (p ⁻¹) (lim* 0);
  (inj₂ p) → lim 0 p})
add≤ a@(lim f fw) zero = inj₁ refl
add≤ a@(lim f fw) (suc b) = inj₂ (case add≤ a b of λ {
  (inj₁ p) → tr (_< suc (add a b)) (p ⁻¹) suc*;
  (inj₂ p) → suc p})
add≤ a@(lim f fw) (lim b bw) = inj₂ (case add≤ a (b 0) of λ {
  (inj₁ p) → tr (_< add a (lim b bw)) (p ⁻¹) (lim* 0);
  (inj₂ p) → lim 0 p})

add< : ∀ a b {{_ : not0 b}} → a < add a b
add< zero b {{p}} = 0< b p
add< a@(suc _) (suc b) = (case add≤ a b of λ {
  (inj₁ p) → tr (_< suc (add a b)) (p ⁻¹) suc*;
  (inj₂ p) → suc p})
add< a@(suc _) (lim b bw) = (case add≤ a (b 0) of λ {
  (inj₁ p) → tr (_< add a (lim b bw)) (p ⁻¹) (lim* 0);
  (inj₂ p) → lim 0 p})
add< a@(lim _ _) (suc b) = (case add≤ a b of λ {
  (inj₁ p) → tr (_< suc (add a b)) (p ⁻¹) suc*;
  (inj₂ p) → suc p})
add< a@(lim _ _) (lim b bw) = (case add≤ a (b 0) of λ {
  (inj₁ p) → tr (_< add a (lim b bw)) (p ⁻¹) (lim* 0);
  (inj₂ p) → lim 0 p})

mul   : ∀ a {{_ : not0 a}} → O₁ → O₁
mul-< : ∀ {a}{{_ : not0 a}} → O₁-incr (mul a)
mul a zero       = 0
mul a (suc b)    = add (mul a b) a
mul a (lim b bw) = lim (λ n → mul a (b n)) (λ p → mul-< (bw p))
mul-< {a}{b} suc* = add< (mul a b) a
mul-< {a}(suc {b = c} q) = <-◾ (mul-< q) (add< (mul a c) a)
mul-< {a} (lim* {b} {bw} n) = lim (suc n) (mul-< (bw suc*))
mul-< {a} {a = b} (lim {f} {fw = fw} n p) =
  lim (suc n) (mul-< {a} {b}{f (suc n)} (<-◾ p (fw suc*)))

-- base ω exponentiation
expω₀ : O₁ → O₁
expω₀-not0 : ∀ a → not0 (expω₀ a)
expω₀< : O₁-incr expω₀
expω₀ zero       = 1
expω₀ (suc a)    = mul (expω₀ a) {{expω₀-not0 a}} ω₀
expω₀ (lim a aw) = lim (expω₀ ∘ a) (λ p → expω₀< (aw p))
expω₀-not0 zero       = _
expω₀-not0 (suc a)    = _
expω₀-not0 (lim a aw) = _
expω₀< {a} suc*  = lim* 1
expω₀< (suc p)   = lim 1 (expω₀< p)
expω₀< (lim* n)  = lim* n
expω₀< (lim n p) = lim n (expω₀< p)

ε₀suc : ∀ n → iterℕ n expω₀ 0 < iterℕ (suc n) expω₀ 0
ε₀suc zero = suc*
ε₀suc (suc n) = expω₀< (ε₀suc n)

ε₀-incr : lim-incr (λ n → iterℕ n expω₀ 0)
ε₀-incr {n} suc* = ε₀suc n
ε₀-incr (suc {m = m} p) = <-◾ (ε₀-incr p) (ε₀suc m)

ε₀ : O₁
ε₀ = lim (λ n → iterℕ n expω₀ 0) ε₀-incr

-- Ordinal classes indexed by countable ordinals
--------------------------------------------------------------------------------

data O (l : O₁) (El : ∀ i → i < l → Set) : Set where
  zero : O l El
  suc  : O l El → O l El
  lim  : (ℕ → O l El) → O l El
  Lim  : ∀ i (p : i < l) → (El i p → O l El) → O l El

El : ∀ {l} i → i < l → Set
El i suc*         = O i El
El i (suc p)      = El i p
El _ (lim* {f} n) = O (f n) El
El i (lim n p)    = El i p

U : O₁ → Set
U l = O l El

El≡ : ∀ {l i}(p : i < l) → El i p ≡ U i
El≡ suc*      = refl
El≡ (suc p)   = El≡ p
El≡ (lim* n)  = refl
El≡ (lim n p) = El≡ p

LimU : ∀ {l} i (p : i < l) → (U i → U l) → U l
LimU i p f = Lim i p (λ b → f (coe (El≡ p) b))

⇑ : ∀ {l₁ l₂} → l₁ < l₂ → U l₁ → U l₂
⇑ p zero        = zero
⇑ p (suc a)     = suc (⇑ p a)
⇑ p (lim a)     = lim (⇑ p ∘ a)
⇑ p (Lim i q a) = LimU _ (<-◾ q p) λ j → ⇑ p (a (coe (El≡ q ⁻¹) j))

instance
  NumberO : ∀ {l} → Number (U l)
  NumberO .Number.Constraint _    = ⊤
  NumberO .Number.fromNat zero    = zero
  NumberO .Number.fromNat (suc n) = suc (fromNat n)

iterU : ∀ {l} → U l → (U l → U l) → U l → U l
iterU zero        f = id
iterU (suc a)     f = f ∘ iterU a f
iterU (lim a)     f = λ b → lim λ n → iterU (a n) f b
iterU (Lim i p a) f = λ b → Lim i p λ j → iterU (a j) f b

Ω : ∀ l → U l
Ω zero       = lim λ n → fromNat n
Ω (suc l)    = LimU _ suc* (⇑ suc*)
Ω (lim f fw) = lim (λ n → ⇑ (lim* n) (Ω (f n)))

-- add = λ {l} a b → iterU {l} b suc a
-- mul = λ {l} a b → iterU {l} b (flip add a) 0
-- exp = λ {l} a b → iterU {l} b (flip mul a) 1

-- generalized fast-growing functions
F : ∀ {l i} → i < l → U l → U i → U i
F p zero    b = suc b
F p (suc a) b = iterU b (F p a) b
F p (lim a) b = lim λ n → F p (a n) b
F p (Lim j q a) b rewrite El≡ q with cmpO₁ q p
... | injᵃ r = LimU _ r λ k → F p (a k) b
... | injᵇ r = F p (a (⇑ r b)) b
... | injᶜ r = F p (a (tr U (r ⁻¹) b)) b

-- collapse
φ : ∀ l → U l → U 0
φ zero       a = a
φ (suc l)    a = φ l (F suc* a (Ω l))
φ (lim f fw) a = lim λ n → φ (f n) (F (lim* n) a (Ω (f n)))

-- fast-growing functions
f : U 0 → ℕ → ℕ
f zero    b = suc b
f (suc a) b = iterℕ b (f a) b
f (lim a) b = f (a b) b

myfunction : ℕ → ℕ
myfunction = f (φ _ (Ω ε₀))
