{-# OPTIONS --postfix-projections --without-K --safe #-}

{-
Large countable ordinals in Agda. For examples, see the bottom of this file.
Checked with Agda 2.6.0.1.

Countable ordinals are useful in "big number" contests, because they
can be directly converted into fast-growing ℕ → ℕ functions via the
fast-growing hierarchy:

  https://en.wikipedia.org/wiki/Fast-growing_hierarchy

Here I'm concerned with constructive definitions of ordinals such that
we can extract ℕ → ℕ functions from them.

In set theory, collapsing functions are powerful for defining large countable
ordinals, but by default they are not constructive.

  https://en.wikipedia.org/wiki/Ordinal_collapsing_function

One way of getting constructive definitions is via ordinal notation systems.
Proof theorists have devised many of these. Ordinal notations are often based on
collapsing functions, and they provide decidable first-order syntax for all
countable ordinals below some limit. I.e., given a notation system for ordinals
up to α, all smaller ordinals are representable and their ordering can be
decided. Obviously, this can only possibly work for countable ordinals, because
every notation is countable.

However, ordinal notations can be very complicated to formalize. In Agda, even
the weakest of them, the Cantor normal forms, can be fiddly to formalize.

In Agda, if we just want fast-growing functions, then it is far easier to use
infinitary inductive types to represent "tree" ordinals. These allow us to get
fairly large ordinals almost trivially. However, there are issues when we want
to go further; the problem is that huge trees are too extensional, and we are
often not able to analyze their structure.

For example, take the type of arbitrary small-set-branching trees:

  data Tree : Set₁ where
    node : (A : Set₀) → (A → Tree) → Tree

Tree is quite large from a set-theoretical perspective, as it corresponds to the
least fixed point of the (covariant) powerset function. But we don't have a
natural way to write a function (f : Tree → ℕ → ℕ), because (A : Set₀) is a
black box, and the function space over it is also extensional. In short:

- ordinal notations: intensional, first-order, decidable, precise
- tree ordinals: extensional, higher-order, undecidable, imprecise (over-approximated)

This file contains the extent to which I was able to define large tree ordinals
which still naturally support collapse to countable ordinals.

My collapsing function is based on Madore's ψ from

  https://en.wikipedia.org/wiki/Ordinal_collapsing_function

more precisely the iterated (non-simultaneous) collapse described in section
"Going beyond the Bachmann–Howard ordinal", which describes finitely iterated
collapse. It also introduces a non-iterated "simultaneously inductive" collapse,
which is supposedly easier to extend to infinite families of collapsing
functions. However, I have found that in Agda it is easier to extend the
finitely iterated collapse to transfinite iteration.

The first crucial observation in this file is that bounded countable tree
ordinals have decidable ordering. I have the following definition:

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

This is infinitary inductive-inductive, for convenience, but I am sure that it
can be also defined without induction-induction, using a separate
well-formedness predicate. These ordinals are fairly well-formed, but of course
we cannot prove many classical equlities because of the lack of quotienting on
limits.

We clearly do not have decidable ordering on O₁ because of the (ℕ → O₁)
functions. However, we do have decidable ordering on ordinals bounded by
an arbitrary O₁.

  cmpO₁ : ∀ {a b c} → a < c → b < c → (a < b) ⊎ (b < a) ⊎ (a ≡ b)

Intuitively, a proof of (a < c) is a path to a subtree of c. But since we have
unary and ℕ branching, every such a path is essentially an inhabitant of an
iterated Maybe/(Σ ℕ) type. So, paths only contain first-order decidable data.

So, if we can find a large enough O₁, such that every O₁ which we are interested in
is below it, then we have decidable ordering! For every O₁, we get a recursive ordinal
notation "for free".

Then, the next task is to exploit decidable countable ordinals to define much larger
ordinals, with sufficiently "intensional" structure.

We define ordinal classes indexed by countable ordinals. The indices can be
viewed as "universe levels" of ordinals. I actually use "U l" to refer to the
l-th ordinal class. The index specifies the kinds of allowed limits/branching in
a tree. In my version, trees in U 0 branch at most with ℕ arity, U 1 can also
branch over U 0, U 2 over U 1, and so on.

In imaginary Agda, we have the following definition. The ℕ-limit "lim" is always
available; as I said above, U 0 is already ℕ-branching. It is possible to
set U 0 ≃ ℕ or even U 0 ≃ ⊥, but it is convenient to always have ℕ-limits
available.

    data U (l : O₁) : Set where
      zero : U l
      suc  : U l → U l
      lim  : (ℕ → U l) → U l
      Lim  : (i : O₁)(p : i < l) → (U i → U l) → U l

The real Agda does not accept this, complaining about positivity. It is not
difficult to repair this situation, by using a universe representation trick
(see this file for details).

With this definition, limit arities are indexed over Σ(i : O₁)×(i < l), hence we
have decidable arity comparison. This is essential for defining collapsing functions.
We want to define a function with the following type:

  ∀ {i j} → i < j → U j → U i

The task is to convert a tree with larger limits to a tree which only contains
smaller limits, so we need to be able to tell which Lim-s in the input are too
large to fit in the output, and somehow squeeze them into smaller limits without
throwing away too much information. Hence the need for decidable limit arity.
The general idea for "squeezing" large limits down is to turn them into
fixpoints or to diagonalize over them.

I do not see a way to get decidable arities when we move to universes indexed by
uncountable ordinals. Probably we would need to switch to a completely different
methodology, maybe to ordinal notations based on larger uncountable/inaccessible
ordinals.

This file is IMO the furthest we can go with a relatively small amount of easy
Agda code. It is possible to extend this file by defining larger well-formed
countable ordinals, in order to index larger universes, but that would be
negligible progress towards the next interesting countable ordinals, which are
given by collapsing inaccessible ordinals. Just defining inaccessible ordinals
is easy in Agda, using large types similar to Tree, but I have no clue how to
collapse them.

-}

open import Agda.Builtin.FromNat
open import Data.Empty
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product renaming (proj₁ to ₁; proj₂ to ₂; map to Σmap)
open import Data.Sum
open import Data.Unit using (⊤; tt)
open import Function
open import Relation.Binary.PropositionalEquality

-- std definitions
--------------------------------------------------------------------------------

_◾_ = trans; infixr 4 _◾_
_⁻¹ = sym; infix 6 _⁻¹
ap  = cong
tr  = subst

-- we use overloaded literals
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


-- Well-formed countable ordinals. They are not quotiented though, so lots of
-- classical equations are unprovable. We only use well-formed countable ordinals
-- to index a larger universe of (uncountable) ordinals.

-- We have a bit of ugly and fiddly code here, in order to get ε₀, and thereby
-- a recursive notation up to ε₀. We could delete 100 lines from this part,
-- and only get something like ω₀ in O₁, and we would still have pretty large
-- things. I include the definition of ε₀ here in order to get as far as possible
-- in the nLab table:

--   https://ncatlab.org/nlab/show/ordinal+analysis#table_of_ordinal_analyses
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
  NumberO₁ .Number.Constraint _ = ⊤
  NumberO₁ .Number.fromNat n    = iterℕ n suc zero


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

_+_   : O₁ → O₁ → O₁; infixl 6 _+_
+-< : ∀ {a} → O₁-incr (_+_ a)
_+_ zero b       = b
_+_ a zero       = a
_+_ a (suc b)    = suc (_+_ a b)
_+_ a (lim b bw) = lim (λ n → _+_ a (b n)) (λ p → +-< {a} (bw p))
+-< {zero}     p         = p
+-< {suc a}    suc*      = suc*
+-< {suc a}    (suc p)   = suc (+-< {suc a} p)
+-< {suc a}    (lim* n)  = lim* n
+-< {suc a}    (lim n p) = lim n (+-< {suc a} p)
+-< {lim f fw} suc*      = suc*
+-< {lim f fw} (suc p)   = suc (+-< {lim f fw} p)
+-< {lim f fw} (lim* n)  = lim* n
+-< {lim f fw} (lim n p) = lim n (+-< {lim f fw} p)

not0 : O₁ → Set
not0 zero = ⊥
not0 _    = ⊤

<not0 : ∀ {a b} → a < b → not0 b
<not0 suc* = _
<not0 (suc p) = _
<not0 (lim* n) = _
<not0 (lim n p) = _

_≤_ : O₁ → O₁ → Set; infix 3 _≤_
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

+≤ : ∀ a b → a ≤ a + b
+≤ zero       b = 0≤ b
+≤ a@(suc _)    zero = inj₁ refl
+≤ a@(suc _)    (suc b) = inj₂ (case +≤ a b of λ {
  (inj₁ p) → tr (_< suc (a + b)) (p ⁻¹) suc*;
  (inj₂ p) → suc p})
+≤ a@(suc _)    (lim b bw) = inj₂ (case +≤ a (b 0) of λ {
  (inj₁ p) → tr (_< (a + lim b bw)) (p ⁻¹) (lim* 0);
  (inj₂ p) → lim 0 p})
+≤ a@(lim f fw) zero = inj₁ refl
+≤ a@(lim f fw) (suc b) = inj₂ (case +≤ a b of λ {
  (inj₁ p) → tr (_< suc (a + b)) (p ⁻¹) suc*;
  (inj₂ p) → suc p})
+≤ a@(lim f fw) (lim b bw) = inj₂ (case +≤ a (b 0) of λ {
  (inj₁ p) → tr (_< (a + lim b bw)) (p ⁻¹) (lim* 0);
  (inj₂ p) → lim 0 p})

+< : ∀ a b {{_ : not0 b}} → a < a + b
+< zero b {{p}} = 0< b p
+< a@(suc _) (suc b) = (case +≤ a b of λ {
  (inj₁ p) → tr (_< suc (a + b)) (p ⁻¹) suc*;
  (inj₂ p) → suc p})
+< a@(suc _) (lim b bw) = (case +≤ a (b 0) of λ {
  (inj₁ p) → tr (_< (a + lim b bw)) (p ⁻¹) (lim* 0);
  (inj₂ p) → lim 0 p})
+< a@(lim _ _) (suc b) = (case +≤ a b of λ {
  (inj₁ p) → tr (_< suc (a + b)) (p ⁻¹) suc*;
  (inj₂ p) → suc p})
+< a@(lim _ _) (lim b bw) = (case +≤ a (b 0) of λ {
  (inj₁ p) → tr (_< (a + lim b bw)) (p ⁻¹) (lim* 0);
  (inj₂ p) → lim 0 p})

_*_   : ∀ a {{_ : not0 a}} → O₁ → O₁; infixl 7 _*_
*-< : ∀ {a}{{_ : not0 a}} → O₁-incr (_*_ a)
_*_ a zero       = 0
_*_ a (suc b)    = a * b + a
_*_ a (lim b bw) = lim (λ n → a * b n) (λ p → *-< (bw p))
*-< {a}{b} suc* = +< (a * b) a
*-< {a}(suc {b = c} q) = <-◾ (*-< q) (+< (a * c) a)
*-< {a} (lim* {b} {bw} n) = lim (suc n) (*-< (bw suc*))
*-< {a} {a = b} (lim {f} {fw = fw} n p) =
  lim (suc n) (*-< {a} {b}{f (suc n)} (<-◾ p (fw suc*)))

-- base ω exponentiation
ω₀^_     : O₁ → O₁; infixr 8 ω₀^_
ω₀^-not0 : ∀ a → not0 (ω₀^ a)
ω₀^<     : O₁-incr ω₀^_
ω₀^_ zero       = 1
ω₀^_ (suc a)    = _*_ (ω₀^ a) {{ω₀^-not0 a}} ω₀
ω₀^_ (lim a aw) = lim (ω₀^_ ∘ a) (λ p → ω₀^< (aw p))
ω₀^-not0 zero       = _
ω₀^-not0 (suc a)    = _
ω₀^-not0 (lim a aw) = _
ω₀^< {a} suc*  = lim* 1
ω₀^< (suc p)   = lim 1 (ω₀^< p)
ω₀^< (lim* n)  = lim* n
ω₀^< (lim n p) = lim n (ω₀^< p)

ε₀suc : ∀ n → iterℕ n ω₀^_ 0 < iterℕ (suc n) ω₀^_ 0
ε₀suc zero = suc*
ε₀suc (suc n) = ω₀^< (ε₀suc n)

ε₀-incr : lim-incr (λ n → iterℕ n ω₀^_ 0)
ε₀-incr {n} suc* = ε₀suc n
ε₀-incr (suc {m = m} p) = <-◾ (ε₀-incr p) (ε₀suc m)

ε₀ : O₁
ε₀ = lim (λ n → iterℕ n ω₀^_ 0) ε₀-incr

-- Classes of raw tree ordinals, indexed by well-formed countable ordinals.
--------------------------------------------------------------------------------

data O (l : O₁) (El : ∀ i → i < l → Set) : Set where
  zero : O l El
  suc  : O l El → O l El
  lim  : (ℕ → O l El) → O l El
  Lim  : ∀ i (p : i < l) → (El i p → O l El) → O l El

instance
  NumberO : ∀ {l El} → Number (O l El)
  NumberO .Number.Constraint _ = ⊤
  NumberO .Number.fromNat n    = iterℕ n suc zero

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

Limᵁ : ∀ {l} i (p : i < l) → (U i → U l) → U l
Limᵁ i p f = Lim i p (λ b → f (coe (El≡ p) b))

-- embedding into larger universe
⇑ : ∀ {l₁ l₂} → l₁ < l₂ → U l₁ → U l₂
⇑ p zero        = zero
⇑ p (suc a)     = suc (⇑ p a)
⇑ p (lim a)     = lim (⇑ p ∘ a)
⇑ p (Lim i q a) = Limᵁ _ (<-◾ q p) λ j → ⇑ p (a (coe (El≡ q ⁻¹) j))

iterᵁ : ∀ {l} → U l → (U l → U l) → U l → U l
iterᵁ zero        f = id
iterᵁ (suc a)     f = f ∘ iterᵁ a f
iterᵁ (lim a)     f = λ b → lim λ n → iterᵁ (a n) f b
iterᵁ (Lim i p a) f = λ b → Lim i p λ j → iterᵁ (a j) f b

_+ᵁ_ = λ {l} a b → iterᵁ {l} b suc a;           infixl 6 _+ᵁ_
_*ᵁ_ = λ {l} a b → iterᵁ {l} b (flip _+ᵁ_ a) 0; infixl 7 _*ᵁ_
_^ᵁ_ = λ {l} a b → iterᵁ {l} b (flip _*ᵁ_ a) 1; infixr 8 _^ᵁ_

ω₀ᵁ : ∀ {l} → U l
ω₀ᵁ = lim λ n → fromNat n

-- omega numbers
Ω : ∀ l → U l
Ω zero       = ω₀ᵁ
Ω (suc a)    = Limᵁ _ suc* (⇑ suc*)
Ω (lim a aw) = lim λ n → ⇑ (lim* n) (Ω (a n))

-- least fix point
lfp : ∀ {l} → (U l → U l) → U l
lfp f = lim λ n → iterℕ n f 0

-- "one-step" collapse
ψ< : ∀ {l i} → i < l → U l → U i
ψ< p zero    = lfp (Ω _ ^ᵁ_)
ψ< p (suc a) = lfp (ψ< p a ^ᵁ_)
ψ< p (lim a) = lim (ψ< p ∘ a)
ψ< p (Lim i q a) rewrite El≡ q with cmpO₁ q p
... | injᵃ r = Limᵁ _ r (ψ< p ∘ a)
... | injᵇ r = lfp (ψ< p ∘ a ∘ ⇑ r)
... | injᶜ r = lfp (ψ< p ∘ a ∘ tr U (r ⁻¹))

-- iterated collapse
ψ : ∀ l → U l → U 0
ψ zero       a = a
ψ (suc l)    a = ψ l (ψ< suc* a)
ψ (lim l lw) a = lim λ n → ψ (l n) (ψ< (lim* n) a)

-- fast-growing functions
f : U 0 → ℕ → ℕ
f zero    b = suc b
f (suc a) b = iterℕ b (f a) b
f (lim a) b = f (a b) b

ε₀ᵁ : ∀ {l} → U l
ε₀ᵁ = lfp (ω₀ᵁ ^ᵁ_)

-- Examples for countable ordinals
--------------------------------------------------------------------------------

-- Entries from:
--   https://en.wikipedia.org/wiki/Ordinal_collapsing_function
--   https://ncatlab.org/nlab/show/ordinal+analysis
ex1  = ω₀ᵁ                     -- ω₀
ex2  = ψ 1 0                   -- ε₀
ex3  = ψ 1 1                   -- ε₁
ex4  = ψ 1 2                   -- ε₂
ex5  = ψ 1 (Ω 1)               -- ζ₀
ex6  = ψ 1 (Ω 1 +ᵁ 1)          -- ζ₁
ex7  = ψ 1 (Ω 1 +ᵁ 2)          -- ζ₂
ex8  = ψ 1 (Ω 1 ^ᵁ Ω 1)        -- Γ₀ (Feferman-Schütte)
ex9  = ψ 1 (Ω 1 ^ᵁ Ω 1 ^ᵁ 2)   -- Ackermann
ex10 = ψ 1 (Ω 1 ^ᵁ Ω 1 ^ᵁ ω₀ᵁ) -- SVO (small Veblen ordinal)
ex11 = ψ 1 (Ω 1 ^ᵁ Ω 1 ^ᵁ Ω 1) -- LVO (large Veblen ordinal)
ex12 = ψ 2 0                   -- Bachmann-Howard
ex13 = ψ ω₀ (Ω ω₀)             -- ID<ω
ex14 = ψ ω₀ (Ω ω₀ *ᵁ ε₀ᵁ)      -- W-IDω
ex15 = ψ (ω₀ + 1) 0            -- Takeuti-Feferman-Buchholz
ex16 = ψ (ω₀^ ω₀) (Ω (ω₀^ ω₀)) -- ID<ω^ω
ex17 = ψ ε₀ (Ω ε₀)             -- ID<ε₀


-- a big number
mynum : ℕ
mynum = f ex17 99

{-
How does it compare to other? Considering numbers defined in computer programs,
Loader's number and its variants are definitely much bigger.

  https://googology.wikia.org/wiki/Loader%27s_number
  https://codegolf.stackexchange.com/questions/176966/golf-a-number-bigger-than-loaders-number

If we only consider numbers in total languages, then my number is likely the
biggest defined so far.
-}
