
module FactorialIso.Main where

open import Data.Empty
open import Data.Fin hiding (_+_; _≤_; _<_; pred; compare)
open import Data.Fin.Properties renaming (_≟_ to _Fin-≟_)
open import Data.Nat
open import Data.Nat.Properties
open import Data.Product renaming (map to ×-map)
open import Data.Sum renaming (map to ⊎-map)
open import Data.Unit using (⊤; tt)
open import Data.Vec hiding (head; tail)
open import Function
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
import Relation.Binary.HeterogeneousEquality as H
import Level as L

module ≤ = DecTotalOrder (Data.Nat.decTotalOrder)

open import FactorialIso.ArithLemmas

_! : ℕ → ℕ
zero  ! = 1
suc n ! = suc n * n !

Fin' : ℕ → Set
Fin' n = ∃ λ x → x < n

Vec! : ∀ {n} → Vec ℕ n → Set
Vec! []               = ⊤
Vec! {suc n} (x ∷ xs) = x ≤ n × Vec! xs

ℕ! : ℕ → Set
ℕ! n = Σ (Vec ℕ n) Vec!

≤-prop : ∀ {a b} (p p' : a ≤ b) → p ≡ p'
≤-prop z≤n     z≤n      = refl
≤-prop (s≤s p) (s≤s p') = cong s≤s $ ≤-prop p p'

Vec!-prop : ∀ {n xs} (ps ps' : Vec! {n} xs) → ps ≡ ps'
Vec!-prop {xs = []} tt tt = refl
Vec!-prop {xs = x ∷ xs} (p , ps) (p' , ps')
  rewrite Vec!-prop ps ps' | ≤-prop p p' = refl

-- To
--------------------------------------------------------------------------------

to : ∀ {n} → Vec ℕ n → ℕ
to         []       = 0
to {suc n} (x ∷ xs) = to xs + x * n !

toOK : ∀ {n} (xs : Vec ℕ n) (ps : Vec! xs) → to {n} xs < n !
toOK [] _ = s≤s z≤n
toOK {suc n}(x ∷ xs) (p , ps) =
  (toOK xs ps) +-mono (p *-mono (≤.reflexive {(n !)} refl))

-- From 
--------------------------------------------------------------------------------

≤⇒< : ∀ {a b} → a ≤ b → a ≢ b → a < b
≤⇒< {b = zero}  z≤n      p2 = ⊥-elim (p2 refl)
≤⇒< {b = suc b} z≤n      p2 = s≤s z≤n
≤⇒<             (s≤s p1) p2 = s≤s (≤⇒< p1 (p2 ∘ cong suc))

divMod : ∀ n d → d ≢ 0 → ∃₂ λ m k → (n ≡ m + k * d) × (m < d)
divMod zero    zero    d≢0 = ⊥-elim (d≢0 refl)
divMod zero    (suc d) d≢0 = 0 , 0 , refl , s≤s z≤n
divMod (suc n) d       d≢0 with divMod n d d≢0
... | m , k , p1 , p2 with suc m ≟ d
divMod (suc n) .(suc m) d≢0 | m , k , p1 , p2 | yes refl
  = 0 , suc k , cong suc p1 , s≤s z≤n
... | no ¬eq
  = suc m , k , cong suc p1 , ≤⇒< p2 ¬eq

n!≢0 : ∀ n → n ! ≢ 0
n!≢0 zero ()
n!≢0 (suc n) x with n ! | inspect _! n
n!≢0 (suc n) x  | zero  | [ eq ] = n!≢0 n eq
n!≢0 (suc n) () | suc _ | [ eq ]

from : ∀ n → ℕ → Vec ℕ n
from zero    i = []
from (suc n) i with divMod i (n !) (n!≢0 n)
... | m , k , _ , _ = k ∷ from n m

fromOK : ∀ n (i : ℕ) (p : i < n !) → Vec! (from n i)
fromOK zero    i p = tt
fromOK (suc n) i p with divMod i (n !) (n!≢0 n)
fromOK (suc n) .(m + k * (n !)) p | m , k , refl , p2 = digit< p p2 , fromOK n m p2

-- Equivalences
--------------------------------------------------------------------------------

_~_ : ∀ {α β} → Set α → Set β → Set (α L.⊔ β)
A ~ B = ∃₂ λ (f : B → A) (g : A → B) → (∀ a → f (g a) ≡ a) × (∀ b → g (f b) ≡ b)

~sym : ∀ {α β A B} → _~_ {α}{β} A B → B ~ A
~sym (f , g , fg , gf) = g , f , gf , fg

~trans : ∀ {α β γ A B C} → _~_ {α}{β} A B → _~_ {β}{γ} B C → A ~ C
~trans (f , g , fg , gf) (f' , g' , fg' , gf') = f ∘ f' , g' ∘ g ,
  (λ a → trans (cong f (fg' (g a))) (fg a)) ,
  (λ b → trans (cong g' (gf (f' b))) (gf' b))

toFrom' : ∀ {n} i → i < n ! → to (from n i) ≡ i
toFrom' {zero} .0 (s≤s z≤n) = refl
toFrom' {suc n} i p with divMod i (n !) (n!≢0 n)
toFrom' {suc n} .(m + k * (n !)) p | m , k , refl , p2
 rewrite toFrom' {n} m p2 = refl

fromTo' : ∀ n xs (ps : Vec! xs) → from n (to xs) ≡ xs
fromTo' .0      []       ps       = refl
fromTo' (suc n) (x ∷ xs) (p , ps)
  with divMod (to xs + x * (n !)) (n !) (n!≢0 n) | toOK xs ps | fromTo' n xs ps
... | m , k , p1 , p2 | p3 | p4
  with mod-unique (to xs) m x k (n !) (n!≢0 n) p1 p3 p2
... | eq1 , eq2
  rewrite
    eq1 | eq2 | p4
  = refl

∃-≡ :
  ∀ {α β}{A : Set α}{B : A → Set β}
  → {a a' : A}{b : B a}{b' : B a'}  
  → (eq : a ≡ a') → subst B eq b ≡ b'
  → (Σ A B ∋ (a , b)) ≡ (a' , b')
∃-≡ refl refl = refl

eqv1 : ∀ {n} → Fin' (n !) ~ ℕ! n
eqv1 {n} = f , g , fg , gf where
  f : ℕ! n → Fin' (n !)
  f (xs , ps) = to xs , toOK xs ps

  g : Fin' (n !) → ℕ! n
  g (i , p) = from _ i , fromOK _ i p

  fg : ∀ a → f (g a) ≡ a
  fg (i , p) = ∃-≡ (toFrom' {n} i p) (≤-prop _ _)

  gf : ∀ b → g (f b) ≡ b
  gf (xs , ps) = ∃-≡ (fromTo' n xs ps) (Vec!-prop _ _)

eqv2 : ∀ {n} → Fin' n ~ Fin n
eqv2 {n} = Fin→Fin' , Fin'→Fin , fg , gf where

  Fin→Fin' : ∀ {n} → Fin n → Fin' n
  Fin→Fin' {zero} ()
  Fin→Fin' {suc n₁} zero   = zero , s≤s z≤n
  Fin→Fin' {suc n} (suc i) = ×-map suc s≤s (Fin→Fin' i)
  
  Fin'→Fin : ∀ {n} → Fin' n → Fin n
  Fin'→Fin {zero}   (i , ())
  Fin'→Fin {suc n₁} (zero , s≤s z≤n) = zero
  Fin'→Fin {suc n₁} (suc m , s≤s p)  = suc (Fin'→Fin (m , p))

  fg : ∀ {n} a → Fin→Fin' {n} (Fin'→Fin a) ≡ a
  fg {zero} (i , ())
  fg {suc n₁} (zero , s≤s z≤n) = refl
  fg {suc n₁} (suc m , s≤s p) rewrite fg (m , p) = refl

  gf : ∀ {n} b → Fin'→Fin {n} (Fin→Fin' b) ≡ b
  gf {zero} ()
  gf {suc n₁} zero   = refl
  gf {suc n} (suc b) = cong suc (gf b)


--------------------------------------------------------------------------------

Arrow! : ℕ → Set
Arrow! n = (i : Fin n) → Fin (suc (toℕ i))

shrink : ∀ {n} (i : Fin (suc n)) → (i ≡ fromℕ n) ⊎ (∃ λ i' → i ≡ inject₁ i')
shrink {zero} zero    = inj₁ refl
shrink {zero} (suc ())
shrink {suc n} zero    = inj₂ (zero , refl)
shrink {suc n} (suc i) = ⊎-map (cong suc) (×-map suc (cong suc)) (shrink i)

head : ∀ {n} → Arrow! (suc n) → Fin (suc n)
head {n} f = subst (Fin ∘ suc) (to-from n) (f (fromℕ n))

tail : ∀ {n} → Arrow! (suc n) → Arrow! n
tail {n} f i = subst (Fin ∘ suc) (inject₁-lemma i) (f (inject₁ i))

cons : ∀ {n} → Fin (suc n) → Arrow! n → Arrow! (suc n)
cons {n} x xs i with shrink i
cons {n} x xs i | inj₁ p =
  subst (Fin ∘ suc) (sym (trans (cong toℕ p) (to-from n))) x
cons x  xs i | inj₂ (i' , p) =
  subst (Fin ∘ suc) (sym (trans (cong toℕ p) (inject₁-lemma i'))) (xs i')

subst-cancel :
 ∀ {α β}{A : Set α}(P : A → Set β) {a a'}(p : a ≡ a')(x : P a)
 → x ≡ subst P (sym p) (subst P p x)
subst-cancel P refl x = refl

subst-cancel' :
 ∀ {α β}{A : Set α}(P : A → Set β) {a a'}(p : a ≡ a')(x : P a')
 → x ≡ subst P p (subst P (sym p) x)
subst-cancel' P refl x = refl 

cons-η : ∀ {n} (xs : Arrow! (suc n)) i → xs i ≡ cons (head xs) (tail xs) i
cons-η {n} xs i with shrink i
cons-η {n} xs .(fromℕ n) | inj₁ refl =
  subst-cancel (Fin ∘ suc) (to-from n) (xs (fromℕ n))
cons-η xs .(inject₁ i')  | inj₂ (i' , refl) =
  subst-cancel (Fin ∘ suc) (inject₁-lemma i') (xs (inject₁ i'))

Fin-pred : ∀ {n} → Fin (2 + n) → Fin (1 + n)
Fin-pred zero    = zero
Fin-pred (suc x) = x

fromℕ≢inject₁ : ∀ {n} (i : Fin n) → fromℕ n ≢ inject₁ i
fromℕ≢inject₁ zero ()
fromℕ≢inject₁ (suc i) eq = fromℕ≢inject₁ i (cong Fin-pred eq)

head-cons : ∀ {n} x xs → head {n} (cons x xs) ≡ x
head-cons {n} x xs with shrink (fromℕ n)
... | inj₁ refl     = sym (subst-cancel' (Fin ∘ suc) (to-from n) x)
... | inj₂ (i' , p) = ⊥-elim (fromℕ≢inject₁ i' p)

tail-cons : ∀ {n} x xs i → tail (cons {n} x xs) i ≡ xs i
tail-cons {n} x xs i with shrink (inject₁ i)
... | inj₁ p        = ⊥-elim (fromℕ≢inject₁ i (sym p))
... | inj₂ (i' , p) =
  H.≅-to-≡
   (H.trans
     (H.trans
       (H.≡-subst-removable
         (Fin ∘ suc)
         (inject₁-lemma i)
         (subst
           (Fin ∘ suc)
           (sym (trans (cong toℕ p) (inject₁-lemma i')))
           (xs i')))
       (H.≡-subst-removable
         (Fin ∘ suc)
         (sym (trans (cong toℕ p) (inject₁-lemma i')))
         (xs i')))
     (H.sym $ H.cong xs $
       H.≡-to-≅ $ toℕ-injective $
       subst₂ _≡_ (inject₁-lemma i) (inject₁-lemma i') (cong toℕ p)))

fromℕ≤-prop-toℕ-≤ : ∀ {n} (i : Fin (suc n)) → fromℕ≤ (s≤s (prop-toℕ-≤ i)) ≡ i
fromℕ≤-prop-toℕ-≤ zero    = refl
fromℕ≤-prop-toℕ-≤ {zero} (suc ())
fromℕ≤-prop-toℕ-≤ {suc n} (suc i) = cong suc (fromℕ≤-prop-toℕ-≤ i)

ixcong₂ :
  ∀ {α β}{I : Set α}{A B : I → I → Set β}{i1 i2 i1' i2'}{x : A i1 i2}{y : A i1' i2'}
  → (f : I → I)
  → (g : ∀ {i i'} → A i i' → B (f i) (f i'))
  → i1 ≡ i1'
  → i2 ≡ i2'
  → x H.≅ y → g x H.≅ g y
ixcong₂ f g refl refl H.refl = H.refl


prop-toℕ-≤-fromℕ≤ : ∀ {n m} (p : n ≤ m) → prop-toℕ-≤ (fromℕ≤ (s≤s p)) H.≅ p
prop-toℕ-≤-fromℕ≤ z≤n     = H.refl
prop-toℕ-≤-fromℕ≤ (s≤s p) =
  ixcong₂ {I = ℕ}{_≤_}{_≤_} suc s≤s (toℕ-fromℕ≤ (s≤s p)) refl (prop-toℕ-≤-fromℕ≤ p)

eqv3 : ∀ {n} → Arrow! n ~ ℕ! n
eqv3 {n} = f , g , fg , gf where

  postulate funext : ∀ {α β} → Extensionality α β

  f : ∀ {n} → ℕ! n → Arrow! n
  f {zero}  (xs , ps)         = λ ()
  f {suc n} (x ∷ xs , p , ps) = cons (fromℕ≤ (s≤s p)) (f {n} (xs , ps))

  g : ∀ {n} → Arrow! n → ℕ! n
  g {zero}  xs = [] , tt
  g {suc n} xs =
    toℕ (head xs) ∷ proj₁ (g (tail xs)) ,
    prop-toℕ-≤ (head xs) , proj₂ (g (tail xs))

  fg : ∀ {n} a → f {n} (g a) ≡ a
  fg {zero}  xs = funext (λ ())
  fg {suc n} xs =
    subst
      (λ x → cons (fromℕ≤ (s≤s (prop-toℕ-≤ (head xs)))) x ≡ xs)
      (sym $ fg (tail xs)) $
    subst
      (λ x → cons x (tail xs) ≡ xs)
      (sym $ fromℕ≤-prop-toℕ-≤ (head xs))
      (sym $ funext (cons-η xs))

  gf : ∀ {n} b → g {n} (f b) ≡ b
  gf {zero}  ([] , tt)          = refl
  gf {suc n} (x ∷ xs , p , ps)
    rewrite
      head-cons (fromℕ≤ (s≤s p)) (f (xs , ps))
    | funext (tail-cons (fromℕ≤ (s≤s p)) (f (xs , ps)))
    | gf (xs , ps)
    = ∃-≡ (cong (flip _∷_ xs)
      (toℕ-fromℕ≤ (s≤s p)))
      (H.≅-to-≡ (
        H.trans
          (H.≡-subst-removable
            Vec!
            (cong (flip _∷_ xs) (toℕ-fromℕ≤ (s≤s p)))
            (prop-toℕ-≤ (fromℕ≤ (s≤s p)) , ps))
            (ixcong₂ {I = ℕ} {_≤_} {λ x₁ y → x₁ ≤ y × Vec! xs} id
               (λ p₁ → p₁ , ps) (toℕ-fromℕ≤ (s≤s p)) refl (prop-toℕ-≤-fromℕ≤ p))))

--------------------------------------------------------------------------------

main : ∀ {n} → ((i : Fin n) → Fin (suc (toℕ i))) ~ Fin (n !)
main {n} = ~trans eqv3 (~trans (~sym eqv1) eqv2)

