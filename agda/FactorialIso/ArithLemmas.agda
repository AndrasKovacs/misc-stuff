
module FactorialIso.ArithLemmas where

open import Data.Nat
open import Data.Nat.Properties
open import Data.Nat.Properties.Simple
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Data.Product
open import Data.Empty
open import Relation.Nullary
open import Function

open SemiringSolver

≤-sum : ∀ a b → a ≤ b → ∃ λ c → b ≡ a + c
≤-sum .0 b z≤n    = b , refl
≤-sum _ _ (s≤s p) with ≤-sum _ _ p
... | b , p' = b , cong suc p'

+-inj : ∀ {a b} c → c + a ≡ c + b → a ≡ b
+-inj zero    p = p
+-inj (suc c) p = +-inj c (cong pred p)

≤-+-elim : ∀ {a b} → a + b ≤ a → b ≡ 0
≤-+-elim {zero}  z≤n     = refl
≤-+-elim {suc a} (s≤s p) = ≤-+-elim p

-- Lemma for digit bounds
--------------------------------------------------------------------------------

digit< : ∀ {a b c d} → a + b * c < c + d * c → a < c → b ≤ d
digit< {a}{b}{c}{d} p1 p2 with b ≤? d
... | yes p   = p
... | no  nle with ≤-sum _ _ $ ≰⇒> nle
digit< {a} {.(suc (d + b'))} {c} {d} p1 p2 | no nle | b' , refl
  rewrite
    solve 4
      (λ a c d b' → a :+ (c :+ (d :+ b') :* c) := c :+ d :* c :+ (a :+ b' :* c))
      refl (suc a) c d b'
  with ≤-+-elim p1
... | ()  

-- Modular decomposition is unique
--------------------------------------------------------------------------------

lem1 : ∀ m m' d → m ≤ d → m' ≤ d → suc m + d ≢ m'
lem1 .0 .0       d       z≤n z≤n       ()
lem1 .0 (suc m') (suc d) z≤n (s≤s pm') eq = lem1 0 m' d z≤n pm' (cong pred eq)
lem1 _ .0 _ (s≤s pm) z≤n ()
lem1 (suc m) (suc m') (suc d) (s≤s pm) (s≤s pm') eq rewrite sym $ +-suc m (suc d) =
  lem1 m (suc m') (suc (suc d)) (≤-step $ ≤-step pm) (≤-step $ s≤s pm') eq

lem :
  ∀ m m' k k' d
  → m + suc (d + (k' + k) * suc d) ≡ m' + k' * suc d
  → m ≤ d
  → m' ≰ d
lem m m' k k' d eq pm pm'
  rewrite
    solve 4
      (λ m d k k' →
        m :+ ((con 1 :+ d) :+ (k' :+ k) :* (con 1 :+ d)) :=
        k' :* (con 1 :+ d) :+ ((con 1 :+ m) :+ (k :+ d :* k :+ d)))
      refl m d k k'
  | +-comm m' (k' * suc d)      
  = lem1 m m'
       (k + d * k + d)
       (≤-steps (k + d * k) pm)
       (≤-steps (k + d * k) pm')
       (+-inj (k' * suc d) eq)

mod-unique' :
  ∀ m m' k k' d
  → m + k * suc d ≡ m' + k' * suc d
  → m ≤ d → m' ≤ d
  → m ≡ m' × k ≡ k'
mod-unique' m m' k k' d eq pm pm' with compare k k'
mod-unique' m m' k' .k' d eq pm pm' | equal .k'
  rewrite +-comm m (k' * suc d) | +-comm m' (k' * suc d) = +-inj (k' * suc d) eq , refl
mod-unique' m₁ m' m .(suc (m + k)) d eq pm pm'  | less    .m k
  = ⊥-elim (lem m' m₁ k m d (sym eq) pm' pm)
mod-unique' m m' .(suc (k' + k)) k' d eq pm pm' | greater .k' k
  = ⊥-elim (lem m m' k k' d eq pm pm')

mod-unique :
  ∀ m m' k k' d
  → d ≢ 0
  → m + k * d ≡ m' + k' * d
  → m < d → m' < d
  → m ≡ m' × k ≡ k'
mod-unique m m' k k' zero    d≢0 eq pm pm' = ⊥-elim (d≢0 refl)
mod-unique m m' k k' (suc d) d≢0 eq (s≤s pm) (s≤s pm') =
  mod-unique' m m' k k' d eq pm pm'

