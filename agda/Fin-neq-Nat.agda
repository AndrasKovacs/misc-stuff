open import Data.Fin hiding (_<_; _≤_)
open import Data.Nat
open import Function
open import Data.Product renaming (map to pmap)
open import Data.List renaming (map to lmap)
open import Relation.Binary.PropositionalEquality
open import Data.Empty
open import Relation.Nullary
open import Relation.Binary
open import Data.Sum renaming (map to smap)
import Level as L

module ≤ = DecTotalOrder Data.Nat.decTotalOrder

data _∈_ {A : Set} (a : A) : List A → Set where
  here  : ∀ {as} → a ∈ (a ∷ as)
  there : ∀ {a' as} → a ∈ as → a ∈ (a' ∷ as)

Finite : Set → Set
Finite A = ∃ λ as → ∀ (a : A) → a ∈ as

<-trans : ∀ {a b c} → a < b → b < c → a < c
<-trans {zero} (s≤s p1) (s≤s p2) = s≤s z≤n
<-trans {suc a} (s≤s p1) (s≤s p2) = s≤s (<-trans p1 p2)

<-suc : ∀ {a b} → a < b → a < suc b
<-suc {zero} (s≤s p) = s≤s z≤n
<-suc {suc a} (s≤s p) = s≤s (<-suc p)

¬≤ : ∀ {a b} → ¬ (a ≤ b) → b < a
¬≤ {zero}          p = ⊥-elim (p z≤n)
¬≤ {suc a} {zero}  p = s≤s z≤n
¬≤ {suc a} {suc b} p = s≤s (¬≤ (λ z → p (s≤s z)))

<-irrefl : ∀ {n} → ¬ (n < n)
<-irrefl {zero} ()
<-irrefl {suc n} (s≤s x) = <-irrefl x

lem : (xs : List ℕ) → ∃ λ n → ∀ {n'} → n' ∈ xs → n' < n
lem [] = zero , (λ {x} → λ ())
lem (x ∷ xs) with lem xs
lem (x ∷ xs) | out , p with suc out ≤.≤? x
lem (x ∷ xs) | out , p₁ | yes p = suc x , lem' where
  lem' : {n' : ℕ} → n' ∈ (x ∷ xs) → suc n' ≤ suc x
  lem' here       = ≤.refl
  lem' (there el) = <-trans (p₁ el) (<-suc p)  
lem (x ∷ xs) | out , p  | no ¬p = suc out , lem' where
  lem' : {n' : ℕ} → n' ∈ (x ∷ xs) → suc n' ≤ suc out
  lem' here       = ¬≤ ¬p
  lem' (there el) = <-suc (p el)

∈-map : ∀ {A B : Set}{x}{xs : List A}(f : A → B) → x ∈ xs → f x ∈ lmap f xs
∈-map {xs = []} f ()
∈-map {xs = ._ ∷ xs} f here = here
∈-map {xs = a' ∷ xs} f (there p) = there (∈-map f p)

Fin-shrink : ∀ {n} (a : Fin (suc n)) → (a ≡ fromℕ n) ⊎ (∃ λ a' → a ≡ inject₁ a')
Fin-shrink {zero} zero = inj₁ refl
Fin-shrink {zero} (suc ())
Fin-shrink {suc n} zero = inj₂ (zero , refl)
Fin-shrink {suc n} (suc a) = smap (cong suc) (pmap suc (cong suc)) (Fin-shrink a)

Fin-finite : ∀ n → Finite (Fin n)
Fin-finite zero    = [] , (λ ())
Fin-finite (suc n) with Fin-finite n
... | xs , p = fromℕ n ∷ lmap inject₁ xs , lem' where
  lem' : (a : Fin (suc n)) → a ∈ (fromℕ n ∷ lmap inject₁ xs)
  lem' a with Fin-shrink a
  lem' ._ | inj₁ refl = here
  lem' .(inject₁ a') | inj₂ (a' , refl) = there (∈-map inject₁ (p a'))

Fin≢ℕ : ∀ n → Fin n ≢ ℕ
Fin≢ℕ n p with subst Finite p (Fin-finite n)
... | ns , inj with lem ns
... | out , pout = <-irrefl (pout (inj out))