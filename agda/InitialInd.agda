-- An initial Nat object also has induction

{-# OPTIONS --without-K #-}

open import Relation.Binary.PropositionalEquality
open import Data.Product
open import Function

record Nat : Set₁ where
  constructor con
  field
    C : Set
    z : C
    s : C → C
open Nat

record Nat⇒ (N N' : Nat) : Set₁ where
  constructor con
  open Nat
  field
    rec  : C N → C N'
    recz : rec (z N) ≡ z N'
    recs : ∀ n → rec (s N n) ≡ s N' (rec n)
open Nat⇒

Nat∘ : ∀ {N N' N'' : Nat} → Nat⇒ N' N'' → Nat⇒ N N' → Nat⇒ N N''
Nat∘ (con rec recz recs) (con rec₁ recz₁ recs₁) =
  con (rec ∘ rec₁) (trans (cong rec recz₁) recz)
  (λ n → trans (cong rec (recs₁ n)) (recs (rec₁ n)))

Nat-id : (N : Nat) → Nat⇒ N N
Nat-id (con C z s) = con id refl (λ n → refl)

record Initial (N : Nat) : Set₁ where
  constructor con
  field
    init : (N' : Nat) → Nat⇒ N N'
    univ : (N' : Nat) → (f : Nat⇒ N N') → f ≡ init N'
open Initial

init-id : (N : Nat)(iN : Initial N)(f : Nat⇒ N N) → f ≡ Nat-id N
init-id N i f = trans (univ i N f) (sym (univ i N (Nat-id N)))

rec-id : {N : Nat}(f : Nat⇒ N N) → f ≡ Nat-id N → rec f ≡ id
rec-id _ refl = refl

init-ind :
  (ℕ : Nat)(i : Initial ℕ)(P : C ℕ → Set) → (∀ n → P n → P (s ℕ n)) → P (z ℕ) → ∀ n → P n
init-ind ℕ i P ps pz n =
  subst P (cong (_$ n) (rec-id _ (init-id ℕ i fromTo))) (proj₂ (rec to n))
  where
    ℕP : Nat
    ℕP = con (∃ P) (z ℕ , pz) (λ {(n , pn) → (s ℕ n , ps n pn)})

    to : Nat⇒ ℕ ℕP
    to = init i ℕP

    from : Nat⇒ ℕP ℕ
    from = con proj₁ refl (λ n → refl)

    fromTo : Nat⇒ ℕ ℕ
    fromTo = Nat∘ from to

