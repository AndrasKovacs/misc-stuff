
{-# OPTIONS --without-K #-}

open import Data.Fin hiding (_+_)
open import Data.Nat
open import Data.Nat.Properties
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Data.Product
open import Function hiding (Injective; Injection)
open import Data.Empty

Injective : ∀{α β}{A : Set α}{B : Set β} → (A → B) → Set _
Injective f = ∀ {a a'} → f a ≡ f a' → a ≡ a'

Injection : ∀ {α β} → Set α → Set β → Set _
Injection A B = ∃ (Injective {A = A}{B})

fpred : ∀ {n} → Fin (2 + n) → Fin (1 + n)
fpred zero    = zero
fpred (suc x) = x

suc-inj : ∀ {n} → Injective (Fin.suc {n})
suc-inj {zero} {()} p
suc-inj {suc n} p = cong fpred p

suc≢zero : ∀ {n} a → (Fin (suc n) ∋ suc a) ≢ zero
suc≢zero a ()

shift :  ∀ {a}(x' x : Fin (suc a)) → x ≢ x' → Fin a
shift         zero     (suc x) x≢x' = x
shift {suc a} (suc x') zero    x≢x' = zero
shift {suc a} (suc x') (suc x) x≢x' = suc (shift x' x (x≢x' ∘ cong suc))
shift         zero     zero    x≢x' = ⊥-elim (x≢x' refl)

shift-inj : ∀ {a} (x x₁ x₂ : Fin (suc a)) x₁≢x x₂≢x → shift x x₁ x₁≢x ≡ shift x x₂ x₂≢x → x₁ ≡ x₂
shift-inj         zero     (suc x₁) (suc .x₁) x₁≢x x₂≢x refl = refl
shift-inj         (suc x)  zero     zero      x₁≢x x₂≢x eq   = refl
shift-inj {suc a} (suc x)  (suc x₁) (suc x₂)  x₁≢x x₂≢x eq   =
  cong suc (shift-inj x x₁ x₂ (x₁≢x ∘ cong suc) (x₂≢x ∘ cong suc) (suc-inj eq))
shift-inj         zero     zero     x₂        x₁≢x x₂≢x eq   = ⊥-elim (x₁≢x refl)
shift-inj         zero     (suc x₁) zero      x₁≢x x₂≢x eq   = ⊥-elim (x₂≢x refl)
shift-inj {zero}  (suc ()) zero     (suc x₂)  x₁≢x x₂≢x eq

shrink : ∀ a b → Injection (Fin (suc a)) (Fin (suc b)) → Injection (Fin a) (Fin b)
shrink a b (f , inj) = f' , inj' where

  f' : Fin a → Fin b
  f' x = shift (f zero) (f (suc x)) (suc≢zero x ∘ inj)

  inj' : Injective f'
  inj' {x}{x'} = suc-inj ∘ inj ∘ f-eq where
    x≢f0  = suc≢zero x ∘ inj
    x'≢f0 = suc≢zero x' ∘ inj
    f-eq  = shift-inj (f zero) (f (suc x)) (f (suc x')) x≢f0 x'≢f0

¬suc-inj : ∀ a → ¬ Injection (Fin (suc a)) (Fin a)
¬suc-inj zero    (f , _) with f zero
... | ()
¬suc-inj (suc a) inj = ¬suc-inj a (shrink _ _ inj)

¬plus-inj : ∀ a b → ¬ Injection (Fin (suc (b + a))) (Fin a)
¬plus-inj a zero    inj     = ¬suc-inj a inj
¬plus-inj a (suc b) (f , p) = ¬plus-inj a b (f ∘ suc , suc-inj ∘ p)

Fin-inj : Injective Fin
Fin-inj {a} {b} eq with Data.Nat.compare a b
Fin-inj eq | equal _ = refl
Fin-inj eq | less a k rewrite +-comm a k =
  ⊥-elim $ ¬plus-inj a k $ subst (flip Injection (Fin a)) eq (id , id)
Fin-inj eq | greater b k rewrite +-comm b k =
  ⊥-elim $ ¬plus-inj b k $ subst (flip Injection (Fin b)) (sym eq) (id , id)
