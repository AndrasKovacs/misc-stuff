{-# OPTIONS --without-K #-}

-- Type families and "fibration"-s are equivalent

module FibrationEqv where

open import Data.Product
open import Basics

TyFam : Set → Set _
TyFam A = A → Set

Fib : Set → Set _
Fib A = Σ Set λ I → I → A

eq : TyFam ≡ Fib
eq = funext λ A → ua (f , g , fg , gf) where

  g : ∀ {A} → TyFam A → Fib A
  g f = ∃ f , proj₁

  f : ∀ {A} → Fib A → TyFam A
  f (E , proj) a = Σ E λ e → proj e ≡ a

  fg : ∀ {A} (x : A → Set) → f (g x) ≡ x
  fg {A} f = funext λ a → ua (f' a , g' a , fg' a , gf' a)
    where
      f' : ∀ a → f a → Σ (Σ A f) (λ e → proj₁ e ≡ a)
      f' a fa = (a , fa) , refl

      g' : ∀ a → Σ (Σ A f) (λ e → proj₁ e ≡ a) → f a
      g' a ((.a , fa) , refl) = fa

      fg' : ∀ a x → f' a (g' a x) ≡ x
      fg' a ((.a , fa') , refl) = refl

      gf' : ∀ a x → g' a (f' a x) ≡ x
      gf' a fa = refl

  gf : ∀ {A}(x : Σ Set λ E → E → A) → g (f x) ≡ x
  gf {A}(E , proj) =
    ⟵ Σ-≡ ((ua eqvA) , funext λ e → ap (λ f → f proj₁ e) (coe-post-∘ eqvA))
    where
      f' : E → ∃ (f (E , proj))
      f' e = proj e , e , refl

      g' : ∃ (f (E , proj)) → E
      g' (a , e , p) = e

      eqvA : ∃ (f (E , proj)) ~ E
      eqvA = (f' , g' , (λ {(_ , _ , refl) → refl}) , (λ _ → refl))
