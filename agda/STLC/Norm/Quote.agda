
{-# OPTIONS --without-K --no-eta --rewriting #-}

module SetoidSimple.Norm.Quote where

open import lib

open import SetoidSimple.Syntax
open import SetoidSimple.Norm.Model
open import SetoidSimple.Elim
open import SetoidSimple.Nf

open DModel M

mutual
  q : ∀ {Γ} A (t : Tm Γ A) → ElimTy M A t → Σ (Nf Γ A) λ t' → ⌜ t' ⌝ ≡ t
  q ι       t tᴹ = tᴹ
  q (A ⇒ B) t tᴹ = let (tₙ , ptₙ) = q B (app t) {!!} in lamₙ tₙ , {!!}

  -- Problem !! : need weakening to be able to apply to "π₂ id"

  u : ∀ {Γ} A (n : Ne Γ A) → ElimTy M A ⌜ n ⌝ne
  u ι       n      = ne n , refl
  u (A ⇒ B) n a aᴹ = let (aₙ , paₙ) = q A a aᴹ
    in coe (ap (λ a → ElimTy M B (⌜ n ⌝ne $ a)) paₙ) (u B (n $ₙ aₙ))

