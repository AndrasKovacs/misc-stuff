{-# OPTIONS --without-K #-}

open import Relation.Binary.PropositionalEquality
open import Data.Product

data W (S : Set)(P : S → Set) : Set where
  sup : ∀ s → (P s → W S P) → W S P

module _ (I : Set)(S : Set)(P : S → Set)(out : S → I)(ins : ∀ s → P s → I) where

  record Wᴬ : Set₁ where
    field
      W'   : I → Set
      sup' : ∀ s → ((p : P s) → W' (ins s p)) → W' (out s)
  open Wᴬ

  record Wᴰ (γ : Wᴬ) : Set₁ where
    field
      W'ᴰ : ∀ i → W' γ i → Set
      sup'ᴰ : ∀ s (f : ∀ p → W' γ (ins s p))(fᴰ : ∀ p → W'ᴰ _ (f p)) → W'ᴰ (out s) (sup' γ s f)
  open Wᴰ

  record Wˢ (γ : Wᴬ)(γᴰ : Wᴰ γ) : Set where
    field
      W'ˢ   : ∀ i → (x : W' γ i) → W'ᴰ γᴰ i x
      sup'ˢ : ∀ s (f : ∀ p → W' γ (ins s p))
              → W'ˢ _ (sup' γ s f) ≡ sup'ᴰ γᴰ _ f (λ p → W'ˢ (ins s p) (f p))
  open Wˢ

  wf : W S P → I → Set
  wf (sup s f) i = (∀ p → wf (f p) (ins s p)) × (out s ≡ i)

  syn : Wᴬ
  syn = record {
    W'   = λ i → Σ (W S P) (λ w → wf w i);
    sup' = λ s f → (sup s (λ p → f p .proj₁)) , (λ p → f p .proj₂) , refl
    }

  module _ (γᴰ : Wᴰ syn) where

    eval : ∀ i (w : W S P)(p : wf w i) → W'ᴰ γᴰ i (w , p)
    eval _ (sup s f) (fp , refl) =
      sup'ᴰ γᴰ s (λ p → (f p) , (fp p)) (λ p → eval (ins s p) (f p) (fp p))

    sec : Wˢ _ γᴰ
    sec = record {W'ˢ = λ {i (w , p) → eval i w p}; sup'ˢ = λ s f → refl}
