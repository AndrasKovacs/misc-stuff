{-# OPTIONS --without-K #-}

open import Relation.Binary.PropositionalEquality
open import Data.Product

module _ (I : Set)(S : Set)(P : S → Set)(outer : S → I)(inner : ∀ s → P s → I) where

  -- assume ordinary W types
  data W  : Set where
    sup : ∀ s → (P s → W) → W

  -- indexed W algebras
  record IxWᴬ : Set₁ where
    field
      W'   : I → Set
      sup' : ∀ s → ((p : P s) → W' (inner s p)) → W' (outer s)
  open IxWᴬ

  -- displayed algebras
  record IxWᴰ (γ : IxWᴬ) : Set₁ where
    field
      W'ᴰ : ∀ i → W' γ i → Set
      sup'ᴰ : ∀ s (f : ∀ p → W' γ (inner s p))(fᴰ : ∀ p → W'ᴰ _ (f p)) → W'ᴰ (outer s) (sup' γ s f)
  open IxWᴰ

  -- sections of displayed algebras
  record IxWˢ (γ : IxWᴬ)(γᴰ : IxWᴰ γ) : Set where
    field
      W'ˢ   : ∀ i → (x : W' γ i) → W'ᴰ γᴰ i x
      sup'ˢ : ∀ s (f : ∀ p → W' γ (inner s p))
              → W'ˢ _ (sup' γ s f) ≡ sup'ᴰ γᴰ _ f (λ p → W'ˢ (inner s p) (f p))
  open IxWˢ

  -- well-indexing predicate over W types
  wf : W → I → Set
  wf (sup s f) i = (∀ p → wf (f p) (inner s p)) × (outer s ≡ i)

  -- candidate for initial IxW algebra
  initAlg : IxWᴬ
  initAlg = record {
    W'   = λ i → Σ W (λ w → wf w i);
    sup' = λ s f → (sup s (λ p → f p .proj₁)) , (λ p → f p .proj₂) , refl
    }

  -- for any displayed algebra over initAlg ...
  module _ (γᴰ : IxWᴰ initAlg) where

    eval : ∀ i (w : W)(p : wf w i) → W'ᴰ γᴰ i (w , p)
    eval _ (sup s f) (fp , refl) =
      sup'ᴰ γᴰ s (λ p → (f p) , (fp p)) (λ p → eval (inner s p) (f p) (fp p))

    -- ... we get a section of it
    sec : IxWˢ initAlg γᴰ
    sec = record {W'ˢ = λ {i (w , p) → eval i w p}; sup'ˢ = λ s f → refl}
