
{-# OPTIONS --without-K #-}

module PropTrunc where
open import Lib

-- private
--   postulate
--       _⊢>_ : ∀ {α}{A : Set α} → A → A → Set α
--   {-# BUILTIN REWRITE _⊢>_ #-}

postulate
  ∣_∣   : ∀ {α} → Set α → Set α
  embed : ∀ {α}{A : Set α} → A → ∣ A ∣
  trunc : ∀ {α}{A : Set α}(x y : ∣ A ∣) → x ≡ y
  ∣∣-rec :
    ∀ {α β}{A : Set α}{P : Set β}
    → (A → P) → ((x y : P) → x ≡ y) → ∣ A ∣ → P

postulate
  ∣∣-rec-embed :
    ∀ {α β A P embedᴾ truncᴾ a} → ∣∣-rec {α}{β}{A}{P} embedᴾ truncᴾ (embed a) ≡ embedᴾ a
-- {-# REWRITE ∣∣-rec-embed #-}

postulate
  ∣∣-rec-trunc :
    ∀ {α β A P embedᴾ truncᴾ x y}
    → (∣∣-rec {α}{β}{A}{P} embedᴾ truncᴾ & (trunc x y))
    ≡ truncᴾ (∣∣-rec embedᴾ truncᴾ x) (∣∣-rec embedᴾ truncᴾ y)

infixl 9 _∣&∣_
infixl 8 _∣⊗∣_

_∣&∣_ : ∀ {α β}{A : Set α}{B : Set β} → (A → B) → ∣ A ∣ → ∣ B ∣
_∣&∣_ f a = ∣∣-rec (embed ∘ f) trunc a

_∣⊗∣_ : ∀ {α β}{A : Set α}{B : Set β} → ∣ (A → B) ∣ → ∣ A ∣ → ∣ B ∣
_∣⊗∣_ f a = ∣∣-rec (λ f → ∣∣-rec (λ a → embed (f a)) trunc a) trunc f
