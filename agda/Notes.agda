
{-# OPTIONS --type-in-type --without-K #-}

open import Relation.Binary.PropositionalEquality

J : ∀ A (a : A)(P : ∀ a' → a ≡ a' → Set) → P a refl → ∀ a' p → P a' p
J A a P Prefl .a refl = Prefl

transport : ∀ {A}{a a' : A}(P : A → Set) → a ≡ a' → P a → P a'
transport {A}{a}{a'} P p pa = J A a (λ a' _ → P a') pa a' p

Jᴾ :
  ∀ A (Aᴾ : A → Set)
    a (aᴾ : Aᴾ a)
    (P : ∀ a' → a ≡ a' → Set)
    (Pᴾ : (a' : A)(a'ᴾ : Aᴾ a')(p : a ≡ a')(pᴾ : transport Aᴾ p aᴾ ≡ a'ᴾ) → P a' p → Set)
    (Prefl : P a refl)
    (Preflᴾ : Pᴾ a aᴾ refl refl Prefl)
    (a' : A)(a'ᴾ : Aᴾ a')
    (p : a ≡ a')(pᴾ : transport Aᴾ p aᴾ ≡ a'ᴾ)
  → Pᴾ a' a'ᴾ p pᴾ (J A a P Prefl a' p)
Jᴾ A Aᴾ a aᴾ P Pᴾ Prefl Preflᴾ a' a'ᴾ p pᴾ =
  J A a (λ a' p → ∀ a'ᴾ pᴾ → Pᴾ a' a'ᴾ p pᴾ (J A a P Prefl a' p))
    (λ a'ᴾ pᴾ → J (Aᴾ a) aᴾ (λ a'ᴾ pᴾ → Pᴾ a a'ᴾ refl pᴾ Prefl) Preflᴾ a'ᴾ pᴾ)
    a' p a'ᴾ pᴾ




