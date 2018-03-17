
module Source.LogicalEqv where

open import Lib
open import Source.Syntax

infix 4 _≈_
_≈_ : ∀ {A} → Tm ∙ A → Tm ∙ A → Set
_≈_ {𝔹}     t u = t ~ u
_≈_ {A ⇒ B} t u = ∀ {a a'} → a ≈ a' → app t a ≈ app u a'

infix 6 _≈⁻¹
_≈⁻¹ : ∀ {A}{t t' : Tm ∙ A} → t ≈ t' → t' ≈ t
_≈⁻¹ {𝔹}     p = p ~⁻¹
_≈⁻¹ {A ⇒ B} p = λ q → p (q ≈⁻¹) ≈⁻¹

infixr 4 _≈◾_
_≈◾_ : ∀ {A}{t t' t'' : Tm ∙ A} → t ≈ t' → t' ≈ t'' → t ≈ t''
_≈◾_ {𝔹}     p q = p ~◾ q
_≈◾_ {A ⇒ B} p q = λ r → p r ≈◾ q (r ≈⁻¹ ≈◾ r)

postulate
  ≈refl    : ∀ {A}(t : Tm ∙ A) → t ≈ t
  canonic𝔹 : (t : Tm ∙ 𝔹) → (t ~ true) ⊎ (t ~ false)
  canonic⇒ : ∀ {A B} → (t : Tm ∙ (A ⇒ B)) → ∃ λ t' → t ~ lam t'
