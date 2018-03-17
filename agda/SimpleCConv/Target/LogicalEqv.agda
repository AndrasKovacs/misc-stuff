
module Target.LogicalEqv where

open import Lib
open import Target.Syntax

infix 4 _≈_
_≈_ : ∀ {A} → Tm ∙ A → Tm ∙ A → Set
_≈_ {𝔹}      t u = t ~ u
_≈_ {Top}    t u = ⊤
_≈_ {A * B}  t u = (π₁ t ≈ π₁ u) × (π₂ t ≈ π₂ u)
_≈_ {A ⇒⁺ B} t u = ∀ {a a'} → a ≈ a' → app⁺ t a ≈ app⁺ u a'
_≈_ {A ⇒ B}  t u = ∀ {a a'} → a ≈ a' → app t a ≈ app u a'

infix 6 _≈⁻¹
_≈⁻¹ : ∀ {A}{t t' : Tm ∙ A} → t ≈ t' → t' ≈ t
_≈⁻¹ {𝔹}      p       = p ~⁻¹
_≈⁻¹ {Top}    p       = p
_≈⁻¹ {A * B}  (p , q) = (p ≈⁻¹) , (q ≈⁻¹)
_≈⁻¹ {A ⇒ B}  p       = λ q → p (q ≈⁻¹) ≈⁻¹
_≈⁻¹ {A ⇒⁺ B} p       = λ q → p (q ≈⁻¹) ≈⁻¹

infixr 4 _≈◾_
_≈◾_ : ∀ {A}{t t' t'' : Tm ∙ A} → t ≈ t' → t' ≈ t'' → t ≈ t''
_≈◾_ {𝔹}     p q = p ~◾ q
_≈◾_ {A ⇒ B} p q = λ r → p r ≈◾ q (r ≈⁻¹ ≈◾ r)
_≈◾_ {A ⇒⁺ B} p q = λ r → p r ≈◾ q (r ≈⁻¹ ≈◾ r)
_≈◾_ {Top} p q = p
_≈◾_ {A * B} (p , q) (r , s) = (p ≈◾ r) , (q ≈◾ s)
