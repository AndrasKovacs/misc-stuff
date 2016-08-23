{-# OPTIONS --type-in-type #-}

open import Data.Nat hiding (_*_)
open import Data.List
open import Relation.Binary.PropositionalEquality
open import Data.Empty
open import Data.Product
open import Data.Sum
open import Function

{-
  Sum-of-products descriptions

  This construction removes the nesting ambiguity of σ-s of
  usual descriptions, and also removes the possibility of infinite
  sums at the topmost level of a description. This brings descriptions
  closer in looks and behavior to indexed family definitions as in Agda.

  We achieve this by having a sum-of-telescopes representation, where
  each of the inner telescopes have shapes independent of their σ-bound
  values.

  I haven't yet thought about how this could be useful.
-}

data Shape : Set where
  ret : Shape
  σ π ind : Shape → Shape

mutual
  data Prod I : Shape → Set where
    ret  : I → Prod I ret
    σ    : ∀ {s} A → (A → Prod I s) → Prod I (σ s)
    π    : ∀ {s} A → (A → Desc I) → Prod I s → Prod I (π s)
    ind  : ∀ {s} → I → Prod I s → Prod I (ind s)

  Desc : Set → Set
  Desc I = List (∃ (Prod I))

mutual
  ⟦_⟧ : ∀ {I} → Desc I → (I → Set) → (I → Set)
  ⟦ []         ⟧ F i = ⊥
  ⟦ p ∷ []     ⟧ F i = ⟦ proj₂ p ⟧ₚ F i
  ⟦ p ∷ p' ∷ d ⟧ F i = ⟦ proj₂ p ⟧ₚ F i ⊎ ⟦ p' ∷ d ⟧ F i

  -- we get annoying ⊥ cases in function definitions this way:
  -- ⟦ []    ⟧ F i = ⊥
  -- ⟦ p ∷ d ⟧ F i = ⟦ proj₂ p ⟧ₚ F i ⊎ ⟦ d ⟧ F i
  -- although it might be better for other (obvious) reasons

  ⟦_⟧ₚ : ∀ {I n} → Prod I n → (I → Set) → (I → Set)
  ⟦ ret j   ⟧ₚ F i = i ≡ j
  ⟦ σ A k   ⟧ₚ F i = ∃ λ a → ⟦ k a ⟧ₚ F i
  ⟦ π A B p ⟧ₚ F i = (∀ a → ⟦ B a ⟧ F i) × ⟦ p ⟧ₚ F i
  ⟦ ind j p ⟧ₚ F i = F j × ⟦ p ⟧ₚ F i

data μ {I} (D : Desc I) (i : I) : Set where
  ⟨_⟩ : ⟦ D ⟧ (μ D) i → μ D i

_*_ : ∀ {I s} → Set → Prod I s → Prod I (σ s)
A * p = σ A λ _ → p
infixr 5 _*_

Vec' : Set → Desc ℕ
Vec' A =
    (, ret 0)
  ∷ (, σ ℕ λ n → A * ind n (ret (suc n)))
  ∷ []

Vec = μ ∘ Vec'

pattern nil = ⟨ inj₁ refl ⟩
pattern cons {n} a as = ⟨ inj₂ (n , a , as , refl) ⟩

Vec-elim :
  ∀ {A}
  → (Vec*  : ∀ {n} → Vec A n → Set)
  → Vec* nil
  → (∀ {n as} a → Vec* as → Vec* (cons {n} a as))
  → ∀ {n} as → Vec* {n} as
Vec-elim Vec* nil* cons* nil         = nil*
Vec-elim Vec* nil* cons* (cons a as) = cons* a (Vec-elim Vec* nil* cons* as)





