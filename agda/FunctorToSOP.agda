-- Turn a general polynomial functor description into a sum-of-products one

open import Data.Product
open import Relation.Binary.PropositionalEquality
open import Data.Unit
open import Data.List hiding ([_]) renaming (map to lmap)
open import Data.Empty
open import Data.Sum
open import Function
open import Category.Monad
open import Algebra

open module ListMonad {α} = RawMonad (Data.List.monad {α})
module LM {α}{A} = Monoid (monoid {α} A)

data U : Set where
  one   : U
  zero  : U
  rec   : U
  _*_   : U → U → U
  _+_   : U → U → U
  fix   : U → U

mutual
  ⟦_⟧ : U → Set → Set
  ⟦ one    ⟧ k = ⊤
  ⟦ zero   ⟧ k = ⊥
  ⟦ rec    ⟧ k = k
  ⟦ a * b  ⟧ k = ⟦ a ⟧ k × ⟦ b ⟧ k
  ⟦ a + b  ⟧ k = ⟦ a ⟧ k ⊎ ⟦ b ⟧ k
  ⟦ fix u  ⟧ k = μ u

  data μ : U → Set where
    ⟨_⟩ : ∀ {u} → ⟦ u ⟧ (μ u) → μ u

mutual
  data Field : Set where
    rec : Field
    fix : Sum → Field

  Prod = List Field
  Sum  = List Prod

  ⟦_⟧ₛ : Sum → Set → Set
  ⟦ []    ⟧ₛ k = ⊥
  ⟦ p ∷ s ⟧ₛ k = ⟦ p ⟧ₚ k ⊎ ⟦ s ⟧ₛ k

  ⟦_⟧ₚ : Prod → Set → Set
  ⟦ []        ⟧ₚ k = ⊤
  ⟦ rec   ∷ p ⟧ₚ k = k × ⟦ p ⟧ₚ k
  ⟦ fix s ∷ p ⟧ₚ k = μₛ s × ⟦ p ⟧ₚ k

  data μₛ : Sum → Set where
    ⟨_⟩ : ∀ {s} → ⟦ s ⟧ₛ (μₛ s) → μₛ s

_*ˢ_ : Sum → Sum → Sum
_*ˢ_ = ListMonad.zipWith _++_

nf : U → Sum
nf one     = [] ∷ []
nf zero    = []
nf rec     = (rec ∷ []) ∷ []
nf (a * b) = nf a *ˢ nf b
nf (a + b) = nf a ++ nf b
nf (fix u) = (fix (nf u) ∷ []) ∷ []

++ₚ : ∀ p {p' A} → ⟦ p ⟧ₚ A → ⟦ p' ⟧ₚ A → ⟦ p ++ p' ⟧ₚ A
++ₚ []          xs       ys = ys
++ₚ (rec ∷ p)   (x , xs) ys = x , ++ₚ p xs ys
++ₚ (fix s ∷ p) (x , xs) ys = x , ++ₚ p xs ys

_++^_ : ∀ {s A} → ⟦ s ⟧ₛ A → ∀ s'' → ⟦ s ++ s'' ⟧ₛ A
_++^_ {[]}    () _
_++^_ {p ∷ s} (inj₁ x) s'' = inj₁ x
_++^_ {p ∷ s} (inj₂ y) s'' = inj₂ (y ++^ s'')

_^++_ : ∀ {s A} s' → ⟦ s ⟧ₛ A → ⟦ s' ++ s ⟧ₛ A
_^++_ {[]}    s'' ()
_^++_ {_ ∷ _} []        x = x
_^++_ {_ ∷ _} (p ∷ s'') x = inj₂ (s'' ^++ x)

_,ₛ_ : ∀ {s s' A} → ⟦ s ⟧ₛ A → ⟦ s' ⟧ₛ A → ⟦ s *ˢ s' ⟧ₛ A
_,ₛ_ {[]}    {s'} () y
_,ₛ_ {p ∷ s} {[]}      (inj₁ x) ()
_,ₛ_ {p ∷ s} {p' ∷ s'} (inj₁ x) (inj₁ y) = inj₁ (++ₚ p x y)
_,ₛ_ {p ∷ s} {p' ∷ s'} (inj₁ x) (inj₂ y) = inj₂ (next ++^ _)
  where
    next : ⟦ (s' >>= λ p' → return (p ++ p')) ⟧ₛ _
    next = subst (λ x → ⟦ x ⟧ₛ _) (proj₂ LM.identity _)(_,ₛ_ {p ∷ []} (inj₁ x) y)
_,ₛ_ {p ∷ s} {s'} (inj₂ x) y = (s' >>= λ p' → return (p ++ p')) ^++ (x ,ₛ y)

mutual
  ⟦nf⟧ : ∀ {u} → μ u → μₛ (nf u)
  ⟦nf⟧ {u} ⟨ x ⟩ = ⟨ ⟦nf⟧' u x ⟩

  ⟦nf⟧' : ∀ u {u'} → ⟦ u ⟧ (μ u') → ⟦ nf u ⟧ₛ (μₛ (nf u'))
  ⟦nf⟧' one     x        = inj₁ x
  ⟦nf⟧' zero    x        = x
  ⟦nf⟧' rec     x        = inj₁ (⟦nf⟧ x , tt)
  ⟦nf⟧' (a * b) (x , y)  = ⟦nf⟧' a x ,ₛ ⟦nf⟧' b y
  ⟦nf⟧' (a + b) (inj₁ x) = ⟦nf⟧' a x ++^ nf b
  ⟦nf⟧' (a + b) (inj₂ y) = nf a ^++ ⟦nf⟧' b y
  ⟦nf⟧' (fix u) x        = inj₁ (⟦nf⟧ x , tt)

