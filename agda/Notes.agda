
{-# OPTIONS --without-K #-}

open import Data.Empty
open import Data.Unit
open import Data.Bool
open import Data.Nat
open import Data.Product
open import Relation.Binary.PropositionalEquality

data Type′ (U : Set) (El : U → Set) : Set
⟦_⟧′ : {U : Set} {El : U → Set} → Type′ U El → Set

data Type′ U El where
  `Type : Type′ U El
  `⟦_⟧ : U → Type′ U El
  `⊥ `⊤ `Bool : Type′ U El
  `Π `Σ : (τ : Type′ U El) (τ′ : ⟦ τ ⟧′ → Type′ U El) → Type′ U El

⟦_⟧′ {U = U} `Type = U
⟦_⟧′ {El = El} `⟦ τ ⟧ = El τ
⟦ `⊥ ⟧′ = ⊥
⟦ `⊤ ⟧′ = ⊤
⟦ `Bool ⟧′ = Bool
⟦ `Π τ τ′ ⟧′ = (v : ⟦ τ ⟧′) → ⟦ τ′ v ⟧′
⟦ `Σ τ τ′ ⟧′ = Σ ⟦ τ ⟧′ λ v → ⟦ τ′ v ⟧′

Type : {n : ℕ} → Set
_⟦_⟧ : (n : ℕ) → Type {n} → Set

Type {zero}  = Type′ ⊥ ⊥-elim
Type {suc n} = Type′ (Type {n}) (_⟦_⟧ n)

_⟦_⟧ (zero)  e = ⟦ e ⟧′
_⟦_⟧ (suc n) e = ⟦ e ⟧′

------------------------------------------------------------

idt : ∀ {U El} → Type′ U El
idt = `Π `Type λ A → `Π `⟦ A ⟧ λ _ → `⟦ A ⟧

id : ∀ {n} → suc n ⟦ idt ⟧
id = λ A x → x
