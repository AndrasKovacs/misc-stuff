{-# OPTIONS --without-K #-}

module Syntax where

open import Lib

data Con : ℕ → Set
data Ty (n : ℕ) : Set
data Tm (n : ℕ) : Set

data Con where
  ∙   : Con zero
  _▷_ : ∀ {n} → Con n → Ty n → Con (suc n)

data Ty n where
  U  : Ty n
  El : Tm n → Ty n
  Π  : Ty n → Ty (suc n) → Ty n

data Tm n where
  var : Fin n → Tm n
  lam : Tm (suc n) → Tm n
  app : Tm n → Tm n → Tm n
