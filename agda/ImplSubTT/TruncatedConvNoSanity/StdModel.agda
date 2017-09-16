{-# OPTIONS --without-K #-}

module StdModel where

open import Lib
open import Syntax
open import Embedding
open import Substitution
open import Conversion
open import Typing
open import Sanity

open import Data.Maybe
open import Category.Monad
open module MaybeMonad {α} = RawMonad {α} Data.Maybe.monad

import Level as L

module M (Uᴹ : Set)(Elᴹ : Uᴹ → Set) where
