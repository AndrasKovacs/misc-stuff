{-# OPTIONS --no-eta --without-K --rewriting #-}

module STLC.Cubical.LogPred.Methods2 where

open import Level
open import STLC.Cubical.Lib
open import STLC.Cubical.Syntax
open import STLC.Cubical.Derived
open import STLC.Cubical.Elim
open import STLC.Cubical.Nf

open import STLC.Cubical.LogPred.Methods1

idlᴹ :
  ∀ {Γ} {Γᴹ : Conᴹ Γ} {Δ} {Δᴹ : Conᴹ Δ} {δ : Tms Γ Δ}{δᴹ : Tmsᴹ Γᴹ Δᴹ δ}
  -- → idᴹ ∘ᴹ δᴹ ≡[ ap (Tmsᴹ Γᴹ Δᴹ) idl ]≡ δᴹ
  → _∘ᴹ_ {Δᴹ = Δᴹ}{Σᴹ = Δᴹ} idᴹ δᴹ ≡[ ap (Tmsᴹ Γᴹ Δᴹ) idl ]≡ δᴹ
idlᴹ {Γ}{Γᴹ}{Δ}{Δᴹ}{δ}{δᴹ} = {!!}

idrᴹ :
  ∀ {Γ} {Γᴹ : Conᴹ Γ} {Δ} {Δᴹ : Conᴹ Δ} {δ : Tms Γ Δ}
    {δᴹ : Tmsᴹ Γᴹ Δᴹ δ}
  -- → δᴹ ∘ᴹ idᴹ ≡[ ap (Tmsᴹ Γᴹ Δᴹ) idr ]≡ δᴹ
  → _∘ᴹ_ {Δᴹ = Γᴹ}{Σᴹ = Δᴹ} δᴹ idᴹ ≡[ ap (Tmsᴹ Γᴹ Δᴹ) idr ]≡ δᴹ
idrᴹ {Γ}{Γᴹ}{Δ}{Δᴹ}{δ}{δᴹ} = {!!}

assᴹ :
  ∀ {Δ} {Δᴹ : Conᴹ Δ} {Γ} {Γᴹ : Conᴹ Γ}
    {Σ} {Σᴹ : Conᴹ Σ} {Ω} {Ωᴹ : Conᴹ Ω}
    {σ : Tms Σ Ω} {σᴹ : Tmsᴹ Σᴹ Ωᴹ σ} {δ : Tms Γ Σ}
    {δᴹ : Tmsᴹ Γᴹ Σᴹ δ} {ν : Tms Δ Γ} {νᴹ : Tmsᴹ Δᴹ Γᴹ ν}

    -- (σᴹ ∘ᴹ δᴹ) ∘ᴹ νᴹ ≡[ ap (Tmsᴹ Δᴹ Ωᴹ) ass ]≡ σᴹ ∘ᴹ (δᴹ ∘ᴹ νᴹ)
    → _∘ᴹ_ {Σᴹ = Ωᴹ} (_∘ᴹ_ {Σᴹ = Ωᴹ} σᴹ δᴹ) νᴹ
      ≡[ ap (Tmsᴹ Δᴹ Ωᴹ) (ass {σ = σ}{δ}{ν}) ]≡
    _∘ᴹ_ {Σᴹ = Ωᴹ} σᴹ (_∘ᴹ_ {Σᴹ = Σᴹ} δᴹ νᴹ)

assᴹ {Γ}{Γᴹ}{Δ}{Δᴹ}{Σ}{Σᴹ}{Ω}{Ωᴹ}{σ}{σᴹ}{δ}{δᴹ}{ν}{νᴹ} = {!!}
