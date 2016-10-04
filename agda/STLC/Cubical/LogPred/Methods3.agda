{-# OPTIONS --no-eta --without-K --rewriting #-}

module STLC.Cubical.LogPred.Methods3 where

open import Level
open import STLC.Cubical.Lib
open import STLC.Cubical.Syntax
open import STLC.Cubical.Derived
open import STLC.Cubical.Elim
open import STLC.Cubical.Nf

open import STLC.Cubical.LogPred.Methods1

,∘ᴹ :
  ∀ {Γ} {Γᴹ : Conᴹ Γ} {Δ} {Δᴹ : Conᴹ Δ}
    {Σ} {Σᴹ : Conᴹ Σ} {δ : Tms Γ Δ} {δᴹ : Tmsᴹ Γᴹ Δᴹ δ}
    {σ : Tms Σ Γ} {σᴹ : Tmsᴹ Σᴹ Γᴹ σ} {A} {Aᴹ : Tyᴹ A}
    {a} {aᴹ : Tmᴹ Γᴹ Aᴹ a}
    -- (δᴹ ,ₛᴹ aᴹ) ∘ᴹ σᴹ ≡[ ap (Tmsᴹ Σᴹ (Δᴹ ,ᴹ Aᴹ)) ,∘ ]≡ δᴹ ∘ᴹ σᴹ ,ₛᴹ aᴹ [ σᴹ ]ᴹ
    → _∘ᴹ_ {Σᴹ = Δᴹ ,ᴹ Aᴹ} (_,ₛᴹ_ {Δᴹ = Δᴹ} δᴹ {Aᴹ = Aᴹ} aᴹ) σᴹ
        ≡[ ap (Tmsᴹ Σᴹ (Δᴹ ,ᴹ Aᴹ)) ,∘ ]≡
      _,ₛᴹ_ {Δᴹ = Δᴹ} (_∘ᴹ_ {Σᴹ = Δᴹ} δᴹ σᴹ) {Aᴹ = Aᴹ} (_[_]ᴹ {Aᴹ = Aᴹ} aᴹ σᴹ)

,∘ᴹ {Γ}{Γᴹ}{Δ}{Δᴹ}{Σ}{Σᴹ}{δ}{δᴹ}{σ}{σᴹ}{A}{Aᴹ}{a}{aᴹ} = {!!}
