{-# OPTIONS --no-eta --rewriting --without-K #-}

module STLC.Norm.Methods2 where

open import STLC.Derived
open import STLC.lib
open import STLC.Syntax
open import STLC.Norm.Methods1
open import STLC.Norm.CoeLemmas

[id]ᴹ :
  ∀{Γ}{Γᴹ : Conᴹ Γ}{A}{Aᴹ : Tyᴹ A}{t : Tm Γ A}{tᴹ : Tmᴹ Γᴹ Aᴹ t}
  -- tᴹ [ idᴹ ]ᴹ ≡[ ap (Tmᴹ Γᴹ Aᴹ) [id] ]≡ tᴹ
  → _[_]ᴹ {Aᴹ = Aᴹ} tᴹ idᴹ ≡[ ap (Tmᴹ Γᴹ Aᴹ) [id] ]≡ tᴹ
[id]ᴹ {Γ}{Γᴹ}{A}{Aᴹ}{t}{tᴹ} =
  Tmᴹ-≡-intro {Γ} {Γᴹ} {A} {Aᴹ} [id] λ Δ σ σᴹ
  → ap-◾ (ap (λ t₁ → Aᴹ (t₁ [ σ ])) [id]) (ap Aᴹ ([][] ⁻¹))
  ◾ ap (coe (ap Aᴹ ([][] ⁻¹) ◾ ap (λ t → Aᴹ (t [ σ ])) [id]))
        (coe-float tᴹ (idl ⁻¹))
  ◾ ap-◾ (ap Aᴹ ([][] ⁻¹) ◾ ap (λ t₁ → Aᴹ (t₁ [ σ ])) [id])
          (ap (λ z → Aᴹ (t [ z ])) (idl ⁻¹))
  ◾ UIP-coe
      (ap (λ z → Aᴹ (t [ z ])) (idl ⁻¹) ◾
        (ap Aᴹ ([][] ⁻¹) ◾ ap (λ t₁ → Aᴹ (t₁ [ σ ])) [id]))
      refl

[][]ᴹ :
  ∀ {Γ}{Γᴹ : Conᴹ Γ}{Δ}{Δᴹ : Conᴹ Δ}{Σ}{Σᴹ : Conᴹ Σ}{A}{Aᴹ : Tyᴹ A}
   {t : Tm Σ A}{tᴹ : Tmᴹ Σᴹ Aᴹ t}{σ : Tms Γ Δ}{σᴹ : Tmsᴹ Γᴹ Δᴹ σ}{δ}{δᴹ : Tmsᴹ Δᴹ Σᴹ δ}

   -- tᴹ [ δᴹ ]ᴹ [ σᴹ ]ᴹ ≡[ ap (Tmᴹ Γᴹ Aᴹ) [][] ]≡ tᴹ [ δᴹ ∘ᴹ σᴹ ]ᴹ

   → _[_]ᴹ {Aᴹ = Aᴹ} (_[_]ᴹ {Aᴹ = Aᴹ} tᴹ δᴹ) σᴹ
            ≡[ ap (Tmᴹ Γᴹ Aᴹ) [][] ]≡
     _[_]ᴹ {Aᴹ = Aᴹ} tᴹ (_∘ᴹ_ {Σᴹ = Σᴹ} δᴹ σᴹ)

[][]ᴹ {Γ}{Γᴹ}{Δ}{Δᴹ}{Σ}{Σᴹ}{A}{Aᴹ}{t}{tᴹ}{σ}{σᴹ}{δ}{δᴹ} =
  Tmᴹ-≡-intro {Γ}{Γᴹ}{A}{Aᴹ} [][] λ Ξ γ γᴹ
  → ap-◾ (ap (λ t → Aᴹ (t [ γ ])) [][]) (ap Aᴹ ([][] ⁻¹))
  ◾ ap-◾ (ap Aᴹ ([][] ⁻¹) ◾ ap (λ t → Aᴹ (t [ γ ])) [][]) (ap Aᴹ ([][] ⁻¹))
  ◾ UIP-coe
      (ap Aᴹ ([][] ⁻¹) ◾ (ap Aᴹ ([][] ⁻¹) ◾ ap (λ t → Aᴹ (t [ γ ])) [][]))
      (ap (λ z → Aᴹ (t [ z ])) (ass ⁻¹) ◾ ap Aᴹ ([][] ⁻¹))
  ◾ ap-◾ (ap Aᴹ ([][] ⁻¹)) (ap (λ z → Aᴹ (t [ z ])) (ass ⁻¹)) ⁻¹
  ◾ ap (coe (ap Aᴹ ([][] ⁻¹))) (coe-float tᴹ (ass ⁻¹) ⁻¹)

idlᴹ :
  ∀ {Γ} {Γᴹ : Conᴹ Γ} {Δ} {Δᴹ : Conᴹ Δ} {δ : Tms Γ Δ}{δᴹ : Tmsᴹ Γᴹ Δᴹ δ}
  -- → idᴹ ∘ᴹ δᴹ ≡[ ap (Tmsᴹ Γᴹ Δᴹ) idl ]≡ δᴹ
  → _∘ᴹ_ {Δᴹ = Δᴹ}{Σᴹ = Δᴹ} idᴹ δᴹ ≡[ ap (Tmsᴹ Γᴹ Δᴹ) idl ]≡ δᴹ
idlᴹ {Γ}{Γᴹ}{Δ}{Δᴹ}{δ}{δᴹ} =
  Tmsᴹ-≡-intro {Γ} {Γᴹ} {Δ} {Δᴹ} idl λ Σ σ σᴹ
  → ap-◾ (ap (λ σ₁ → Δᴹ (σ₁ ∘ σ)) idl) (ap Δᴹ (ass ⁻¹))
  ◾ ap-◾ (ap Δᴹ (ass ⁻¹) ◾ ap (λ σ₁ → Δᴹ (σ₁ ∘ σ)) idl) (ap Δᴹ (idl ⁻¹))
  ◾ UIP-coe
      (ap Δᴹ (idl ⁻¹) ◾ (ap Δᴹ (ass ⁻¹) ◾ ap (λ σ₁ → Δᴹ (σ₁ ∘ σ)) idl))
      refl

idrᴹ :
  ∀ {Γ} {Γᴹ : Conᴹ Γ} {Δ} {Δᴹ : Conᴹ Δ} {δ : Tms Γ Δ}
    {δᴹ : Tmsᴹ Γᴹ Δᴹ δ}
  -- → δᴹ ∘ᴹ idᴹ ≡[ ap (Tmsᴹ Γᴹ Δᴹ) idr ]≡ δᴹ
  → _∘ᴹ_ {Δᴹ = Γᴹ}{Σᴹ = Δᴹ} δᴹ idᴹ ≡[ ap (Tmsᴹ Γᴹ Δᴹ) idr ]≡ δᴹ
idrᴹ {Γ}{Γᴹ}{Δ}{Δᴹ}{δ}{δᴹ} =
  Tmsᴹ-≡-intro {Γ} {Γᴹ} {Δ} {Δᴹ} idr λ Σ σ σᴹ
  → ap (λ x → coe (ap (λ δ → Δᴹ (δ ∘ σ)) idr) (coe (ap Δᴹ (ass ⁻¹)) x))
       (coe-float δᴹ (idl ⁻¹))
  ◾ ap-◾ (ap (λ δ → Δᴹ (δ ∘ σ)) idr) (ap Δᴹ (ass ⁻¹))
  ◾ ap-◾ (ap Δᴹ (ass ⁻¹) ◾ ap (λ δ → Δᴹ (δ ∘ σ)) idr) (ap (λ z → Δᴹ (δ ∘ z)) (idl ⁻¹))
  ◾ UIP-coe
      (ap (λ z → Δᴹ (δ ∘ z)) (idl ⁻¹) ◾
        (ap Δᴹ (ass ⁻¹) ◾ ap (λ δ → Δᴹ (δ ∘ σ)) idr))
      refl

assᴹ :
  ∀ {Δ} {Δᴹ : Conᴹ Δ} {Γ} {Γᴹ : Conᴹ Γ}
    {Σ} {Σᴹ : Conᴹ Σ} {Ω} {Ωᴹ : Conᴹ Ω}
    {σ : Tms Σ Ω} {σᴹ : Tmsᴹ Σᴹ Ωᴹ σ} {δ : Tms Γ Σ}
    {δᴹ : Tmsᴹ Γᴹ Σᴹ δ} {ν : Tms Δ Γ} {νᴹ : Tmsᴹ Δᴹ Γᴹ ν}

    -- (σᴹ ∘ᴹ δᴹ) ∘ᴹ νᴹ ≡[ ap (Tmsᴹ Δᴹ Ωᴹ) ass ]≡ σᴹ ∘ᴹ (δᴹ ∘ᴹ νᴹ)
    → _∘ᴹ_ {Σᴹ = Ωᴹ} (_∘ᴹ_ {Σᴹ = Ωᴹ} σᴹ δᴹ) νᴹ
      ≡[ ap (Tmsᴹ Δᴹ Ωᴹ) (ass {σ = σ}{δ}{ν}) ]≡
    _∘ᴹ_ {Σᴹ = Ωᴹ} σᴹ (_∘ᴹ_ {Σᴹ = Σᴹ} δᴹ νᴹ)

assᴹ {Γ}{Γᴹ}{Δ}{Δᴹ}{Σ}{Σᴹ}{Ω}{Ωᴹ}{σ}{σᴹ}{δ}{δᴹ}{ν}{νᴹ} =
  Tmsᴹ-≡-intro {Γ} {Γᴹ} {Ω} {Ωᴹ} ass λ Ξ γ γᴹ
  → ap-◾ (ap (λ σ₁ → Ωᴹ (σ₁ ∘ γ)) ass) (ap Ωᴹ (ass ⁻¹))
  ◾ ap-◾ (ap Ωᴹ (ass ⁻¹) ◾ ap (λ σ₁ → Ωᴹ (σ₁ ∘ γ)) ass) (ap Ωᴹ (ass ⁻¹))
  ◾ UIP-coe
     (ap Ωᴹ (ass ⁻¹) ◾ (ap Ωᴹ (ass ⁻¹) ◾ ap (λ σ₁ → Ωᴹ (σ₁ ∘ γ)) ass))
     (ap (λ z → Ωᴹ (σ ∘ z)) (ass ⁻¹) ◾ ap Ωᴹ (ass ⁻¹))
  ◾ ap-◾ (ap Ωᴹ (ass ⁻¹)) (ap (λ z → Ωᴹ (σ ∘ z)) (ass ⁻¹)) ⁻¹
  ◾ ap (coe (ap Ωᴹ (ass ⁻¹))) (coe-float σᴹ (ass ⁻¹)) ⁻¹

