
{-# OPTIONS --without-K --type-in-type #-}


module ImpredPSh5 where

open import Lib
open import JM
open import Syntax

record Cand {Γ'} Γ A : Set₁ where
  constructor con
  field
    S : Set
    Q : S → Nf {Γ'} Γ A
    U : Ne Γ A → S
open Cand

*ᴹ : ∀ {Γ'} Γ → Ty Γ' → Set
*ᴹ {Γ'} Γ A = ∀ {Δ' Δ σ'}(σ : OPE {Δ'}{Γ'} σ' Δ Γ) → Cand Δ (Tyₑ σ' A)

*ᴹₑ : ∀ {Γ' Γ A Δ' Δ σ'}(σ : OPE {Δ'}{Γ'} σ' Δ Γ) → *ᴹ {Γ'} Γ A → *ᴹ {Δ'} Δ (Tyₑ σ' A)
*ᴹₑ {A = A} {σ' = σ'} σ f {σ' = δ'} δ = coe (Cand _ & Ty-∘ₑ σ' δ' A ⁻¹) (f (σ ∘ₑ δ))

data Con'ᴹ : (Γ' : Con') → ∀ {Δ'} → Con Δ' → Sub' Δ' Γ' → Set where
  ∙   : ∀ {Δ' Δ} → Con'ᴹ ∙ {Δ'} Δ ∙
  _,_ : ∀ {Γ' Δ' Δ σ A} → Con'ᴹ Γ' {Δ'} Δ σ → *ᴹ Δ A → Con'ᴹ (Γ' ,*) Δ (σ , A)

Con'ᴹₑ :
  ∀ {Γ' Δ' Δ σ' Σ' Σ δ'}(δ : OPE {Σ'}{Δ'} δ' Σ Δ) → Con'ᴹ Γ' {Δ'} Δ σ' → Con'ᴹ Γ' {Σ'} Σ (σ' ₛ∘'ₑ δ')
Con'ᴹₑ δ ∙          = ∙
Con'ᴹₑ δ (σ'ᴹ , Aᴹ) = Con'ᴹₑ δ σ'ᴹ , *ᴹₑ δ Aᴹ

*∈ᴹ : ∀ {Γ'}(v : *∈ Γ') → ∀ {Δ' Δ}(σ : Sub' Δ' Γ')(σᴹ : Con'ᴹ Γ' Δ σ) → Cand Δ (*∈ₛ σ v)
*∈ᴹ vz     (σ , A) (σᴹ , Aᴹ) = coe (Cand _ & Ty-idₑ A) (Aᴹ idₑ)
*∈ᴹ (vs v) (σ , _) (σᴹ , _)  = *∈ᴹ v σ σᴹ

generic*ᴹ : ∀ {Γ' Γ}(v : *∈ Γ') → *ᴹ {Γ'} Γ (var v)
generic*ᴹ {Γ'}{Γ} v {Δ'}{Δ}{σ'} σ = con (Ne Δ (var (*∈ₑ σ' v))) ne (λ n → n)

Tyᴹ : ∀ {Γ'}(A : Ty Γ') → ∀ {Δ' Δ}(σ : Sub' Δ' Γ')(σᴹ : Con'ᴹ Γ' Δ σ) → Cand Δ (Tyₛ σ A)
Tyᴹ (var v) σ σᴹ = *∈ᴹ v σ σᴹ
Tyᴹ {Γ'} (A ⇒ B) {Δ'} {Δ} σ σᴹ = con

  (∀ {Σ' Σ δ'}(δ : OPE {Σ'}{Δ'} δ' Σ Δ) → Tyᴹ A _ (Con'ᴹₑ δ σᴹ) .S → Tyᴹ B _ (Con'ᴹₑ δ σᴹ) .S)

  (λ fᴹ → let σᴹ' = Con'ᴹₑ (drop {A = Tyₛ (σ ₛ∘'ₑ id'ₑ) A} idₑ) σᴹ in
          lam (coe ((λ x → Nf (Δ , Tyₛ x A) (Tyₛ x B)) & {!!})
           (Tyᴹ B _ σᴹ' .Q (fᴹ (drop idₑ) (Tyᴹ A _ σᴹ' .U (var vz))))))

  (λ n {Σ'}{Σ}{δ'} δ aᴹ → let σᴹ' = Con'ᴹₑ δ σᴹ in
    Tyᴹ B _ σᴹ' .U  (app (coe (Ne Σ & Ty-ₛ∘ₑ σ δ' (A ⇒ B)) (Neₑ δ n)) (Tyᴹ A _ σᴹ' .Q aᴹ)))

Tyᴹ {Γ'} (∀' A)  {Δ'} {Δ} σ σᴹ = con

  (∀ {Σ' Σ δ'}(δ : OPE {Σ'}{Δ'} δ' Σ Δ)(B : Ty Σ')(Bᴹ : *ᴹ Σ B) → Tyᴹ A _ (Con'ᴹₑ δ σᴹ , Bᴹ) .S)

  (λ fᴹ → let g* = generic*ᴹ vz in tlam (Tyᴹ A _ (Con'ᴹₑ (drop' idₑ) σᴹ , g*) .Q (fᴹ (drop' idₑ) _ g*)))

  (λ n {Σ'}{Σ}{δ'} δ B Bᴹ →
     Tyᴹ A _ (Con'ᴹₑ δ σᴹ , Bᴹ) .U (coe (Ne Σ & {!!}) (tappₙₑ (Neₑ δ n) B)))

Tyᴹₑ :
  ∀ {Γ' A Δ' Δ σ' σ'ᴹ Σ' Σ δ'}(δ : OPE {Σ'}{Δ'} δ' Σ Δ) → Tyᴹ {Γ'} A σ' σ'ᴹ .S → Tyᴹ A _ (Con'ᴹₑ δ σ'ᴹ) .S
Tyᴹₑ {A = var vz} {σ'ᴹ = σ'ᴹ , X} δ aᴹ = {!!}
Tyᴹₑ {A = var (vs v)} δ aᴹ = {!!}
Tyᴹₑ {A = A ⇒ B} δ aᴹ {Ξ'}{Ξ}{ν'} ν xᴹ = {!!}
Tyᴹₑ {A = ∀' A}  δ aᴹ {Ξ'}{Ξ}{ν'} ν B Bᴹ = {!!}

data Conᴹ : ∀ {Γ'} → Con Γ' → ∀ {Δ'} Δ {σ'} → Con'ᴹ Γ' {Δ'} Δ σ' → Set where
  ∙   : ∀ {Δ' Δ} → Conᴹ ∙ {Δ'} Δ ∙
  _,_ : ∀ {Γ' Γ Δ' Δ σ' σ'ᴹ A} → Conᴹ {Γ'} Γ {Δ'} Δ {σ'} σ'ᴹ → Tyᴹ A σ' σ'ᴹ .S → Conᴹ (Γ , A) Δ σ'ᴹ
  _,* : ∀ {Γ' Γ Δ' Δ σ' σ'ᴹ A}{Aᴹ : *ᴹ Δ A} → Conᴹ {Γ'} Γ {Δ'} Δ {σ'} σ'ᴹ → Conᴹ (Γ ,*) Δ (σ'ᴹ , Aᴹ)

Conᴹₑ :
  ∀ {Γ' Γ Δ' Δ σ' σ'ᴹ Σ' Σ δ'}(δ : OPE {Σ'}{Δ'} δ' Σ Δ) → Conᴹ {Γ'} Γ Δ {σ'} σ'ᴹ → Conᴹ Γ Σ (Con'ᴹₑ δ σ'ᴹ)
Conᴹₑ δ ∙        = ∙
Conᴹₑ δ (Γᴹ , x) = {!!} , {!!}
Conᴹₑ δ (Γᴹ ,*)  = {!!} ,*

∈ᴹ : ∀ {Γ' Γ A} → _∈_ {Γ'} A Γ → ∀ {Δ' Δ σ'} σ'ᴹ → Conᴹ Γ Δ σ'ᴹ → Tyᴹ {Γ'} A {Δ'} σ' σ'ᴹ .S
∈ᴹ vz       σ'ᴹ      (Γᴹ , t) = t
∈ᴹ (vs v)   σ'ᴹ      (Γᴹ , t) = ∈ᴹ v σ'ᴹ Γᴹ
∈ᴹ (vs* v) (σ'ᴹ , _) (Γᴹ ,* ) = coe {!!} (∈ᴹ v σ'ᴹ Γᴹ)

Tmᴹ : ∀ {Γ' Γ A} → Tm {Γ'} Γ A → ∀ {Δ' Δ σ'} σ'ᴹ → Conᴹ Γ Δ σ'ᴹ → Tyᴹ {Γ'} A {Δ'} σ' σ'ᴹ .S
Tmᴹ (var v)    σ'ᴹ Γᴹ = ∈ᴹ v σ'ᴹ Γᴹ
Tmᴹ (lam t)    σ'ᴹ Γᴹ = λ δ aᴹ → Tmᴹ t (Con'ᴹₑ δ σ'ᴹ) ({!!} , aᴹ)
Tmᴹ (app f x)  σ'ᴹ Γᴹ = {!!}
Tmᴹ (tlam t)   σ'ᴹ Γᴹ = {!!}
Tmᴹ (tapp t B) σ'ᴹ Γᴹ = {!!}

-- Tmᴹ : ∀ {Γ' Γ A} → Tm {Γ'} Γ A → ∀ {Δ' Δ}(Γ'ᴹ : Con'ᴹ Γ' {Δ'} Δ) → Conᴹ Γ Δ Γ'ᴹ → Tyᴹ A Γ'ᴹ
-- Tmᴹ (var v)    Γ'ᴹ Γᴹ = ∈ᴹ v Γ'ᴹ Γᴹ
-- Tmᴹ (lam t)    Γ'ᴹ Γᴹ = λ σ aᴹ → Tmᴹ t (Con'ᴹₑ σ Γ'ᴹ) (Conᴹₑ σ Γᴹ , aᴹ)
-- Tmᴹ (app f x)  Γ'ᴹ Γᴹ = coe {!!} (Tmᴹ f Γ'ᴹ Γᴹ idₑ (coe {!!} (Tmᴹ x Γ'ᴹ Γᴹ))) -- Con'ᴹ-idₑ
-- Tmᴹ (tlam t)   Γ'ᴹ Γᴹ = λ σ Bᴹ → Tmᴹ t (Con'ᴹₑ σ Γ'ᴹ , Bᴹ) (Conᴹₑ σ Γᴹ ,*)
-- Tmᴹ (tapp t B) Γ'ᴹ Γᴹ = coe {!!} (Tmᴹ t Γ'ᴹ Γᴹ idₑ (λ δ → Tyᴹ B (Con'ᴹₑ δ Γ'ᴹ))) -- Tyₛᴹ


