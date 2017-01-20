
{-# OPTIONS --without-K --type-in-type #-}

-- note: interpretation of universe for dependent TT PSh:

-- ⟦ U ⟧ : C → Set₀
-- ⟦ U ⟧ I = ∀ J → C(J, I) → Set₀

-- Huber thesis pg. 31: "U(I) consists of Set₀-valued presheaves over C/I (slice category over I)"
-- todo : rename Ren to OPE

module ImpredPSh3 where

open import Lib
open import JM
open import Syntax

-- the following is very neat:
-- *ᴹ : PSh OPE
-- *ᴹ I = PSh (OPE/I)
*ᴹ : ∀ {Γ'} → Con Γ' → Set₁ -- note Set₁
*ᴹ {Γ'} Γ = ∀ {Δ' Δ σ'} → Ren {Δ'} σ' Δ Γ → Set

*ᴹᵣ : ∀ {Γ' Γ Δ' Δ σ'} → Ren {Δ'}{Γ'} σ' Δ Γ → *ᴹ Γ → *ᴹ Δ
*ᴹᵣ σ Aᴹ δ = Aᴹ (σ ∘ᵣ δ)

data Con'ᴹ : Con' → ∀ {Δ'} → Con Δ' → Set where
  ∙   : ∀ {Δ' Δ} → Con'ᴹ ∙ {Δ'} Δ
  _,_ : ∀ {Γ' Δ' Δ} → Con'ᴹ Γ' {Δ'} Δ → *ᴹ Δ → Con'ᴹ (Γ' ,*) Δ

Con'ᴹᵣ : ∀ {Γ' Δ' Δ Σ' Σ σ} → Ren {Σ'} {Δ'} σ Σ Δ → Con'ᴹ Γ' Δ → Con'ᴹ Γ' Σ
Con'ᴹᵣ σ ∙          = ∙
Con'ᴹᵣ σ (Γ'ᴹ , Aᴹ) = Con'ᴹᵣ σ Γ'ᴹ , *ᴹᵣ σ Aᴹ

*∈ᴹ : ∀ {Γ'} → *∈ Γ' → ∀ {Δ' Δ} → Con'ᴹ Γ' {Δ'} Δ → Set
*∈ᴹ vz     {Δ'}{Δ} (Γ'ᴹ , Aᴹ) = Aᴹ idᵣ  -- idᵣ terminal obj. in slice cat.
*∈ᴹ (vs v) {Δ'}{Δ} (Γ'ᴹ , Aᴹ) = *∈ᴹ v Γ'ᴹ

Tyᴹ : ∀ {Γ'} → Ty Γ' → ∀ {Δ' Δ} → Con'ᴹ Γ' {Δ'} Δ → Set
Tyᴹ (var v) {Δ'}{Δ} Γ'ᴹ = *∈ᴹ v Γ'ᴹ
Tyᴹ (A ⇒ B) {Δ'}{Δ} Γ'ᴹ =
  ∀ {Σ' Σ σ'}(σ : Ren {Σ'} σ' Σ Δ) → Tyᴹ A (Con'ᴹᵣ σ Γ'ᴹ) → Tyᴹ B (Con'ᴹᵣ σ Γ'ᴹ)
Tyᴹ (∀' A)  {Δ'}{Δ} Γ'ᴹ =
  ∀ {Σ' Σ σ'}(σ : Ren {Σ'} σ' Σ Δ) → (Bᴹ : *ᴹ Σ) → Tyᴹ A (Con'ᴹᵣ σ Γ'ᴹ , Bᴹ)

*∈ᴹᵣ : ∀ {Γ'}(v : *∈ Γ'){Δ' Δ Σ' Σ σ' Γ'ᴹ}(σ : Ren {Σ'}{Δ'} σ' Σ Δ) → *∈ᴹ v Γ'ᴹ → *∈ᴹ v (Con'ᴹᵣ σ Γ'ᴹ)
*∈ᴹᵣ vz     {Γ'ᴹ = Γ'ᴹ , Aᴹ} σ tᴹ = {!!} -- todo: *ᴹ I : PSh (OPE/I)
*∈ᴹᵣ (vs v) {Γ'ᴹ = Γ'ᴹ , _}  σ tᴹ = *∈ᴹᵣ v σ tᴹ

Tyᴹᵣ : ∀ {Γ'} A {Δ' Δ Σ' Σ σ' Γ'ᴹ}(σ : Ren {Σ'}{Δ'} σ' Σ Δ) → Tyᴹ {Γ'} A {Δ'}{Δ} Γ'ᴹ → Tyᴹ A (Con'ᴹᵣ σ Γ'ᴹ)
Tyᴹᵣ (var v) σ tᴹ = *∈ᴹᵣ v σ tᴹ
Tyᴹᵣ (A ⇒ B) σ tᴹ = λ δ aᴹ → coe (Tyᴹ B & {!!}) (tᴹ (σ ∘ᵣ δ) (coe (Tyᴹ A & {!!}) aᴹ)) -- Con'ᴹ-∘ᵣ
Tyᴹᵣ (∀' A ) σ tᴹ = λ δ Bᴹ → coe {!!} (tᴹ (σ ∘ᵣ δ) Bᴹ)                                -- Con'ᴹ-∘ᵣ

data Conᴹ : ∀ {Γ'} → Con Γ' → ∀ {Δ'} Δ  → Con'ᴹ Γ' {Δ'} Δ → Set where
  ∙   : ∀ {Δ' Δ} → Conᴹ ∙ {Δ'} Δ ∙
  _,_ : ∀ {Γ' Γ Δ' Δ Γ'ᴹ}{A}         → Conᴹ {Γ'} Γ {Δ'} Δ Γ'ᴹ → Tyᴹ A Γ'ᴹ → Conᴹ (Γ , A) Δ Γ'ᴹ
  _,* : ∀ {Γ' Γ Δ' Δ Γ'ᴹ}{Aᴹ : *ᴹ Δ} → Conᴹ {Γ'} Γ {Δ'} Δ Γ'ᴹ → Conᴹ (Γ ,*) Δ (Γ'ᴹ , Aᴹ)

Conᴹᵣ : ∀ {Γ' Γ Δ' Δ Γ'ᴹ Σ' Σ σ'} (σ : Ren {Σ'}{Δ'} σ' Σ Δ) → Conᴹ {Γ'} Γ {Δ'} Δ Γ'ᴹ → Conᴹ Γ Σ (Con'ᴹᵣ σ Γ'ᴹ)
Conᴹᵣ σ ∙                   = ∙
Conᴹᵣ σ (_,_ {A = A} Γᴹ aᴹ) = Conᴹᵣ σ Γᴹ , Tyᴹᵣ A σ aᴹ
Conᴹᵣ σ (Γᴹ ,*)             = Conᴹᵣ σ Γᴹ ,*

Ren'ᴹ :  ∀ {Γ' Δ'} → Ren' Γ' Δ' → ∀ {Σ' Σ} → Con'ᴹ Γ' {Σ'} Σ → Con'ᴹ Δ' Σ
Ren'ᴹ ∙        Γ'ᴹ        = Γ'ᴹ
Ren'ᴹ (drop σ) (Γ'ᴹ , _ ) = Ren'ᴹ σ Γ'ᴹ
Ren'ᴹ (keep σ) (Γ'ᴹ , Aᴹ) = Ren'ᴹ σ Γ'ᴹ , Aᴹ

Sub'ᴹ :  ∀ {Γ' Δ'} → Sub' Γ' Δ' → ∀ {Σ' Σ} → Con'ᴹ Γ' {Σ'} Σ → Con'ᴹ Δ' Σ
Sub'ᴹ ∙       Γ'ᴹ = ∙
Sub'ᴹ (σ , A) Γ'ᴹ = Sub'ᴹ σ Γ'ᴹ , (λ δ → Tyᴹ A (Con'ᴹᵣ δ Γ'ᴹ))

∈ᴹ : ∀ {Γ' Γ A} → _∈_ {Γ'} A Γ → ∀ {Δ' Δ}(Γ'ᴹ : Con'ᴹ Γ' {Δ'} Δ) → Conᴹ Γ Δ Γ'ᴹ → Tyᴹ A Γ'ᴹ
∈ᴹ vz      _ (Γᴹ , t) = t
∈ᴹ (vs v)  _ (Γᴹ , _) = ∈ᴹ v _ Γᴹ
∈ᴹ (vs* v) _ (Γᴹ ,* ) = coe {!!} (∈ᴹ v _ Γᴹ) -- Tyᵣᴹ

Tmᴹ : ∀ {Γ' Γ A} → Tm {Γ'} Γ A → ∀ {Δ' Δ}(Γ'ᴹ : Con'ᴹ Γ' {Δ'} Δ) → Conᴹ Γ Δ Γ'ᴹ → Tyᴹ A Γ'ᴹ
Tmᴹ (var v)    Γ'ᴹ Γᴹ = ∈ᴹ v Γ'ᴹ Γᴹ
Tmᴹ (lam t)    Γ'ᴹ Γᴹ = λ σ aᴹ → Tmᴹ t (Con'ᴹᵣ σ Γ'ᴹ) (Conᴹᵣ σ Γᴹ , aᴹ)
Tmᴹ (app f x)  Γ'ᴹ Γᴹ = coe {!!} (Tmᴹ f Γ'ᴹ Γᴹ idᵣ (coe {!!} (Tmᴹ x Γ'ᴹ Γᴹ))) -- Con'ᴹ-idᵣ
Tmᴹ (tlam t)   Γ'ᴹ Γᴹ = λ σ Bᴹ → Tmᴹ t (Con'ᴹᵣ σ Γ'ᴹ , Bᴹ) (Conᴹᵣ σ Γᴹ ,*)
Tmᴹ (tapp t B) Γ'ᴹ Γᴹ = coe {!!} (Tmᴹ t Γ'ᴹ Γᴹ idᵣ (λ δ → Tyᴹ B (Con'ᴹᵣ δ Γ'ᴹ))) -- Tyₛᴹ



