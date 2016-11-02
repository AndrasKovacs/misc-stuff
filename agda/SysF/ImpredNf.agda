
{-# OPTIONS --without-K --type-in-type #-}

module ImpredNf where

open import Lib
open import Syntax

data Con'ᴹ : Con' → Set where
  ∙   : Con'ᴹ ∙
  _,_ : ∀ {Γ} → Con'ᴹ Γ → (∀ Γ → Con Γ → Set) → Con'ᴹ (Γ ,*)

*∈ᴹ : ∀ {Γ'} → *∈ Γ' → Con'ᴹ Γ' → ∀ Δ' → Con Δ' → Set
*∈ᴹ vz     (Γ'ᴹ , Aᴹ) Δ' Δ = Aᴹ Δ' Δ
*∈ᴹ (vs v) (Γ'ᴹ , Aᴹ) Δ' Δ = *∈ᴹ v Γ'ᴹ Δ' Δ

Tyᴹ : ∀ {Γ'} → Ty Γ' → Con'ᴹ Γ' → ∀ Δ' → Con Δ' → Set
Tyᴹ (var v) Γ'ᴹ Δ' Δ = *∈ᴹ v Γ'ᴹ Δ' Δ
Tyᴹ ι       Γ'ᴹ Δ' Δ = Nf Δ ι
Tyᴹ (A ⇒ B) Γ'ᴹ Δ' Δ =
  ∀ {Σ' Σ σ'}(σ : Ren {Σ'} σ' Σ Δ) → Tyᴹ A Γ'ᴹ Σ' Σ → Tyᴹ B Γ'ᴹ Σ' Σ
Tyᴹ (∀' A)  Γᴹ Δ' Δ =
  ∀ {Σ' Σ σ'}(σ : Ren {Σ'} σ' Σ Δ) (Bᴹ : ∀ Γ' → Con Γ' → Set)
  → Tyᴹ A (Γᴹ , Bᴹ) Σ' Σ

data Conᴹ : ∀ {Γ'} → Con Γ' → Con'ᴹ Γ' → ∀ {Δ'} → Con Δ' → Set where
  ∙   : ∀ {Δ'}{Δ} → Conᴹ {∙} ∙ ∙ {Δ'} Δ
  _,_ : ∀ {Γ' Γ Γ'ᴹ Δ' Δ A} → Conᴹ {Γ'} Γ Γ'ᴹ {Δ'} Δ → Tyᴹ A Γ'ᴹ Δ' Δ → Conᴹ (Γ , A) Γ'ᴹ Δ
  _,* : ∀ {Γ' Γ Γ'ᴹ Aᴹ Δ' Δ} → Conᴹ {Γ'} Γ Γ'ᴹ {Δ'} Δ → Conᴹ (Γ ,*) (Γ'ᴹ , Aᴹ) Δ

Ren'ᴹ : ∀ {Γ Δ} → Ren' Γ Δ → Con'ᴹ Γ → Con'ᴹ Δ
Ren'ᴹ ∙        Γᴹ        = Γᴹ
Ren'ᴹ (drop σ) (Γᴹ , Aᴹ) = Ren'ᴹ σ Γᴹ
Ren'ᴹ (keep σ) (Γᴹ , Aᴹ) = Ren'ᴹ σ Γᴹ , Aᴹ

-- PRESHEAF PLZ IN *ᴹ
*∈ᴹᵣ :
  ∀ {Γ' Γ'ᴹ Δ' Δ Σ' Σ σ v}
  → Ren {Σ'}{Δ'} σ Σ Δ → *∈ᴹ {Γ'} v Γ'ᴹ Δ' Δ → *∈ᴹ v Γ'ᴹ Σ' Σ
*∈ᴹᵣ {Γ'ᴹ = Γ'ᴹ , Aᴹ} {v = vz} σ₁ x₁ = {!!}
*∈ᴹᵣ {v = vs v} σ x = {!!}

Tyᴹᵣ :
  ∀ {Γ' A Γ'ᴹ Δ' Δ Σ' Σ σ}
  → Ren {Σ'}{Δ'} σ Σ Δ → Tyᴹ {Γ'} A Γ'ᴹ Δ' Δ → Tyᴹ A Γ'ᴹ Σ' Σ
Tyᴹᵣ {A = var v} σ Aᴹ = {!!}
Tyᴹᵣ {A = ι}     σ Aᴹ = Aᴹ [ σ ]ₙᵣ
Tyᴹᵣ {A = A ⇒ B} σ Aᴹ = λ δ → Aᴹ (σ ∘ᵣ δ)
Tyᴹᵣ {A = ∀' A}  σ Aᴹ = λ δ → Aᴹ (σ ∘ᵣ δ)

Conᴹᵣ :
  ∀ {Γ' Γ Δ' Δ Σ' Σ Γ'ᴹ σ} → Ren {Σ'}{Δ'} σ Σ Δ → Conᴹ {Γ'} Γ Γ'ᴹ Δ → Conᴹ Γ Γ'ᴹ Σ
Conᴹᵣ σ ∙         = ∙
Conᴹᵣ σ (_,_ {A = A} Γᴹ Aᴹ) = (Conᴹᵣ σ Γᴹ) , Tyᴹᵣ {A = A} σ Aᴹ -- 
Conᴹᵣ σ (Γᴹ ,*)   = Conᴹᵣ σ Γᴹ ,*  

id'ᵣᴹ : ∀ {Γ} (Γᴹ : Con'ᴹ Γ) → Ren'ᴹ id'ᵣ Γᴹ ≡ Γᴹ
id'ᵣᴹ {∙}    Γᴹ        = refl
id'ᵣᴹ {Γ ,*} (Γᴹ , Aᴹ) = (_, Aᴹ) & id'ᵣᴹ Γᴹ

∈ᴹ :
  ∀ {Γ' Γ A} → _∈_ {Γ'} A Γ
  → (Γᴹ : Con'ᴹ Γ')
  → ∀ {Δ'}{Δ} → Conᴹ Γ Γᴹ {Δ'} Δ → Tyᴹ A Γᴹ Δ' Δ
∈ᴹ vz      Γ'ᴹ       (Γᴹ , Aᴹ) = Aᴹ
∈ᴹ (vs v)  Γ'ᴹ       (Γᴹ , _ ) = ∈ᴹ v Γ'ᴹ Γᴹ
∈ᴹ (vs* v) (Γ'ᴹ , _) (Γᴹ ,*)   = coe {!!} (∈ᴹ v Γ'ᴹ Γᴹ) --semantic []ᵣ

Tmᴹ :
  ∀ {Γ' Γ A} → Tm {Γ'} Γ A
  → (Γᴹ : Con'ᴹ Γ')
  → ∀ {Δ'}{Δ} → Conᴹ Γ Γᴹ {Δ'} Δ → Tyᴹ A Γᴹ Δ' Δ
Tmᴹ (var v)    Γ'ᴹ Γᴹ = ∈ᴹ v Γ'ᴹ Γᴹ
Tmᴹ (lam t)    Γ'ᴹ Γᴹ = λ σ aᴹ → Tmᴹ t Γ'ᴹ (Conᴹᵣ σ Γᴹ , aᴹ)
Tmᴹ (app f a)  Γ'ᴹ Γᴹ = Tmᴹ f Γ'ᴹ Γᴹ idᵣ (Tmᴹ a Γ'ᴹ Γᴹ)
Tmᴹ (tlam t)   Γ'ᴹ Γᴹ = λ σ Bᴹ → Tmᴹ t (Γ'ᴹ , Bᴹ) (Conᴹᵣ σ (Γᴹ ,*)) 
Tmᴹ (tapp t B) Γ'ᴹ Γᴹ = coe {!!} (Tmᴹ t Γ'ᴹ Γᴹ idᵣ (Tyᴹ B Γ'ᴹ)) -- semantic []

