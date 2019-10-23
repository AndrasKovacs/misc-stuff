{-# OPTIONS --without-K --postfix-projections #-}

module BooleanModel where

open import Lib
open import Syntax

Con'ᴹ : Con' → Set
Con'ᴹ ∙      = ⊤
Con'ᴹ (n ,*) = Con'ᴹ n × Bool

*∈ᴹ : ∀ {Γ} → *∈ Γ → Con'ᴹ Γ → Bool
*∈ᴹ vz     Γᴹ = Γᴹ .₂
*∈ᴹ (vs x) Γᴹ = *∈ᴹ x (Γᴹ .₁)

Tyᴹ : ∀ {Γ} → Ty Γ → Con'ᴹ Γ → Bool
Tyᴹ (var x) Γᴹ = *∈ᴹ x Γᴹ
Tyᴹ (A ⇒ B) Γᴹ = if Tyᴹ A Γᴹ then Tyᴹ B Γᴹ else true
Tyᴹ (∀' A)  Γᴹ = Tyᴹ A (Γᴹ , true) ∧ Tyᴹ A (Γᴹ , false)

Conᴹ : ∀ {Γ} → Con Γ → Con'ᴹ Γ → Set
Conᴹ ∙       Γᴹ = ⊤
Conᴹ (Δ , A) Γᴹ = Conᴹ Δ Γᴹ × T (Tyᴹ A Γᴹ)
Conᴹ (Δ ,*)  Γᴹ = Conᴹ Δ (Γᴹ .₁)

OPE'ᴹ : ∀ {Γ Δ} → OPE' Γ Δ → Con'ᴹ Γ → Con'ᴹ Δ
OPE'ᴹ ∙        Γᴹ        = tt
OPE'ᴹ (drop σ) (Γᴹ , Aᴹ) = OPE'ᴹ σ Γᴹ
OPE'ᴹ (keep σ) (Γᴹ , Aᴹ) = OPE'ᴹ σ Γᴹ , Aᴹ

id'ₑᴹ : ∀ {Γ} (Γᴹ : Con'ᴹ Γ) → OPE'ᴹ id'ₑ Γᴹ ≡ Γᴹ
id'ₑᴹ {∙}    Γᴹ        = refl
id'ₑᴹ {Γ ,*} (Γᴹ , Aᴹ) = (_, Aᴹ) & id'ₑᴹ Γᴹ

*∈ₑᴹ :
  ∀ {Γ Δ}(v : *∈ Γ)(σ : OPE' Δ Γ) Γᴹ
  → *∈ᴹ (*∈ₑ σ v) Γᴹ ≡ *∈ᴹ v (OPE'ᴹ σ Γᴹ)
*∈ₑᴹ ()     ∙        Γᴹ
*∈ₑᴹ v      (drop σ) (Γᴹ , Aᴹ) = *∈ₑᴹ v σ Γᴹ
*∈ₑᴹ vz     (keep σ) (Γᴹ , Aᴹ) = refl
*∈ₑᴹ (vs v) (keep σ) (Γᴹ , Aᴹ) = *∈ₑᴹ v σ Γᴹ

Tyₑᴹ :
  ∀ {Γ Δ}(A : Ty Γ)(σ : OPE' Δ Γ) Γᴹ
  → Tyᴹ (Tyₑ σ A) Γᴹ ≡ Tyᴹ A (OPE'ᴹ σ Γᴹ)
Tyₑᴹ (var v) σ Γᴹ = *∈ₑᴹ v σ Γᴹ
Tyₑᴹ (A ⇒ B) σ Γᴹ rewrite Tyₑᴹ A σ Γᴹ | Tyₑᴹ B σ Γᴹ = refl
Tyₑᴹ (∀' A)  σ Γᴹ
  rewrite Tyₑᴹ A (keep σ) (Γᴹ , true) | Tyₑᴹ A (keep σ) (Γᴹ , false) = refl

Sub'ᴹ : ∀ {Γ Δ} → Sub' Γ Δ → Con'ᴹ Γ → Con'ᴹ Δ
Sub'ᴹ ∙       Γᴹ = tt
Sub'ᴹ (σ , A) Γᴹ = Sub'ᴹ σ Γᴹ , Tyᴹ A Γᴹ

*∈ₛᴹ :
  ∀ {Γ Δ}(v : *∈ Γ)(σ : Sub' Δ Γ) Γᴹ
  → Tyᴹ (*∈ₛ σ v) Γᴹ ≡ *∈ᴹ v (Sub'ᴹ σ Γᴹ)
*∈ₛᴹ vz     (σ , A) Γᴹ = refl
*∈ₛᴹ (vs v) (σ , A) Γᴹ = *∈ₛᴹ v σ Γᴹ

ₛ∘'ₑᴹ :
  ∀ {Γ Δ Σ}(σ : Sub' Δ Σ)(δ : OPE' Γ Δ)(Γᴹ : Con'ᴹ Γ)
  → Sub'ᴹ (σ ₛ∘'ₑ δ) Γᴹ ≡ Sub'ᴹ σ (OPE'ᴹ δ Γᴹ)
ₛ∘'ₑᴹ ∙       δ Γᴹ = refl
ₛ∘'ₑᴹ (σ , A) δ Γᴹ = _,_ & ₛ∘'ₑᴹ σ δ Γᴹ ⊗ Tyₑᴹ A δ Γᴹ

Tyₛᴹ :
  ∀ {Γ Δ}(A : Ty Γ)(σ : Sub' Δ Γ) Γᴹ
  → Tyᴹ (Tyₛ σ A) Γᴹ ≡ Tyᴹ A (Sub'ᴹ σ Γᴹ)
Tyₛᴹ (var v) σ Γᴹ = *∈ₛᴹ v σ Γᴹ
Tyₛᴹ (A ⇒ B) σ Γᴹ rewrite Tyₛᴹ A σ Γᴹ | Tyₛᴹ B σ Γᴹ = refl
Tyₛᴹ (∀' A)  σ Γᴹ
  rewrite Tyₛᴹ A (keep'ₛ σ) (Γᴹ , true) | Tyₛᴹ A (keep'ₛ σ) (Γᴹ , false) |
          ₛ∘'ₑᴹ σ wk' (Γᴹ , true) | ₛ∘'ₑᴹ σ wk' (Γᴹ , false) | id'ₑᴹ Γᴹ =
    refl

id'ᴹ : ∀ {Γ} (Γᴹ : Con'ᴹ Γ) → Sub'ᴹ id'ₛ Γᴹ ≡ Γᴹ
id'ᴹ {∙}    Γᴹ        = refl
id'ᴹ {Γ ,*} (Γᴹ , Aᴹ) = (_, Aᴹ) & (ₛ∘'ₑᴹ id'ₛ wk' (Γᴹ , Aᴹ) ◾ Sub'ᴹ id'ₛ & id'ₑᴹ Γᴹ ◾ id'ᴹ Γᴹ)

∈ᴹ : ∀ {Γ Δ A} → A ∈ Δ → (Γᴹ : Con'ᴹ Γ) → Conᴹ Δ Γᴹ → T (Tyᴹ A Γᴹ)
∈ᴹ vz      Γᴹ Δᴹ = ₂ Δᴹ
∈ᴹ (vs v)  Γᴹ Δᴹ = ∈ᴹ v Γᴹ (₁ Δᴹ)
∈ᴹ (vs* {A = A} x) Γᴹ Δᴹ =
  coe (T & (Tyᴹ A & (id'ₑᴹ (Γᴹ .₁) ⁻¹) ◾ Tyₑᴹ A wk' Γᴹ ⁻¹)) (∈ᴹ x (Γᴹ .₁) Δᴹ)

Tmᴹ : ∀ {Γ Δ A} → Tm {Γ} Δ A → (Γᴹ : Con'ᴹ Γ) → Conᴹ Δ Γᴹ → T (Tyᴹ A Γᴹ)
Tmᴹ (var v)    Γᴹ Δᴹ = ∈ᴹ v Γᴹ Δᴹ
Tmᴹ (lam {A} {B} t) Γᴹ Δᴹ with Tyᴹ A Γᴹ | Tmᴹ t Γᴹ
... | false | tᴹ = tt
... | true  | tᴹ = tᴹ (Δᴹ , tt)

Tmᴹ (app {A = A}{B} t u)  Γᴹ Δᴹ with Tyᴹ A Γᴹ | Tmᴹ t Γᴹ Δᴹ | Tmᴹ u Γᴹ Δᴹ
... | true  | tᴹ | uᴹ = tᴹ

Tmᴹ (tlam {A} t) Γᴹ Δᴹ with Tyᴹ A (Γᴹ , true) | Tyᴹ A (Γᴹ , false)
                         | Tmᴹ t (Γᴹ , true) Δᴹ | Tmᴹ t (Γᴹ , false) Δᴹ
... | true | true | tᴹt | tᴹf = tt
Tmᴹ (tapp {A} t B) Γᴹ Δᴹ rewrite Tyₛᴹ A (id'ₛ , B) Γᴹ | id'ᴹ Γᴹ
   with Tyᴹ B Γᴹ | Tyᴹ A (Γᴹ , true)
      | Tyᴹ A (Γᴹ , false) | inspect (Tyᴹ A) (Γᴹ , true) | inspect (Tyᴹ A) (Γᴹ , false)
      | Tmᴹ t Γᴹ Δᴹ
... | true  | true | true | [ eq1 ] | [ eq2 ] | tᴹ = coe (T & eq1 ⁻¹) tt
... | false | true | true | [ eq1 ] | [ eq2 ] | tᴹ = coe (T & eq2 ⁻¹) tt

consistent : Tm ∙ (∀' (var vz)) → ⊥
consistent t = Tmᴹ t _ _
