{-# OPTIONS --without-K --type-in-type #-}

-- Standard model with an impredicative semantic Set₀

module StdModel where

open import Lib
open import Syntax

Con'ᴹ : Con' → Set
Con'ᴹ ∙      = ⊤
Con'ᴹ (Γ ,*) = Con'ᴹ Γ × Set

*∈ᴹ : ∀ {Γ} → *∈ Γ → Con'ᴹ Γ → Set
*∈ᴹ vz     (Γᴹ , Aᴹ) = Aᴹ
*∈ᴹ (vs v) (Γᴹ , _ ) = *∈ᴹ v Γᴹ

Tyᴹ : ∀ {Γ} → Ty Γ → Con'ᴹ Γ → Set
Tyᴹ (var v) Γᴹ = *∈ᴹ v Γᴹ
Tyᴹ (A ⇒ B) Γᴹ = Tyᴹ A Γᴹ → Tyᴹ B Γᴹ
Tyᴹ (∀' A)  Γᴹ = ∀ Bᴹ → Tyᴹ A (Γᴹ , Bᴹ)

Conᴹ : ∀ {Γ} → Con Γ → Con'ᴹ Γ → Set
Conᴹ ∙       Γᴹ = ⊤
Conᴹ (Δ , A) Γᴹ = Conᴹ Δ Γᴹ × Tyᴹ A Γᴹ
Conᴹ (Δ ,* ) Γᴹ = Conᴹ Δ (proj₁ Γᴹ)

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
Tyₑᴹ (A ⇒ B) σ Γᴹ = (λ x y → x → y) & Tyₑᴹ A σ Γᴹ ⊗ Tyₑᴹ B σ Γᴹ
Tyₑᴹ (∀' A)  σ Γᴹ = Π-≡ refl (λ Bᴹ → Tyₑᴹ A (keep σ) (Γᴹ , Bᴹ))

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
Tyₛᴹ (A ⇒ B) σ Γᴹ = (λ x y → x → y) & Tyₛᴹ A σ Γᴹ ⊗ Tyₛᴹ B σ Γᴹ
Tyₛᴹ (∀' A)  σ Γᴹ = Π-≡ refl λ Bᴹ →
  Tyₛᴹ A (keep'ₛ σ) (Γᴹ , Bᴹ) ◾ (λ x → Tyᴹ A (x , Bᴹ)) &
  (ₛ∘'ₑᴹ σ wk' (Γᴹ , Bᴹ) ◾ Sub'ᴹ σ & id'ₑᴹ Γᴹ)

id'ᴹ : ∀ {Γ} (Γᴹ : Con'ᴹ Γ) → Sub'ᴹ id'ₛ Γᴹ ≡ Γᴹ
id'ᴹ {∙}    Γᴹ        = refl
id'ᴹ {Γ ,*} (Γᴹ , Aᴹ) = (_, Aᴹ)
  & (ₛ∘'ₑᴹ id'ₛ wk' (Γᴹ , Aᴹ)
  ◾ Sub'ᴹ id'ₛ & id'ₑᴹ Γᴹ
  ◾ id'ᴹ Γᴹ)

∈ᴹ : ∀ {Γ Δ A} → A ∈ Δ → (Γᴹ : Con'ᴹ Γ) → Conᴹ Δ Γᴹ → Tyᴹ A Γᴹ
∈ᴹ vz      Γᴹ Δᴹ = proj₂ Δᴹ
∈ᴹ (vs v)  Γᴹ Δᴹ = ∈ᴹ v Γᴹ (proj₁ Δᴹ)
∈ᴹ (vs* {A = A} v) Γᴹ Δᴹ =
  coe (Tyᴹ A & (id'ₑᴹ _ ⁻¹) ◾ Tyₑᴹ A wk' Γᴹ ⁻¹)
      (∈ᴹ v (proj₁ Γᴹ) Δᴹ)

Tmᴹ : ∀ {Γ Δ A} → Tm {Γ} Δ A → (Γᴹ : Con'ᴹ Γ) → Conᴹ Δ Γᴹ → Tyᴹ A Γᴹ
Tmᴹ (var v)    Γᴹ Δᴹ = ∈ᴹ v Γᴹ Δᴹ
Tmᴹ (lam t)    Γᴹ Δᴹ = λ Aᴹ → Tmᴹ t Γᴹ (Δᴹ , Aᴹ)
Tmᴹ (app f a)  Γᴹ Δᴹ = Tmᴹ f Γᴹ Δᴹ (Tmᴹ a Γᴹ Δᴹ)
Tmᴹ (tlam t)   Γᴹ Δᴹ = λ Bᴹ → Tmᴹ t (Γᴹ , Bᴹ) Δᴹ
Tmᴹ (tapp {A} t B) Γᴹ Δᴹ =
  coe
      ((λ x → Tyᴹ A (x , Tyᴹ B Γᴹ)) & (id'ᴹ Γᴹ ⁻¹)
    ◾ Tyₛᴹ A (id'ₛ , B) Γᴹ ⁻¹)
  (Tmᴹ t Γᴹ Δᴹ (Tyᴹ B Γᴹ))


-- examples
ID : Tm ∙ (∀' (var vz ⇒ var vz))
ID = tlam (lam (var vz))

IDᴹ : ∀ A → A → A
IDᴹ = Tmᴹ ID _ _

ID' : Tm ∙ (∀' (var vz ⇒ var vz))
ID' = app (tapp ID (∀' (var vz ⇒ var vz))) ID

ID'ᴹ : ∀ A → A → A
ID'ᴹ = Tmᴹ ID' _ _

test : IDᴹ ≡ ID'ᴹ
test = refl

