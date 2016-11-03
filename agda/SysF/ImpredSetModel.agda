{-# OPTIONS --without-K --type-in-type #-}

{-
Model with an impredicative semantic Set
-}

module ImpredSetModel where

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

Ren'ᴹ : ∀ {Γ Δ} → Ren' Γ Δ → Con'ᴹ Γ → Con'ᴹ Δ
Ren'ᴹ ∙        Γᴹ        = tt
Ren'ᴹ (drop σ) (Γᴹ , Aᴹ) = Ren'ᴹ σ Γᴹ
Ren'ᴹ (keep σ) (Γᴹ , Aᴹ) = Ren'ᴹ σ Γᴹ , Aᴹ

id'ᵣᴹ : ∀ {Γ} (Γᴹ : Con'ᴹ Γ) → Ren'ᴹ id'ᵣ Γᴹ ≡ Γᴹ
id'ᵣᴹ {∙}    Γᴹ        = refl
id'ᵣᴹ {Γ ,*} (Γᴹ , Aᴹ) = (_, Aᴹ) & id'ᵣᴹ Γᴹ

[]∈ₖᵣᴹ :
  ∀ {Γ Δ}(v : *∈ Γ)(σ : Ren' Δ Γ) Γᴹ
  → *∈ᴹ (v [ σ ]∈'ᵣ) Γᴹ ≡ *∈ᴹ v (Ren'ᴹ σ Γᴹ)
[]∈ₖᵣᴹ ()     ∙        Γᴹ
[]∈ₖᵣᴹ v      (drop σ) (Γᴹ , Aᴹ) = []∈ₖᵣᴹ v σ Γᴹ
[]∈ₖᵣᴹ vz     (keep σ) (Γᴹ , Aᴹ) = refl
[]∈ₖᵣᴹ (vs v) (keep σ) (Γᴹ , Aᴹ) = []∈ₖᵣᴹ v σ Γᴹ

[]'ᵣᴹ :
  ∀ {Γ Δ}(A : Ty Γ)(σ : Ren' Δ Γ) Γᴹ
  → Tyᴹ (A [ σ ]'ᵣ) Γᴹ ≡ Tyᴹ A (Ren'ᴹ σ Γᴹ)
[]'ᵣᴹ (var v) σ Γᴹ = []∈ₖᵣᴹ v σ Γᴹ
[]'ᵣᴹ (A ⇒ B) σ Γᴹ = (λ x y → x → y) & []'ᵣᴹ A σ Γᴹ ⊗ []'ᵣᴹ B σ Γᴹ
[]'ᵣᴹ (∀' A)  σ Γᴹ = Π-≡ refl (λ Bᴹ → []'ᵣᴹ A (keep σ) (Γᴹ , Bᴹ))

Sub'ᴹ : ∀ {Γ Δ} → Sub' Γ Δ → Con'ᴹ Γ → Con'ᴹ Δ
Sub'ᴹ ∙       Γᴹ = tt
Sub'ᴹ (σ , A) Γᴹ = Sub'ᴹ σ Γᴹ , Tyᴹ A Γᴹ

[]∈'ᴹ :
  ∀ {Γ Δ}(v : *∈ Γ)(σ : Sub' Δ Γ) Γᴹ
  → Tyᴹ (v [ σ ]∈') Γᴹ ≡ *∈ᴹ v (Sub'ᴹ σ Γᴹ)
[]∈'ᴹ vz     (σ , A) Γᴹ = refl
[]∈'ᴹ (vs v) (σ , A) Γᴹ = []∈'ᴹ v σ Γᴹ

ₛ∘'ᵣᴹ :
  ∀ {Γ Δ Σ}(σ : Sub' Δ Σ)(δ : Ren' Γ Δ)(Γᴹ : Con'ᴹ Γ)
  → Sub'ᴹ (σ ₛ∘'ᵣ δ) Γᴹ ≡ Sub'ᴹ σ (Ren'ᴹ δ Γᴹ)
ₛ∘'ᵣᴹ ∙       δ Γᴹ = refl
ₛ∘'ᵣᴹ (σ , A) δ Γᴹ = _,_ & ₛ∘'ᵣᴹ σ δ Γᴹ ⊗ []'ᵣᴹ A δ Γᴹ  

[]'ᴹ :
  ∀ {Γ Δ}(A : Ty Γ)(σ : Sub' Δ Γ) Γᴹ
  → Tyᴹ (A [ σ ]') Γᴹ ≡ Tyᴹ A (Sub'ᴹ σ Γᴹ)
[]'ᴹ (var v) σ Γᴹ = []∈'ᴹ v σ Γᴹ
[]'ᴹ (A ⇒ B) σ Γᴹ = (λ x y → x → y) & []'ᴹ A σ Γᴹ ⊗ []'ᴹ B σ Γᴹ
[]'ᴹ (∀' A)  σ Γᴹ = Π-≡ refl λ Bᴹ → 
  []'ᴹ A (keep'ₛ σ) (Γᴹ , Bᴹ) ◾ (λ x → Tyᴹ A (x , Bᴹ)) &
  (ₛ∘'ᵣᴹ σ wk' (Γᴹ , Bᴹ) ◾ Sub'ᴹ σ & id'ᵣᴹ Γᴹ)

id'ᴹ : ∀ {Γ} (Γᴹ : Con'ᴹ Γ) → Sub'ᴹ id'ₛ Γᴹ ≡ Γᴹ
id'ᴹ {∙}    Γᴹ        = refl
id'ᴹ {Γ ,*} (Γᴹ , Aᴹ) = (_, Aᴹ)
  & (ₛ∘'ᵣᴹ id'ₛ wk' (Γᴹ , Aᴹ)
  ◾ Sub'ᴹ id'ₛ & id'ᵣᴹ Γᴹ
  ◾ id'ᴹ Γᴹ)

∈ᴹ : ∀ {Γ Δ A} → A ∈ Δ → (Γᴹ : Con'ᴹ Γ) → Conᴹ Δ Γᴹ → Tyᴹ A Γᴹ
∈ᴹ vz      Γᴹ Δᴹ = proj₂ Δᴹ
∈ᴹ (vs v)  Γᴹ Δᴹ = ∈ᴹ v Γᴹ (proj₁ Δᴹ)
∈ᴹ (vs* {A = A} v) Γᴹ Δᴹ =
  coe (Tyᴹ A & (id'ᵣᴹ _ ⁻¹) ◾ []'ᵣᴹ A wk' Γᴹ ⁻¹)
      (∈ᴹ v (proj₁ Γᴹ) Δᴹ)

Tmᴹ : ∀ {Γ Δ A} → Tm {Γ} Δ A → (Γᴹ : Con'ᴹ Γ) → Conᴹ Δ Γᴹ → Tyᴹ A Γᴹ
Tmᴹ (var v)    Γᴹ Δᴹ = ∈ᴹ v Γᴹ Δᴹ
Tmᴹ (lam t)    Γᴹ Δᴹ = λ Aᴹ → Tmᴹ t Γᴹ (Δᴹ , Aᴹ)
Tmᴹ (app f a)  Γᴹ Δᴹ = Tmᴹ f Γᴹ Δᴹ (Tmᴹ a Γᴹ Δᴹ)
Tmᴹ (tlam t)   Γᴹ Δᴹ = λ Bᴹ → Tmᴹ t (Γᴹ , Bᴹ) Δᴹ
Tmᴹ (tapp {A} t B) Γᴹ Δᴹ =
  coe
      ((λ x → Tyᴹ A (x , Tyᴹ B Γᴹ)) & (id'ᴹ Γᴹ ⁻¹)
    ◾ []'ᴹ A (id'ₛ , B) Γᴹ ⁻¹)
  (Tmᴹ t Γᴹ Δᴹ (Tyᴹ B Γᴹ))

foo : Tm ∙ (∀' (var vz ⇒ ∀' (var vz ⇒ var (vs vz))))
foo = tlam (lam (tlam (lam (var (vs (vs* vz))))))

-- bar : Tm ∙ 

