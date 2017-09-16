{-# OPTIONS --without-K #-}

module Substitution where

open import Lib
open import Syntax
open import Embedding

infixr 6 _ₑ∘ₛ_ _ₛ∘ₑ_ _∘ₛ_

data Sub (Γ : ℕ) : ℕ → Set where
  ∙   : Sub Γ zero
  _,_ : ∀ {Δ} → Sub Γ Δ → Tm Γ → Sub Γ (suc Δ)

_ₛ∘ₑ_ : ∀ {Γ Δ Σ} → Sub Δ Σ → OPE Γ Δ → Sub Γ Σ
∙       ₛ∘ₑ δ = ∙
(σ , t) ₛ∘ₑ δ = (σ ₛ∘ₑ δ) , Tmₑ δ t

_ₑ∘ₛ_ : ∀ {Γ Δ Σ} → OPE Δ Σ → Sub Γ Δ → Sub Γ Σ
∙      ₑ∘ₛ δ       = δ
drop σ ₑ∘ₛ (δ , t) = σ ₑ∘ₛ δ
keep σ ₑ∘ₛ (δ , t) = σ ₑ∘ₛ δ , t

dropₛ : ∀ {Γ Δ} → Sub Γ Δ → Sub (suc Γ) Δ
dropₛ σ = σ ₛ∘ₑ wk

keepₛ : ∀ {Γ Δ} → Sub Γ Δ → Sub (suc Γ) (suc Δ)
keepₛ σ = dropₛ σ , var zero

⌜_⌝ᵒᵖᵉ : ∀ {Γ Δ} → OPE Γ Δ → Sub Γ Δ
⌜ ∙      ⌝ᵒᵖᵉ = ∙
⌜ drop σ ⌝ᵒᵖᵉ = dropₛ ⌜ σ ⌝ᵒᵖᵉ
⌜ keep σ ⌝ᵒᵖᵉ = keepₛ ⌜ σ ⌝ᵒᵖᵉ

∈ₛ : ∀ {Γ Δ} → Sub Γ Δ → Fin Δ → Tm Γ
∈ₛ (σ , t) zero    = t
∈ₛ (σ , t) (suc v) = ∈ₛ σ v

mutual
  Tmₛ : ∀ {Γ Δ} → Sub Γ Δ → Tm Δ → Tm Γ
  Tmₛ σ (var x)   = ∈ₛ σ x
  Tmₛ σ (lam A t) = lam (Tyₛ σ A) (Tmₛ (keepₛ σ) t)
  Tmₛ σ (app f a) = app (Tmₛ σ f) (Tmₛ σ a)

  Tyₛ : ∀ {Γ Δ} → Sub Γ Δ → Ty Δ → Ty Γ
  Tyₛ σ U       = U
  Tyₛ σ (El t)  = El (Tmₛ σ t)
  Tyₛ σ (Π A B) = Π (Tyₛ σ A) (Tyₛ (keepₛ σ) B)

idₛ : ∀ {Γ} → Sub Γ Γ
idₛ {zero}  = ∙
idₛ {suc Γ} = keepₛ idₛ

_∘ₛ_ : ∀ {Γ Δ Σ} → Sub Δ Σ → Sub Γ Δ → Sub Γ Σ
∙       ∘ₛ δ = ∙
(σ , t) ∘ₛ δ = σ ∘ₛ δ , Tmₛ δ t

assₛₑₑ :
  ∀ {Γ Δ Σ Ξ}(σ : Sub Σ Ξ)(δ : OPE Δ Σ)(ν : OPE Γ Δ)
  → (σ ₛ∘ₑ δ) ₛ∘ₑ ν ≡ σ ₛ∘ₑ (δ ∘ₑ ν)
assₛₑₑ ∙       δ ν = refl
assₛₑₑ (σ , t) δ ν = _,_ & assₛₑₑ σ δ ν ⊗ (Tm-∘ₑ δ ν t ⁻¹)

assₑₛₑ :
  ∀ {Γ Δ Σ Ξ}(σ : OPE Σ Ξ)(δ : Sub Δ Σ)(ν : OPE Γ Δ)
  → (σ ₑ∘ₛ δ) ₛ∘ₑ ν ≡ σ ₑ∘ₛ (δ ₛ∘ₑ ν)
assₑₛₑ ∙        δ       ν = refl
assₑₛₑ (drop σ) (δ , t) ν = assₑₛₑ σ δ ν
assₑₛₑ (keep σ) (δ , t) ν = (_, Tmₑ ν t) & assₑₛₑ σ δ ν

idlₑₛ : ∀ {Γ Δ}(σ : Sub Γ Δ) → idₑ ₑ∘ₛ σ ≡ σ
idlₑₛ ∙       = refl
idlₑₛ (σ , t) = (_, t) & idlₑₛ σ

idlₛₑ : ∀ {Γ Δ}(σ : OPE Γ Δ) → idₛ ₛ∘ₑ σ ≡ ⌜ σ ⌝ᵒᵖᵉ
idlₛₑ ∙        = refl
idlₛₑ (drop σ) =
      ((idₛ ₛ∘ₑ_) ∘ drop) & idrₑ σ ⁻¹
    ◾ assₛₑₑ idₛ σ wk ⁻¹
    ◾ dropₛ & idlₛₑ σ
idlₛₑ (keep σ) =
  (_, var zero) &
      (assₛₑₑ idₛ wk (keep σ)
    ◾ ((idₛ ₛ∘ₑ_) ∘ drop) & (idlₑ σ ◾ idrₑ σ ⁻¹)
    ◾ assₛₑₑ idₛ σ wk ⁻¹
    ◾ (_ₛ∘ₑ wk) & idlₛₑ σ )

idrₑₛ : ∀ {Γ Δ}(σ : OPE Γ Δ) → σ ₑ∘ₛ idₛ ≡ ⌜ σ ⌝ᵒᵖᵉ
idrₑₛ ∙        = refl
idrₑₛ (drop σ) = assₑₛₑ σ idₛ wk ⁻¹ ◾ dropₛ & idrₑₛ σ
idrₑₛ (keep σ) = (_, var zero) & (assₑₛₑ σ idₛ wk ⁻¹ ◾ (_ₛ∘ₑ wk) & idrₑₛ σ)

∈-ₑ∘ₛ : ∀ {Γ Δ Σ}(σ : OPE Δ Σ)(δ : Sub Γ Δ)(v : Fin Σ) → ∈ₛ (σ ₑ∘ₛ δ) v ≡ ∈ₛ δ (∈ₑ σ v)
∈-ₑ∘ₛ ∙        δ       v       = refl
∈-ₑ∘ₛ (drop σ) (δ , t) v       = ∈-ₑ∘ₛ σ δ v
∈-ₑ∘ₛ (keep σ) (δ , t) zero    = refl
∈-ₑ∘ₛ (keep σ) (δ , t) (suc v) = ∈-ₑ∘ₛ σ δ v

mutual
  Tm-ₑ∘ₛ : ∀ {Γ Δ Σ}(σ : OPE Δ Σ)(δ : Sub Γ Δ)(t : Tm Σ) → Tmₛ (σ ₑ∘ₛ δ) t ≡ Tmₛ δ (Tmₑ σ t)
  Tm-ₑ∘ₛ σ δ (var v) = ∈-ₑ∘ₛ σ δ v
  Tm-ₑ∘ₛ σ δ (lam A t) =
    lam & Ty-ₑ∘ₛ σ δ A ⊗ ((λ x → Tmₛ (x , var zero) t) & assₑₛₑ σ δ wk ◾ Tm-ₑ∘ₛ (keep σ) (keepₛ δ) t)
  Tm-ₑ∘ₛ σ δ (app f a) = app & Tm-ₑ∘ₛ σ δ f ⊗ Tm-ₑ∘ₛ σ δ a

  Ty-ₑ∘ₛ : ∀ {Γ Δ Σ}(σ : OPE Δ Σ)(δ : Sub Γ Δ)(A : Ty Σ) → Tyₛ (σ ₑ∘ₛ δ) A ≡ Tyₛ δ (Tyₑ σ A)
  Ty-ₑ∘ₛ σ δ U       = refl
  Ty-ₑ∘ₛ σ δ (El t)  = El & Tm-ₑ∘ₛ σ δ t
  Ty-ₑ∘ₛ σ δ (Π A B) = Π & Ty-ₑ∘ₛ σ δ A ⊗
    (((λ x → Tyₛ (x , var zero) B) & assₑₛₑ σ δ wk ◾ Ty-ₑ∘ₛ (keep σ) (keepₛ δ) B))

∈-ₛ∘ₑ : ∀ {Γ Δ Σ}(σ : Sub Δ Σ)(δ : OPE Γ Δ)(v : Fin Σ) → ∈ₛ (σ ₛ∘ₑ δ) v ≡ Tmₑ δ (∈ₛ σ v)
∈-ₛ∘ₑ (σ , _) δ zero    = refl
∈-ₛ∘ₑ (σ , _) δ (suc v) = ∈-ₛ∘ₑ σ δ v

mutual
  Tm-ₛ∘ₑ : ∀ {Γ Δ Σ}(σ : Sub Δ Σ)(δ : OPE Γ Δ)(t : Tm Σ) → Tmₛ (σ ₛ∘ₑ δ) t ≡ Tmₑ δ (Tmₛ σ t)
  Tm-ₛ∘ₑ σ δ (var v)   = ∈-ₛ∘ₑ σ δ v
  Tm-ₛ∘ₑ σ δ (lam A t) =
    lam & Ty-ₛ∘ₑ σ δ A ⊗
        ((λ x → Tmₛ (x , var zero) t) &
            (assₛₑₑ σ δ wk
          ◾ (σ ₛ∘ₑ_) & (drop & (idrₑ δ ◾ idlₑ δ ⁻¹))
          ◾ assₛₑₑ σ wk (keep δ) ⁻¹)
      ◾ Tm-ₛ∘ₑ (keepₛ σ) (keep δ) t)
  Tm-ₛ∘ₑ σ δ (app f a) = app & Tm-ₛ∘ₑ σ δ f ⊗ Tm-ₛ∘ₑ σ δ a

  Ty-ₛ∘ₑ : ∀ {Γ Δ Σ}(σ : Sub Δ Σ)(δ : OPE Γ Δ)(A : Ty Σ) → Tyₛ (σ ₛ∘ₑ δ) A ≡ Tyₑ δ (Tyₛ σ A)
  Ty-ₛ∘ₑ σ δ U       = refl
  Ty-ₛ∘ₑ σ δ (El t)  = El & Tm-ₛ∘ₑ σ δ t
  Ty-ₛ∘ₑ σ δ (Π A B) =
    Π & Ty-ₛ∘ₑ σ δ A ⊗
        ((λ x → Tyₛ (x , var zero) B) &
            (assₛₑₑ σ δ wk
          ◾ (σ ₛ∘ₑ_) & (drop & (idrₑ δ ◾ idlₑ δ ⁻¹))
          ◾ assₛₑₑ σ wk (keep δ) ⁻¹)
      ◾ Ty-ₛ∘ₑ (keepₛ σ) (keep δ) B)

assₛₑₛ :
  ∀ {Γ Δ Σ Ξ}(σ : Sub Σ Ξ)(δ : OPE Δ Σ)(ν : Sub Γ Δ)
  → (σ ₛ∘ₑ δ) ∘ₛ ν ≡ σ ∘ₛ (δ ₑ∘ₛ ν)
assₛₑₛ ∙       δ ν = refl
assₛₑₛ (σ , t) δ ν = _,_ & assₛₑₛ σ δ ν ⊗ (Tm-ₑ∘ₛ δ ν t ⁻¹)

assₛₛₑ :
  ∀ {Γ Δ Σ Ξ}(σ : Sub Σ Ξ)(δ : Sub Δ Σ)(ν : OPE Γ Δ)
  → (σ ∘ₛ δ) ₛ∘ₑ ν ≡ σ ∘ₛ (δ ₛ∘ₑ ν)
assₛₛₑ ∙       δ ν = refl
assₛₛₑ (σ , t) δ ν = _,_ & assₛₛₑ σ δ ν ⊗ (Tm-ₛ∘ₑ δ ν t ⁻¹)

∈-∘ₛ : ∀ {Γ Δ Σ}(σ : Sub Δ Σ)(δ : Sub Γ Δ)(v : Fin Σ) → ∈ₛ (σ ∘ₛ δ) v ≡ Tmₛ δ (∈ₛ σ v)
∈-∘ₛ (σ , _) δ zero    = refl
∈-∘ₛ (σ , _) δ (suc v) = ∈-∘ₛ σ δ v

mutual
  Tm-∘ₛ : ∀ {Γ Δ Σ}(σ : Sub Δ Σ)(δ : Sub Γ Δ)(t : Tm Σ) → Tmₛ (σ ∘ₛ δ) t ≡ Tmₛ δ (Tmₛ σ t)
  Tm-∘ₛ σ δ (var v)   = ∈-∘ₛ σ δ v
  Tm-∘ₛ σ δ (lam A t) =
    lam & Ty-∘ₛ σ δ A  ⊗
        ((λ x → Tmₛ (x , var zero) t) &
            (assₛₛₑ σ δ wk
          ◾ (σ ∘ₛ_) & (idlₑₛ  (dropₛ δ) ⁻¹) ◾ assₛₑₛ σ wk (keepₛ δ) ⁻¹)
      ◾ Tm-∘ₛ (keepₛ σ) (keepₛ δ) t)
  Tm-∘ₛ σ δ (app f a) = app & Tm-∘ₛ σ δ f ⊗ Tm-∘ₛ σ δ a

  Ty-∘ₛ : ∀ {Γ Δ Σ}(σ : Sub Δ Σ)(δ : Sub Γ Δ)(A : Ty Σ) → Tyₛ (σ ∘ₛ δ) A ≡ Tyₛ δ (Tyₛ σ A)
  Ty-∘ₛ σ δ U       = refl
  Ty-∘ₛ σ δ (El t)  = El & Tm-∘ₛ σ δ t
  Ty-∘ₛ σ δ (Π A B) = Π & Ty-∘ₛ σ δ A ⊗
      ((λ x → Tyₛ (x , var zero) B) &
          (assₛₛₑ σ δ wk
        ◾ (σ ∘ₛ_) & (idlₑₛ  (dropₛ δ) ⁻¹) ◾ assₛₑₛ σ wk (keepₛ δ) ⁻¹)
    ◾ Ty-∘ₛ (keepₛ σ) (keepₛ δ) B)

∈-idₛ : ∀ {Γ}(v : Fin Γ) → ∈ₛ idₛ v ≡ var v
∈-idₛ zero    = refl
∈-idₛ (suc v) = ∈-ₛ∘ₑ idₛ wk v ◾ Tmₑ wk & ∈-idₛ v ◾ (var ∘ suc) & ∈-idₑ v

mutual
  Tm-idₛ : ∀ {Γ}(t : Tm Γ) → Tmₛ idₛ t ≡ t
  Tm-idₛ (var v)   = ∈-idₛ v
  Tm-idₛ (lam A t) = lam & Ty-idₛ A ⊗ Tm-idₛ t
  Tm-idₛ (app f a) = app & Tm-idₛ f ⊗ Tm-idₛ a

  Ty-idₛ : ∀ {Γ}(A : Ty Γ) → Tyₛ idₛ A ≡ A
  Ty-idₛ U       = refl
  Ty-idₛ (El t)  = El & Tm-idₛ t
  Ty-idₛ (Π A B) = Π & Ty-idₛ A ⊗ Ty-idₛ B

idrₛ : ∀ {Γ Δ}(σ : Sub Γ Δ) → σ ∘ₛ idₛ ≡ σ
idrₛ ∙       = refl
idrₛ (σ , t) = _,_ & idrₛ σ ⊗ Tm-idₛ t

idlₛ : ∀ {Γ Δ}(σ : Sub Γ Δ) → idₛ ∘ₛ σ ≡ σ
idlₛ ∙       = refl
idlₛ (σ , t) = (_, t) & (assₛₑₛ idₛ wk (σ , t) ◾ idlₛ (idₑ ₑ∘ₛ σ) ◾ idlₑₛ σ)

assₛ :
  ∀ {Γ Δ Σ Ξ}(σ : Sub Σ Ξ)(δ : Sub Δ Σ)(ν : Sub Γ Δ)
  → (σ ∘ₛ δ) ∘ₛ ν ≡ σ ∘ₛ (δ ∘ₛ ν)
assₛ ∙       δ ν = refl
assₛ (σ , t) δ ν = _,_ & assₛ σ δ ν ⊗ (Tm-∘ₛ δ ν t ⁻¹)
