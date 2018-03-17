
module Source.StdModel where

open import Lib
open import Source.Syntax
open import Data.Bool

⟦_⟧Ty : Ty → Set
⟦ 𝔹     ⟧Ty = Bool
⟦ A ⇒ B ⟧Ty = ⟦ A ⟧Ty → ⟦ B ⟧Ty

⟦_⟧Con : Con → Set
⟦ ∙     ⟧Con = ⊤
⟦ Γ ▶ A ⟧Con = ⟦ Γ ⟧Con × ⟦ A ⟧Ty

⟦_⟧Tm : ∀ {Γ A} → Tm Γ A → ⟦ Γ ⟧Con → ⟦ A ⟧Ty
⟦ var vz     ⟧Tm γ = ₂ γ
⟦ var (vs x) ⟧Tm γ = ⟦ var x ⟧Tm (₁ γ)
⟦ lam t      ⟧Tm γ = λ α → ⟦ t ⟧Tm (γ , α)
⟦ app t u    ⟧Tm γ = ⟦ t ⟧Tm γ (⟦ u ⟧Tm γ)
⟦ true       ⟧Tm γ = true
⟦ false      ⟧Tm γ = false
⟦ if t u v   ⟧Tm γ = if ⟦ t ⟧Tm γ then ⟦ u ⟧Tm γ else ⟦ v ⟧Tm γ

⟦_⟧OPE : ∀ {Γ Δ} → OPE Γ Δ → ⟦ Γ ⟧Con → ⟦ Δ ⟧Con
⟦ ∙      ⟧OPE γ = tt
⟦ drop σ ⟧OPE γ = ⟦ σ ⟧OPE (₁ γ)
⟦ keep σ ⟧OPE γ = ⟦ σ ⟧OPE (₁ γ) , ₂ γ

⟦_⟧Sub : ∀ {Γ Δ} → Sub Γ Δ → ⟦ Γ ⟧Con → ⟦ Δ ⟧Con
⟦ ∙     ⟧Sub γ = tt
⟦ σ , t ⟧Sub γ = ⟦ σ ⟧Sub γ , ⟦ t ⟧Tm γ

⟦idₑ⟧ : ∀ {Γ} → ⟦ idₑ {Γ} ⟧OPE ≡ id
⟦idₑ⟧ {∙}     = refl
⟦idₑ⟧ {Γ ▶ A} rewrite ⟦idₑ⟧ {Γ} = refl

⟦∈ₑ⟧ : ∀ {Γ Δ A}(σ : OPE Γ Δ)(x : A ∈ Δ) → ⟦ var (∈ₑ σ x) ⟧Tm ≡ ⟦ var x ⟧Tm ∘ ⟦ σ ⟧OPE
⟦∈ₑ⟧ ∙ ()
⟦∈ₑ⟧ (drop σ) x rewrite ⟦∈ₑ⟧ σ x = refl
⟦∈ₑ⟧ (keep σ) vz = refl
⟦∈ₑ⟧ (keep σ) (vs x) rewrite ⟦∈ₑ⟧ σ x = refl

⟦Tmₑ⟧ : ∀ {Γ Δ A}(σ : OPE Γ Δ)(t : Tm Δ A) → ⟦ Tmₑ σ t ⟧Tm ≡ ⟦ t ⟧Tm ∘ ⟦ σ ⟧OPE
⟦Tmₑ⟧ σ (var x) = ⟦∈ₑ⟧ σ x
⟦Tmₑ⟧ σ (lam t) rewrite ⟦Tmₑ⟧ (keep σ) t = refl
⟦Tmₑ⟧ σ (app t u) rewrite ⟦Tmₑ⟧ σ t | ⟦Tmₑ⟧ σ u = refl
⟦Tmₑ⟧ σ true = refl
⟦Tmₑ⟧ σ false = refl
⟦Tmₑ⟧ σ (if t u v) rewrite ⟦Tmₑ⟧ σ t | ⟦Tmₑ⟧ σ u | ⟦Tmₑ⟧ σ v = refl

⟦ₛ∘ₑ⟧ : ∀ {Γ Δ Σ} (σ : Sub Δ Σ)(δ : OPE Γ Δ) → ⟦ σ ₛ∘ₑ δ ⟧Sub ≡ ⟦ σ ⟧Sub ∘ ⟦ δ ⟧OPE
⟦ₛ∘ₑ⟧ ∙       δ = refl
⟦ₛ∘ₑ⟧ (σ , t) δ rewrite ⟦ₛ∘ₑ⟧ σ δ | ⟦Tmₑ⟧ δ t = refl

⟦∈ₛ⟧ : ∀ {Γ Δ A}(σ : Sub Γ Δ)(x : A ∈ Δ) → ⟦ ∈ₛ σ x ⟧Tm ≡ ⟦ var x ⟧Tm ∘ ⟦ σ ⟧Sub
⟦∈ₛ⟧ (σ , x) vz     = refl
⟦∈ₛ⟧ (σ , _) (vs x) = ⟦∈ₛ⟧ σ x

⟦Tmₛ⟧ : ∀ {Γ Δ A}(σ : Sub Γ Δ)(t : Tm Δ A) → ⟦ Tmₛ σ t ⟧Tm ≡ ⟦ t ⟧Tm ∘ ⟦ σ ⟧Sub
⟦Tmₛ⟧ σ (var x) = ⟦∈ₛ⟧ σ x
⟦Tmₛ⟧ {Γ} σ (lam {A} t)
  rewrite ⟦Tmₛ⟧ (keepₛ σ) t | ⟦ₛ∘ₑ⟧ σ (wk{A}) | ⟦idₑ⟧{Γ} = refl
⟦Tmₛ⟧ σ (app t u) rewrite ⟦Tmₛ⟧ σ t | ⟦Tmₛ⟧ σ u = refl
⟦Tmₛ⟧ σ true = refl
⟦Tmₛ⟧ σ false = refl
⟦Tmₛ⟧ σ (if t u v) rewrite ⟦Tmₛ⟧ σ t | ⟦Tmₛ⟧ σ u | ⟦Tmₛ⟧ σ v = refl

⟦idₛ⟧ : ∀ {Γ} → ⟦ idₛ {Γ} ⟧Sub ≡ id
⟦idₛ⟧ {∙}     = refl
⟦idₛ⟧ {Γ ▶ A} rewrite ⟦ₛ∘ₑ⟧ (idₛ{Γ}) (wk{A}) | ⟦idₛ⟧ {Γ} | ⟦idₑ⟧{Γ} = refl

⟦~⟧ : ∀ {Γ A}{t t' : Tm Γ A} → t ~ t' → ⟦ t ⟧Tm ≡ ⟦ t' ⟧Tm
⟦~⟧ {Γ} {B} (β {A} t u) rewrite ⟦Tmₛ⟧ (idₛ , u) t | ⟦idₛ⟧ {Γ} = refl
⟦~⟧ {Γ} (η {A} {B} t) rewrite ⟦Tmₑ⟧ (wk{A}) t | ⟦idₑ⟧ {Γ} = refl
⟦~⟧ (lam p)   rewrite ⟦~⟧ p = refl
⟦~⟧ (app t u) rewrite ⟦~⟧ t | ⟦~⟧ u = refl
⟦~⟧ ~refl      = refl
⟦~⟧ (p ~⁻¹)    = ⟦~⟧ p ⁻¹
⟦~⟧ (p ~◾ q)   = ⟦~⟧ p ◾ ⟦~⟧ q
⟦~⟧ true       = refl
⟦~⟧ false      = refl
⟦~⟧ (if t u v) rewrite ⟦~⟧ t | ⟦~⟧ u | ⟦~⟧ v = refl
