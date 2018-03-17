
module Target.Normalization where

open import Lib
open import Target.Syntax
open import Target.ClosureBuilding

mutual
  data Nf (Γ : Con) : Ty → Set where
    ne    : ∀ {A} → Ne Γ A → Nf Γ A
    lam   : ∀ {A B} → Nf (∙ ▶ A) B → Nf Γ (A ⇒ B)
    _,_   : ∀ {A B} → Nf Γ A → Nf Γ B → Nf Γ (A * B)
    tt    : Nf Γ Top
    pack  : ∀ {A B E} → Nf Γ E → Nf Γ (E * A ⇒ B) → Nf Γ (A ⇒⁺ B)
    true  : Nf Γ 𝔹
    false : Nf Γ 𝔹

  data Ne (Γ : Con) : Ty → Set where
    var  : ∀ {A} → A ∈ Γ → Ne Γ A
    app  : ∀ {A B} → Ne Γ (A ⇒ B) → Nf Γ A → Ne Γ B
    app⁺ : ∀ {A B} → Ne Γ (A ⇒⁺ B) → Nf Γ A → Ne Γ B
    if   : ∀ {A} → Ne Γ 𝔹 → Nf Γ A → Nf Γ A → Ne Γ A
    π₁   : ∀ {A B} → Ne Γ (A * B) → Ne Γ A
    π₂   : ∀ {A B} → Ne Γ (A * B) → Ne Γ B

mutual
  Nfₑ : ∀ {Γ Δ A} → OPE Γ Δ → Nf Δ A → Nf Γ A
  Nfₑ σ (ne x) = ne (Neₑ σ x)
  Nfₑ σ (lam t) = lam t
  Nfₑ σ (t , u) = Nfₑ σ t , Nfₑ σ u
  Nfₑ σ tt = tt
  Nfₑ σ (pack env t) = pack (Nfₑ σ env) (Nfₑ σ t)
  Nfₑ σ true = true
  Nfₑ σ false = false

  Neₑ : ∀ {Γ Δ A} → OPE Γ Δ → Ne Δ A → Ne Γ A
  Neₑ σ (var x) = var (∈ₑ σ x)
  Neₑ σ (app t x) = app (Neₑ σ t) (Nfₑ σ x)
  Neₑ σ (app⁺ t x) = app⁺ (Neₑ σ t) (Nfₑ σ x)
  Neₑ σ (if t x x₁) = if (Neₑ σ t) (Nfₑ σ x) (Nfₑ σ x₁)
  Neₑ σ (π₁ t) = π₁ (Neₑ σ t)
  Neₑ σ (π₂ t) = π₂ (Neₑ σ t)

-- Tyᴹ : Ty → Con → Set
-- Tyᴹ 𝔹        Γ = Nf Γ 𝔹
-- Tyᴹ Top      Γ = ⊤
-- Tyᴹ (A * B)  Γ = Tyᴹ A Γ × Tyᴹ B Γ
-- Tyᴹ (A ⇒⁺ B) Γ = ∀ {Δ} → OPE Δ Γ → Tyᴹ A Δ → Tyᴹ B Δ
-- Tyᴹ (A ⇒ B)  Γ = (∀ {Δ} → Tyᴹ A Δ → Tyᴹ B Δ) ⊎ Ne Γ (A ⇒ B)

-- Conᴹ : Con → Con → Set
-- Conᴹ ∙       Δ = ⊤
-- Conᴹ (Γ ▶ A) Δ = Conᴹ Γ Δ × Tyᴹ A Δ

-- OPEᴹ : ∀ {Γ Δ} → OPE Γ Δ → ∀ {Σ} → Conᴹ Γ Σ → Conᴹ Δ Σ
-- OPEᴹ ∙        Γᴹ        = tt
-- OPEᴹ (drop σ) (Γᴹ , _)  = OPEᴹ σ Γᴹ
-- OPEᴹ (keep σ) (Γᴹ , Aᴹ) = OPEᴹ σ Γᴹ , Aᴹ

-- ∈ᴹ : ∀ {Γ A} → A ∈ Γ → ∀ {Δ} → Conᴹ Γ Δ → Tyᴹ A Δ
-- ∈ᴹ {∙} () Γᴹ
-- ∈ᴹ {Γ ▶ x₁} vz Γᴹ = ₂ Γᴹ
-- ∈ᴹ {Γ ▶ x₁} (vs x) Γᴹ = ∈ᴹ x (₁ Γᴹ)

-- postulate
--   lam⁺ⁿ : ∀ {Γ A B} → Nf (Γ ▶ A) B → Nf Γ (A ⇒⁺ B)
-- -- lam⁺ⁿ t = {!!}

-- Tyᴹₑ : ∀ {A Γ Δ} → OPE Δ Γ → Tyᴹ A Γ → Tyᴹ A Δ
-- Tyᴹₑ {𝔹}      σ t = Nfₑ σ t
-- Tyᴹₑ {Top}    σ t = tt
-- Tyᴹₑ {A * B}  σ t = (Tyᴹₑ σ (₁ t)) , (Tyᴹₑ σ (₂ t))
-- Tyᴹₑ {A ⇒⁺ B} σ t = λ δ a → t (σ ∘ₑ δ) a
-- Tyᴹₑ {A ⇒ B} σ (inl t) = inl t
-- Tyᴹₑ {A ⇒ B} σ (inr t) = inr (Neₑ σ t)

-- Conᴹₑ : ∀ {Γ Δ Σ} → OPE Σ Δ → Conᴹ Γ Δ → Conᴹ Γ Σ
-- Conᴹₑ {∙}     σ tt        = tt
-- Conᴹₑ {_ ▶ _} σ (Γᴹ , tᴹ) = Conᴹₑ σ Γᴹ , Tyᴹₑ σ tᴹ

-- mutual
--   qᴹ : ∀ {A Γ} → Tyᴹ A Γ → Nf Γ A
--   qᴹ {𝔹}      t = t
--   qᴹ {Top}    t = tt
--   qᴹ {A * B}  t = qᴹ (₁ t) , qᴹ (₂ t)
--   qᴹ {A ⇒⁺ B} t = lam⁺ⁿ (qᴹ (t wk (uᴹ (var vz))))
--   qᴹ {A ⇒ B} (inl t) = lam (qᴹ (t (uᴹ (var vz))))
--   qᴹ {A ⇒ B} (inr t) = ne t

--   uᴹ : ∀ {A Γ} → Ne Γ A → Tyᴹ A Γ
--   uᴹ {𝔹}      t = ne t
--   uᴹ {Top}    t = tt
--   uᴹ {A * B}  t = uᴹ (π₁ t) , uᴹ (π₂ t)
--   uᴹ {A ⇒⁺ B} t = λ σ a → uᴹ (app⁺ (Neₑ σ t) (qᴹ a))
--   uᴹ {A ⇒ B}  t = inr t

-- Tmᴹ : ∀ {Γ A} → Tm Γ A → ∀ {Δ} → Conᴹ Γ Δ → Tyᴹ A Δ
-- Tmᴹ (var x) Γᴹ = ∈ᴹ x Γᴹ
-- Tmᴹ tt Γᴹ = tt
-- Tmᴹ true Γᴹ = true
-- Tmᴹ false Γᴹ = false
-- Tmᴹ (if t u v) Γᴹ with Tmᴹ t Γᴹ
-- ... | ne n  = uᴹ (if n (qᴹ (Tmᴹ u Γᴹ)) (qᴹ (Tmᴹ v Γᴹ)))
-- ... | true  = Tmᴹ u Γᴹ
-- ... | false = Tmᴹ v Γᴹ
-- Tmᴹ (π₁ t) Γᴹ = ₁ (Tmᴹ t Γᴹ)
-- Tmᴹ (π₂ t) Γᴹ = ₂ (Tmᴹ t Γᴹ)
-- Tmᴹ (t , u) Γᴹ = Tmᴹ t Γᴹ , Tmᴹ u Γᴹ
-- Tmᴹ {Γ} (pack {E}{A}{B} env t) {Δ} Γᴹ {Σ} =
--   λ σ a → case Tmᴹ t (Conᴹₑ σ Γᴹ) of λ {
--     (inl t) → t (Tmᴹ env (Conᴹₑ σ Γᴹ) , a);
--     (inr t) → uᴹ (Ne.app t (qᴹ (Tmᴹ env (Conᴹₑ σ Γᴹ)) , qᴹ a))}
-- Tmᴹ (app⁺ t u) Γᴹ = Tmᴹ t Γᴹ idₑ (Tmᴹ u Γᴹ)
-- Tmᴹ (lam t) Γᴹ = inl (λ a → Tmᴹ t (tt , a))
-- Tmᴹ (app t u) Γᴹ = case Tmᴹ t Γᴹ of λ {
--   (inl t) → t (Tmᴹ u Γᴹ);
--   (inr t) → uᴹ (Ne.app t (qᴹ (Tmᴹ u Γᴹ)))}

-- uConᴹ : ∀ {Γ} → Conᴹ Γ Γ
-- uConᴹ {∙}     = tt
-- uConᴹ {Γ ▶ A} = Conᴹₑ wk (uConᴹ {Γ}) , uᴹ {A} (var vz)

-- nf : ∀ {Γ A} → Tm Γ A → Nf Γ A
-- nf t = qᴹ (Tmᴹ t uConᴹ)
