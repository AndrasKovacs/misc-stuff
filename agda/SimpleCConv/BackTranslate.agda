{-# OPTIONS --without-K #-}

module BackTranslate where

open import Lib
import Source.Syntax as S
import Target.Syntax as T
import Target.Normalization as T
open import CConv

-- data Tr : T.Ty → Set where
--   𝔹    : Tr T.𝔹
--   _⇒⁺_ : ∀ {A B} → Tr A → Tr B → Tr (A T.⇒⁺ B)

-- data Tr* : T.Con → Set where
--   ∙   : Tr* T.∙
--   _▶_ : ∀ {Γ A} → Tr* Γ → Tr A → Tr* (Γ T.▶ A)

Tyᴹ : T.Ty → S.Con → Set
Tyᴹ T.𝔹        Γ = S.Tm Γ S.𝔹
Tyᴹ T.Top      Γ = ⊤
Tyᴹ (A T.* B)  Γ = Tyᴹ A Γ × Tyᴹ B Γ
Tyᴹ (A T.⇒⁺ B) Γ = ∀ {Δ} → S.OPE Δ Γ → Tyᴹ A Δ → Tyᴹ B Δ
Tyᴹ (A T.⇒ B)  Γ = ∀ {Δ} → Tyᴹ A Δ → Tyᴹ B Δ

Conᴹ : S.Con → S.Con → Set
Conᴹ S.∙       Δ = ⊤
Conᴹ (Γ S.▶ A) Δ = Conᴹ Γ Δ × Tyᴹ (Ty⁺ A) Δ

OPEᴹ : ∀ {Γ Δ} → S.OPE Γ Δ → ∀ {Σ} → Conᴹ Γ Σ → Conᴹ Δ Σ
OPEᴹ S.∙        Γᴹ        = tt
OPEᴹ (S.drop σ) (Γᴹ , _)  = OPEᴹ σ Γᴹ
OPEᴹ (S.keep σ) (Γᴹ , Aᴹ) = OPEᴹ σ Γᴹ , Aᴹ

Tyᴹₑ : ∀ {A Γ Δ} → S.OPE Δ Γ → Tyᴹ A Γ → Tyᴹ A Δ
Tyᴹₑ = {!!}

Conᴹₑ : ∀ {Γ Δ Σ} → S.OPE Σ Δ → Conᴹ Γ Δ → Conᴹ Γ Σ
Conᴹₑ = {!!}

-- all neutrals have translation type!

mutual
  qᴹ : ∀ {A Γ} → Tyᴹ A Γ → S.Tm Γ {!!} ⊎ T.Nf (Con⁺ Γ) A
  qᴹ {T.𝔹} t = inl t
  qᴹ {T.Top} t = inr T.tt
  qᴹ {A T.* B} t = inr ({!qᴹ {A} ?!} T., {!!})
  qᴹ {A T.⇒⁺ B} t = {!!}
  qᴹ {A T.⇒ B} t = {!!}

  uᴹ : ∀ {A Γ} → {!!} → Tyᴹ A Γ
  uᴹ {A} = {!!}

∈ᴹ : ∀ {Γ A} → A T.∈ (Con⁺ Γ) → ∀ {Δ} → Conᴹ Γ Δ → Tyᴹ A Δ
∈ᴹ {S.∙} () Γᴹ
∈ᴹ {Γ S.▶ x₁} T.vz Γᴹ = ₂ Γᴹ
∈ᴹ {Γ S.▶ x₁} (T.vs x) Γᴹ = ∈ᴹ x (₁ Γᴹ)

Tmᴹ : ∀ {Γ A} → T.Tm (Con⁺ Γ) A → ∀ {Δ} → Conᴹ Γ Δ → Tyᴹ A Δ
Tmᴹ (T.var x) Γᴹ = ∈ᴹ x Γᴹ
Tmᴹ T.tt Γᴹ = tt
Tmᴹ T.true Γᴹ = S.true
Tmᴹ T.false Γᴹ = S.false
Tmᴹ (T.if t u v) Γᴹ with Tmᴹ t Γᴹ
... | S.true  = Tmᴹ u Γᴹ
... | S.false = Tmᴹ v Γᴹ
... | n       = uᴹ (S.Tm.if n {!Tmᴹ u Γᴹ!} {!!})
Tmᴹ (T.π₁ t) Γᴹ = ₁ (Tmᴹ t Γᴹ)
Tmᴹ (T.π₂ t) Γᴹ = ₂ (Tmᴹ t Γᴹ)
Tmᴹ (t T., u) Γᴹ = Tmᴹ t Γᴹ , Tmᴹ u Γᴹ
Tmᴹ (T.pack env t) Γᴹ = λ σ a → Tmᴹ t (Conᴹₑ σ Γᴹ) (Tmᴹ env (Conᴹₑ σ Γᴹ) , a)
Tmᴹ (T.app⁺ t u) Γᴹ = Tmᴹ t Γᴹ S.idₑ (Tmᴹ u Γᴹ)
Tmᴹ (T.lam t) Γᴹ = λ a → {!!}
Tmᴹ (T.app t u) Γᴹ = Tmᴹ t Γᴹ (Tmᴹ u Γᴹ)

  -- qᴹ : ∀ {A Γ} → Tyᴹ (Ty⁺ A) Γ → S.Tm Γ A
  -- qᴹ {S.𝔹}     t = t
  -- qᴹ {A S.⇒ B} t = S.lam {!t S.wk !}

  -- uᴹ : ∀ {A Γ} → S.Tm Γ A → Tyᴹ (Ty⁺ A) Γ
  -- uᴹ {S.𝔹}     t = {!!}
  -- uᴹ {A S.⇒ B} t = {!!}








-- Tr : T.Ty → Set
-- Tr T.𝔹 = {!!}
-- Tr T.Top = {!!}
-- Tr (A T.* A₁) = {!!}
-- Tr (A T.⇒⁺ A₁) = {!!}
-- Tr (A T.⇒ A₁) = {!!}




-- back∈ : ∀ {A A⁺ Γ Γ⁺} → A⁺ T.∈ Γ⁺ → A⁺ ≡ Ty⁺ A → Γ⁺ ≡ Con⁺ Γ → A S.∈ Γ
-- back∈ {Γ = S.∙} T.vz refl ()
-- back∈ {Γ = Γ S.▶ A} T.vz p refl rewrite Ty⁺-inj p = S.vz
-- back∈ {Γ = S.∙} (T.vs x) p ()
-- back∈ {Γ = Γ S.▶ x₁} (T.vs x) refl refl = S.vs (back∈ x refl refl)

-- lem : ∀ {A⁺ Γ} → T.Ne (Con⁺ Γ) A⁺ → ∃ λ A → Ty⁺ A ≡ A⁺
-- lem (T.var x) = {!!}
-- lem (T.app t u) = {!!}
-- lem (T.app⁺ t u) = {!!}
-- lem (T.if t u v) = {!!}
-- lem (T.π₁ t) with lem t
-- ... | (A , p) = {!p!}
-- lem (T.π₂ t) = {!!}

-- postulate
--   ⌜_⌝Nf : ∀ {Γ A} → T.Nf Γ A → T.Tm Γ A
--   ⌜_⌝Ne : ∀ {Γ A} → T.Ne Γ A → T.Tm Γ A
--   -- lem' : ∀ {A⁺ Γ} → T.Nf (Con⁺ Γ) A⁺ → ∃ λ A → Ty⁺ A ≡ A⁺

-- mutual
--   backNf : ∀ {A Γ} → T.Nf (Con⁺ Γ) (Ty⁺ A) → S.Tm Γ A
--   backNf {S.𝔹}     (T.ne t) = backNe t
--   backNf {S.𝔹}     T.true   = S.true
--   backNf {S.𝔹}     T.false  = S.false
--   backNf {A S.⇒ B} (T.ne x) = backNe x
--   backNf {A S.⇒ B} (T.pack env t) = {!!} --

--   -- with lem' t
--   -- backNf {A S.⇒ B} (T.pack env t) | S.𝔹 , ()
--   -- backNf {A S.⇒ B} (T.pack env t) | (EA S.⇒ B') , ()

--   backNe : ∀ {A Γ} → T.Ne (Con⁺ Γ) (Ty⁺ A) → S.Tm Γ A
--   backNe (T.var x)    = S.var (back∈ x refl refl)
--   backNe (T.app⁺ t x) with lem t
--   backNe (T.app⁺ t x) | S.𝔹 , ()
--   backNe (T.app⁺ t x) | (A S.⇒ B) , foo with T.⇒⁺-inj foo
--   backNe (T.app⁺ t x) | (A S.⇒ B) , foo | refl , q with Ty⁺-inj q
--   ... | refl = {!!} -- S.app (backNe t) (backNf x)
--   backNe (T.if t u v) = S.if (backNe t) (backNf u) (backNf v)

--   backNe (T.app t x)  = {!!}
--   backNe (T.π₁ t)     = {!!}
--   backNe (T.π₂ t)     = {!!}
