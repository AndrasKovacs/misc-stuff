{-# OPTIONS --without-K #-}

module StdModel (Uᴹ : Set)(Elᴹ : Uᴹ → Set) where

open import Lib
open import Syntax
open import Embedding
open import Substitution
open import Conversion
open import Typing
open import Sanity
open import SyntaxSet
open import PropTrunc
open import UIP

Conᴹ :
  ∀ {n}{Γ : Con n} → Γ ⊢ → Set

Tyᴹ :
  ∀ {n Γ} Γw {A} → Γ ⊢ A → Conᴹ {n}{Γ} Γw → Set

OPEᴹ :
  ∀ {n Γ} Γw {m Δ} Δw → ∀ {σ} → OPE⊢ Γ Δ σ → Conᴹ {n}{Γ} Γw → Conᴹ {m}{Δ} Δw

Tyₑᴹ :
  ∀ {n Γ} Γw {m Δ} Δw {A} Aw {σ}
  → (σw : OPE⊢ {n}{m} Γ Δ σ)
  → ∀ γ → Tyᴹ {n}{Γ} Γw {Tyₑ σ A}(Γ⊢Aₑ σw Aw) γ ≡ Tyᴹ {m}{Δ} Δw Aw (OPEᴹ Γw Δw σw γ)

Subᴹ :
  ∀ {n Γ} Γw {m Δ} Δw → ∀ {σ} → Sub⊢ Γ Δ σ → Conᴹ {n}{Γ} Γw → Conᴹ {m}{Δ} Δw

Tyₛᴹ :
  ∀ {n Γ} Γw {m Δ} Δw {A} Aw {σ}
  → (σw : Sub⊢ {n} Γ {m} Δ σ)
  → ∀ γ → Tyᴹ {n}{Γ} Γw {Tyₛ σ A}(Γ⊢Aₛ σw Aw) γ ≡ Tyᴹ {m}{Δ} Δw Aw (Subᴹ Γw Δw σw γ)

Tm⇑ᴹ :
  ∀ {n Γ} Γw {A} Aw {t}(tw : Γ ⊢ t ⇑ A)(γ : Conᴹ {n}{Γ} Γw) → Tyᴹ Γw {A} Aw γ

Tm⇓ᴹ :
  ∀ {n Γ} Γw {A} Aw {t}(tw : Γ ⊢ t ⇓ A)(γ : Conᴹ {n}{Γ} Γw) → Tyᴹ Γw {A} Aw γ

Tm⇑ₑᴹ :
  ∀ {n Γ} Γw {m Δ} Δw {A} Aw {σ}
  (σw : OPE⊢ {n}{m} Γ Δ σ) {t} (tw : Δ ⊢ t ⇑ A)
  → ∀ γ
  → coe (Tyₑᴹ Γw Δw Aw σw γ)
    (Tm⇑ᴹ {n}{Γ} Γw (Γ⊢Aₑ σw Aw) (Γ⊢t⇑Aₑ σw tw) γ) ≡
     Tm⇑ᴹ {m}{Δ} Δw Aw tw (OPEᴹ Γw Δw σw γ)

~ₜᴹ : ∀ {n Γ} Γw {A} Aw {B} Bw → A ~ₜ B → Tyᴹ {n}{Γ} Γw {A} Aw ≡ Tyᴹ Γw {B} Bw

~⇑ᴹ :
  ∀ {n Γ} Γw {A} Aw {t} tw {t'} tw'
  → t ~ t' → Tm⇑ᴹ {n}{Γ} Γw {A} Aw {t} tw ≡ Tm⇑ᴹ Γw Aw {t'} tw'
~⇑ᴹ Γw Aw (app (lam x₁ tw) x) tw' (β A t u) =
  ext λ γ → {!!}
~⇑ᴹ Γw Aw tw tw' (η A t) = {!tw'!}
~⇑ᴹ Γw Aw tw tw' (app t~t' t~t'') = {!!}
~⇑ᴹ Γw Aw tw tw' (lam x t~t') = {!!}
~⇑ᴹ Γw Aw tw tw' ~refl = Tm⇑ᴹ Γw Aw & Γ⊢t⇑Aprop tw tw'
~⇑ᴹ Γw Aw tw tw' (t~t' ~⁻¹) = ~⇑ᴹ Γw Aw tw' tw t~t' ⁻¹
~⇑ᴹ Γw Aw tw tw' (t~t' ~◾ t~t'') = {!!} -- bleh

~ₜᴹ Γw (El tw) (El tw') (El t) = {!!}
~ₜᴹ Γw (Π Aw Bw) (Π Aw' Bw') (Π A B) = {!!}
~ₜᴹ Γw Aw Bw ~ₜrefl = Tyᴹ Γw & Γ⊢Aprop Aw Bw
~ₜᴹ Γw Aw Bw (B~A ~ₜ⁻¹) = ~ₜᴹ Γw Bw Aw B~A ⁻¹
~ₜᴹ Γw Aw Cw (A~B ~ₜ◾ B~C) = {!!} -- this is bad (conversion must be typed...)

Conᴹ ∙         = ⊤
Conᴹ (Γw ▷ Aw) = Σ (Conᴹ Γw) (Tyᴹ Γw Aw)

Tyᴹ Γw U         γ = Uᴹ
Tyᴹ Γw (El tw)   γ = Elᴹ (Tm⇓ᴹ Γw U tw γ)
Tyᴹ Γw (Π Aw Bw) γ = (α : Tyᴹ Γw Aw γ) → Tyᴹ (Γw ▷ Aw) Bw (γ , α)

OPEᴹ Γw        ∙         ∙         γ       = tt
OPEᴹ (Γw ▷ Aw) Δw        (drop σw) (γ , t) = OPEᴹ Γw Δw σw γ
OPEᴹ (_▷_ {Γ = Γ} Γw Aw) (_▷_ {Γ = Δ} {A} Δw Aw') (keep {σ = σ} σw) (γ , t)
  = (OPEᴹ Γw Δw σw γ) ,
    coe ((λ x → Tyᴹ Γw x γ) & Γ⊢Aprop Aw (Γ⊢Aₑ σw Aw')
  ◾ Tyₑᴹ Γw Δw Aw' σw γ) t

OPEᴹ-idₑ : ∀ {n Γ} Γw γ → OPEᴹ {n}{Γ} Γw Γw idₑ⊢ γ ≡ γ
OPEᴹ-idₑ ∙         γ = refl
OPEᴹ-idₑ (_▷_ {Γ = Γ} {A} Γw Aw) (γ , t) = {!(coe ((λ x → OPE⊢ (Γ ▷ x) (Γ ▷ A) (keep idₑ)) & Ty-idₑ A))!}

lookupᴹ : ∀ {n Γ} Γw x (Aw : Γ ⊢ lookup x Γ) → (γ : Conᴹ {n}{Γ} Γw) → Tyᴹ Γw Aw γ
lookupᴹ (Γw ▷ Aw) zero    Aw' (γ , t) =
  -- why is it not reducing ?
  coe ((Tyᴹ Γw Aw & (OPEᴹ-idₑ Γw γ ⁻¹ ◾ agda-bug ⁻¹) ◾ Tyₑᴹ (Γw ▷ Aw) Γw Aw wk⊢ (γ , t) ⁻¹) ◾ (λ x → Tyᴹ (Γw ▷ Aw) x (γ , t)) & Γ⊢Aprop Aw' (Γ⊢Aₑ wk⊢ Aw) ⁻¹) t
  where
    postulate agda-bug : OPEᴹ (Γw ▷ Aw) Γw (drop idₑ⊢) (γ , t) ≡ OPEᴹ Γw Γw idₑ⊢ γ

lookupᴹ (Γw ▷ Aw) (suc x) _   (γ , t) = {!!}

Tm⇑ₑᴹ Γw Δw Aw σw (var x)     γ = {!!}
Tm⇑ₑᴹ Γw Δw Cw σw (lam Aw tw) γ = {!!}
Tm⇑ₑᴹ Γw Δw Aw σw (app tw uw) γ = {!!}

Tm⇓ᴹ Γw Aw (A' , tw , p) γ = {!!} -- need semantic conversion

Tyₑᴹ Γw Δw U         σw γ = refl
Tyₑᴹ Γw Δw (El tw)   σw γ = Elᴹ & {!!}
Tyₑᴹ Γw Δw (Π Aw Bw) σw γ = {!!}

Tyₛᴹ Γw Δw U         σw γ = refl
Tyₛᴹ Γw Δw (El x)    σw γ = Elᴹ & {!!}
Tyₛᴹ Γw Δw (Π Aw Bw) σw γ = {!!}


Subᴹ Γw ∙         ∙        γ = tt
Subᴹ Γw (Δw ▷ Aw) (σw , t) γ =
  Subᴹ Γw Δw σw γ , coe (Tyₛᴹ Γw Δw Aw σw γ) (Tm⇓ᴹ Γw (Γ⊢Aₛ σw Aw) t γ)

Tm⇑ᴹ Γw Aw        (var x)     γ = lookupᴹ Γw x Aw γ
Tm⇑ᴹ Γw (Π Aw Bw) (lam _ tw)  γ = λ α → Tm⇑ᴹ (Γw ▷ Aw) Bw tw (γ , α)
Tm⇑ᴹ Γw Cw        (app tw uw) γ with Γ⊢t⇑? Γw tw
... | Π Aw' Bw' =
  -- Cw is substituted Bw' (need semantic Sub)
  coe {!!} (Tm⇑ᴹ Γw (Π Aw' Bw') tw γ (Tm⇓ᴹ Γw Aw' uw γ))
