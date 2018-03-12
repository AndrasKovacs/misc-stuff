{-# OPTIONS --without-K #-}

module ClosureBuilding where

open import Lib
open import Target

qCon : Con → Ty
qCon ∙       = Top
qCon (Γ ▶ A) = qCon Γ * A

open' : ∀ Γ → Sub Γ (∙ ▶ qCon Γ)
open' ∙       = ∙ , tt
open' (Γ ▶ A) = ∙ , (Tmₑ wk (head (open' Γ)) , var vz)

close : ∀ Γ → Sub (∙ ▶ qCon Γ) Γ
close ∙       = ∙
close (Γ ▶ A) = close Γ ∘ₛ (∙ , π₁ (var vz)) , π₂ (var vz)

open-close : ∀ {Γ} → (open' Γ ∘ₛ close _) ~ₛ idₛ
open-close {∙}     = ∙ , (ttη ~⁻¹)
open-close {Γ ▶ A} with open' Γ | open-close{Γ}
... | ∙ , ct | ∙ , hyp =
  ∙ ,
  (((≡~ (Tm-ₑ∘ₛ (wk{A}) ((close _ ∘ₛ (∙ , π₁ (var vz))) , π₂ (var vz)) ct ⁻¹)
    ~◾ ≡~ ((λ x → Tmₛ x ct) & (idlₑₛ (close _ ∘ₛ (∙ , π₁ (var vz)))))
    ~◾ ≡~ (Tm-∘ₛ (close _) (∙ , π₁ (var vz)) ct) ~◾ Tmₛσ~ (∙ , π₁ (var vz)) hyp) , ~refl)
    ~◾ ,η (var vz))

close-open : ∀ {Γ} → (close Γ ∘ₛ open' Γ) ~ₛ idₛ
close-open {∙}     = ∙
close-open {Γ ▶ A} with open' Γ | close-open {Γ}
... | ∙ , ct | hyp
  rewrite assₛ (close _) (∙ , π₁ {_}{qCon Γ}{A} (var vz)) (∙ , (Tmₑ wk ct , var vz))
     =   ((~∘ₛ~ (~ₛrefl (close Γ)) (∙ , π₁β _ (var vz))
        ~ₛ◾ ≡~ₛ (assₛₛₑ (close _) (∙ , ct) (wk{A}) ⁻¹))
        ~ₛ◾ ~ₛ∘ₑ hyp (wk{A}))
     , π₂β (Tmₑ wk ct) (var vz)

lam⁺ : ∀ {Γ A B} → Tm (Γ ▶ A) B → Tm Γ (A ⇒⁺ B)
lam⁺ {Γ} {A} {B} t = pack (head (open' Γ)) (lam (Tmₛ (close (Γ ▶ A)) t))

-- Tmₑ-lam⁺ : ∀ {Γ Δ A B}(σ : OPE Γ Δ)(t : Tm (Δ ▶ A) B) → Tmₑ σ (lam⁺ t) ~ lam⁺ (Tmₑ (keep σ) t)
-- Tmₑ-lam⁺ σ t = {!!}

Tmₛ-lam⁺ : ∀ {Γ Δ A B}(σ : Sub Γ Δ)(t : Tm (Δ ▶ A) B) → Tmₛ σ (lam⁺ t) ~ lam⁺ (Tmₛ (keepₛ σ) t)
Tmₛ-lam⁺ {Γ}{Δ}{A}{B} σ t with open' Γ | open' Δ | close-open{Γ} | close-open{Δ}
... | ∙ , hopenΓ | ∙ , hopenΔ | co | oc
  rewrite Tm-∘ₛ ((σ ₛ∘ₑ (wk{A})) , var vz)
                ((close _ ∘ₛ (∙ , π₁ (var (vz {_}{∙})))) , π₂ (var vz)) t ⁻¹
        | assₛₑₛ σ (wk{A}) ((close _ ∘ₛ (∙ , π₁ (var (vz{_}{∙})))) , π₂ (var vz))
        | idlₑₛ (close _ ∘ₛ (∙ , π₁ {_} {qCon Γ} {A} (var (vz {_}{∙}))))
  =
  η⁺ (  β⁺ _ _ _
     ~◾ β _ _
     ~◾ (≡~ (Tm-∘ₛ _ _ t ⁻¹)
     ~◾         Tmₛ~t ((≡~ₛ (assₛ _ _ _)
            ~ₛ◾ ~∘ₛ~ (~ₛrefl _) (∙ , π₁β _ _)
            ~ₛ◾ ≡~ₛ ((λ x → close _ ∘ₛ (∙ , x)) & Tm-ₛ∘ₑ σ (wk{A}) hopenΔ ⁻¹)
            ~ₛ◾ ≡~ₛ (assₛ (close Δ) (∙ , hopenΔ) (σ ₛ∘ₑ wk) ⁻¹)
            ~ₛ◾ ≡~ₛ (assₛₛₑ _ _ _ ⁻¹)
            ~ₛ◾ ~ₛ∘ₑ
                  (    ~∘ₛ~ oc (~ₛrefl σ)
                   ~ₛ◾ ≡~ₛ (idlₛ σ)
                   ~ₛ◾ ≡~ₛ (idrₛ σ ⁻¹)
                   ~ₛ◾ ~∘ₛ~ (~ₛrefl _) (co ~ₛ⁻¹))
                  wk
            ~ₛ◾ ≡~ₛ (assₛₛₑ σ _ wk)
            ~ₛ◾ ≡~ₛ ((σ ∘ₛ_) & assₛₛₑ (close Γ) (∙ , hopenΓ) (wk{A}))
            ~ₛ◾ ~∘ₛ~ (~ₛrefl _) (~∘ₛ~ (~ₛrefl _) (∙ , π₁β _ _ ~⁻¹))
            ~ₛ◾ ≡~ₛ ((σ ∘ₛ_) & assₛ _ _ _ ⁻¹)
            ~ₛ◾ ≡~ₛ (assₛ _ _ _ ⁻¹))
        , (π₂β _ _ ~◾ π₂β _ _ ~⁻¹)) t
     ~◾ ≡~ (Tm-∘ₛ _ _ t))
     ~◾ β _ _ ~⁻¹
     ~◾ β⁺ _ _ _ ~⁻¹)
