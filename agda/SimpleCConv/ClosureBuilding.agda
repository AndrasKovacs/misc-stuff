{-# OPTIONS --without-K #-}

module ClosureBuilding where

open import Lib
open import Target

qCon : Con → Ty
qCon ∙       = Top
qCon (Γ ▶ A) = qCon Γ * A

head : ∀ {Γ Δ A} → Sub Γ (Δ ▶ A) → Tm Γ A
head (σ , t) = t

tail : ∀ {Γ Δ A} → Sub Γ (Δ ▶ A) → Sub Γ Δ
tail (σ , _) = σ

subη : ∀ {Γ Δ A}(t : Sub Γ (Δ ▶ A)) → (tail t , head t) ≡ t
subη (σ , t) = refl

open' : ∀ {Γ} → Sub Γ (∙ ▶ qCon Γ)
open' {∙}     = ∙ , tt
open' {Γ ▶ A} = ∙ , Tmₑ wk (head (open' {Γ})) , var vz

close : ∀ {Γ} → Sub (∙ ▶ qCon Γ) Γ
close {∙}     = ∙
close {Γ ▶ A} = close {Γ} ∘ₛ (∙ , π₁ (var vz)) , π₂ (var vz)

open-close : ∀ {Γ} → (open' {Γ} ∘ₛ close) ~ₛ idₛ
open-close {∙}     = ∙ , (ttη ~⁻¹)
open-close {Γ ▶ A} with open' {Γ} | open-close{Γ}
... | ∙ , ct | ∙ , hyp =
  ∙ ,
  (((≡~ (Tm-ₑ∘ₛ (wk{A}) ((close ∘ₛ (∙ , π₁ (var vz))) , π₂ (var vz)) ct ⁻¹)
    ~◾ ≡~ ((λ x → Tmₛ x ct) & (idlₑₛ (close ∘ₛ (∙ , π₁ (var vz)))))
    ~◾ ≡~ (Tm-∘ₛ close (∙ , π₁ (var vz)) ct) ~◾ Tmₛσ~ (∙ , π₁ (var vz)) hyp) , ~refl)
    ~◾ ,η (var vz))

close-open : ∀ {Γ} → (close ∘ₛ open' {Γ}) ~ₛ idₛ
close-open {∙}     = ∙
close-open {Γ ▶ A} with open' {Γ} | close-open {Γ}
... | ∙ , ct | hyp
  rewrite assₛ close (∙ , π₁ {_}{qCon Γ}{A} (var vz)) (∙ , (Tmₑ wk ct , var vz))
     =   ((~∘ₛ~ (~ₛrefl (close {Γ})) (∙ , π₁β _ (var vz))
        ~ₛ◾ ≡~ₛ (assₛₛₑ close (∙ , ct) (wk{A}) ⁻¹))
        ~ₛ◾ ~ₛ∘ₑ hyp (wk{A}))
     , π₂β (Tmₑ wk ct) (var vz)

lam⁺ : ∀ {Γ A B} → Tm (Γ ▶ A) B → Tm Γ (A ⇒⁺ B)
lam⁺ {Γ} {A} {B} t = pack (head open') (lam (Tmₛ (close {Γ ▶ A}) t))
