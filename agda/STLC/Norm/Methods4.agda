{-# OPTIONS --no-eta --rewriting --without-K #-}

module STLC.Norm.Methods4 where

open import STLC.lib

open import STLC.Renaming
open import STLC.Nf
open import STLC.Syntax
open import STLC.Derived
open import STLC.Norm.Methods1
open import STLC.Norm.CoeLemmas

private
  postulate cheat : ∀ {α}{A : Set α} → A

abstract
  lamᴹ-coe :
    ∀ {Γ Δ A B}{t : Tm (Γ , A) B}{σ : Tms Δ Γ}{a : Tm Δ A}
    → t [ σ ,ₛ a ] ≡ lam t [ σ ] $ a
  lamᴹ-coe {t = t}{σ}{a} = (
      ap (_$ a) lam[]
    ◾ ap (_[ id ,ₛ a ]) ⇒β
    ◾ [][]
    ◾ ap (t [_]) (
      ,∘ ◾ ,ₛ≡ (ass ◾ ap (σ ∘_) (π₁id∘ ◾ ,β₁) ◾ idr) π₂idβ)
    ) ⁻¹

  appᴹ-coe :
    ∀ {Γ Δ A B}{σ : Tms Δ (Γ , A)}{t : Tm Γ (A ⇒ B)}
    → t [ π₁ σ ] $ π₂ σ ≡ app t [ σ ]
  appᴹ-coe {σ = σ}{t} =
      ap (_[ id ,ₛ π₂ σ ]) app[]
    ◾ [][]
    ◾ ap (app t [_]) (
        ,∘ ◾ ,ₛ≡ (ass ◾ (ap (π₁ σ ∘_) (π₁id∘ ◾ ,β₁) ◾ idr)) π₂idβ ◾ ,η)

stab-Con : ∀ {Γ}{Γᴹ : Conᴹ Γ}{Σ Δ}{σ : Tms Δ Γ} → (r : Δ ⊆ Σ) → Γᴹ σ → Γᴹ (σ ∘ sub r)
stab-Con {∙}     {Γᴹ} {Σ} {Δ} {σ} r σᴹ = {!!}
stab-Con {Γ , x} {Γᴹ} {Σ} {Δ} {σ} r σᴹ = {!!}

lamᴹ :
  ∀ {Γ} {Γᴹ : Conᴹ Γ} {A} {Aᴹ : Tyᴹ A} {B} {Bᴹ : Tyᴹ B} {t : Tm (Γ , A) B}
  → Tmᴹ (Γᴹ ,ᴹ Aᴹ) Bᴹ t → Tmᴹ Γᴹ (Aᴹ ⇒ᴹ Bᴹ) (lam t)
lamᴹ {Γ}{Γᴹ}{A}{Aᴹ}{B}{Bᴹ} {t} tᴹ Δ σ σᴹ Σ r a aᴹ =
  coe {!!} (tᴹ Σ (σ ∘ sub r ,ₛ a) ({!σᴹ!} , coe (ap Aᴹ (,β₂ ⁻¹)) aᴹ)) -- stability
--  coe (ap Bᴹ lamᴹ-coe) (tᴹ Δ (σ ,ₛ a) (coe (ap Γᴹ (,β₁ ⁻¹)) σᴹ , coe (ap Aᴹ (,β₂ ⁻¹)) aᴹ))

appᴹ :
  ∀ {Γ} {Γᴹ : Conᴹ Γ} {A} {Aᴹ : Tyᴹ A} {B}{Bᴹ : Tyᴹ B}
    {t : Tm Γ (A ⇒ B)}
  → Tmᴹ Γᴹ (Aᴹ ⇒ᴹ Bᴹ) t → Tmᴹ (Γᴹ ,ᴹ Aᴹ) Bᴹ (app t)
appᴹ {Γ}{Γᴹ}{A}{Aᴹ}{B}{Bᴹ}{t} tᴹ Δ σ (π₁σᴹ , π₂σᴹ) =
  coe (ap Bᴹ appᴹ-coe) (tᴹ Δ (π₁ σ) π₁σᴹ _ idᵣ (π₂ σ) π₂σᴹ)

-- lam[]ᴹ :
--   ∀ {Γ} {Γᴹ : Conᴹ Γ} {Δ} {Δᴹ : Conᴹ Δ} {δ : Tms Γ Δ}
--     {δᴹ : Tmsᴹ Γᴹ Δᴹ δ} {A} {Aᴹ : Tyᴹ A} {B} {Bᴹ : Tyᴹ B}
--     {t : Tm (Δ , A) B} {tᴹ : Tmᴹ (Δᴹ ,ᴹ Aᴹ) Bᴹ t}

--   --           lamᴹ tᴹ [ δᴹ ]ᴹ
--   --    ≡[ ap (Tmᴹ Γᴹ (Aᴹ ⇒ᴹ Bᴹ)) lam[] ]≡
--   -- lamᴹ (tᴹ [ δᴹ ∘ᴹ π₁ᴹ idᴹ ,ₛᴹ π₂ᴹ idᴹ ]ᴹ)

--   →  _[_]ᴹ {Aᴹ = Aᴹ ⇒ᴹ Bᴹ} (lamᴹ {Γᴹ = Δᴹ}{Bᴹ = Bᴹ} tᴹ) δᴹ
--           ≡[ ap (Tmᴹ Γᴹ (Aᴹ ⇒ᴹ Bᴹ)) lam[] ]≡
--      lamᴹ {Bᴹ = Bᴹ} (_[_]ᴹ {Aᴹ = Bᴹ} tᴹ
--        (_,ₛᴹ_ {Δᴹ = Δᴹ} (_∘ᴹ_ {Σᴹ = Δᴹ} δᴹ (π₁ᴹ{Δᴹ = Γᴹ}{Aᴹ = Aᴹ} idᴹ))
--          {Aᴹ = Aᴹ} (π₂ᴹ {Δᴹ = Γᴹ}{Aᴹ = Aᴹ} idᴹ)))

-- lam[]ᴹ {Γ}{Γᴹ}{Δ}{Δᴹ}{δ}{δᴹ}{A}{Aᴹ}{B}{Bᴹ}{t}{tᴹ} =
--   Tmᴹ-≡-intro {Γ}{Γᴹ}{A ⇒ B}{Aᴹ ⇒ᴹ Bᴹ} lam[] λ Σ σ σᴹ
--   → funext λ a → funext λ aᴹ
--   → ap (λ x → x aᴹ) (coe-apply
--       (λ a t → Aᴹ a → Bᴹ (t [ σ ] $ a))
--       lam[] ((_[_]ᴹ {Aᴹ = Aᴹ ⇒ᴹ Bᴹ} (lamᴹ {Γᴹ = Δᴹ}{Bᴹ = Bᴹ} tᴹ)) δᴹ Σ σ σᴹ) a)
--   ◾ coe-apply (λ aᴹ t → Bᴹ (t [ σ ] $ a)) lam[]
--     ((_[_]ᴹ {Aᴹ = Aᴹ ⇒ᴹ Bᴹ} (lamᴹ {Γᴹ = Δᴹ}{Bᴹ = Bᴹ} tᴹ)) δᴹ Σ σ σᴹ a) aᴹ
--   ◾ ap (λ x → coe (ap (λ t₁ → Bᴹ (app (t₁ [ σ ]) [ id ,ₛ a ])) lam[]) (x aᴹ))
--        (coe-apply
--          (λ a t → Aᴹ a → Bᴹ (app t [ id ,ₛ a ]))
--          ([][] ⁻¹)
--          (λ a aᴹ →
--             coe (ap Bᴹ lamᴹ-coe)
--             (tᴹ Σ (δ ∘ σ ,ₛ a)
--              (coe (ap Δᴹ (,β₁ ⁻¹)) (δᴹ Σ σ σᴹ) ,
--               coe (ap (λ z → Aᴹ z) (,β₂ ⁻¹)) aᴹ)))
--          a)
--   ◾ ap (coe (ap (λ t → Bᴹ (app (t [ σ ]) [ id ,ₛ a ])) lam[]))
--        (coe-apply
--          (λ aᴹ t → Bᴹ (app t [ id ,ₛ a ]))
--          ([][] ⁻¹)
--          (λ aᴹ →
--             coe (ap Bᴹ lamᴹ-coe)
--             (tᴹ Σ (δ ∘ σ ,ₛ a)
--              (coe (ap Δᴹ (,β₁ ⁻¹)) (δᴹ Σ σ σᴹ) ,
--               coe (ap (λ z → Aᴹ z) (,β₂ ⁻¹)) aᴹ)))
--          aᴹ)
--   ◾ ap-◾ (ap (λ t₁ → Bᴹ (app (t₁ [ σ ]) [ id ,ₛ a ])) lam[])
--          (ap (λ t₁ → Bᴹ (app t₁ [ id ,ₛ a ])) ([][] ⁻¹))
--   ◾ ap-◾ (ap (λ t₁ → Bᴹ (app t₁ [ id ,ₛ a ])) ([][] ⁻¹) ◾
--             ap (λ t₁ → Bᴹ (app (t₁ [ σ ]) [ id ,ₛ a ])) lam[])
--           (ap Bᴹ lamᴹ-coe)
--   ◾ ap (λ x →
--          coe
--           (ap Bᴹ lamᴹ-coe ◾
--            (ap (λ t₁ → Bᴹ (app t₁ [ id ,ₛ a ])) ([][] ⁻¹) ◾
--             ap (λ t₁ → Bᴹ (app (t₁ [ σ ]) [ id ,ₛ a ])) lam[]))
--           (tᴹ Σ (δ ∘ σ ,ₛ a) x))
--      (coe-× (ap Δᴹ (,β₁ ⁻¹)) (ap Aᴹ (,β₂ ⁻¹)))
--   ◾ cheat 

