{-# OPTIONS --without-K #-}

module Conversion where

open import Lib
open import Syntax
open import Embedding
open import Substitution

data _~_ {n : ℕ} : Tm n → Tm n → Set where
  β     : ∀ t u → app (lam t) u ~ Tmₛ (idₛ , u) t
  η     : ∀ t → t ~ lam (app (Tmₑ wk t) (var zero))
  app   : ∀ {t t' u u'} → t ~ t' → u ~ u' → app t u ~ app t' u'
  lam   : ∀ {t t'} → t ~ t' → lam t ~ lam t'
  ~refl : ∀ {t} → t ~ t
  _~⁻¹  : ∀ {t t'} → t ~ t' → t' ~ t
  _~◾_  : ∀ {t t' t''} → t ~ t' → t' ~ t'' → t ~ t''

infix 3 _~_
infixl 4 _~◾_
infix 6 _~⁻¹

data _~ₜ_ {n : ℕ} : Ty n → Ty n → Set where
  El     : ∀ {t t'} → t ~ t' → El t ~ₜ El t'
  Π      : ∀ {A A' B B'} → A ~ₜ A' → B ~ₜ B' → Π A B ~ₜ Π A' B'
  ~ₜrefl : ∀ {t} → t ~ₜ t
  _~ₜ⁻¹  : ∀ {t t'} → t ~ₜ t' → t' ~ₜ t
  _~ₜ◾_  : ∀ {t t' t''} → t ~ₜ t' → t' ~ₜ t'' → t ~ₜ t''

infix 3 _~ₜ_
infixl 4 _~ₜ◾_
infix 6 _~ₜ⁻¹

~ₑ : ∀ {Γ Δ}{t t' : Tm Γ}(σ : OPE Δ Γ) → t ~ t' → Tmₑ σ t ~ Tmₑ σ t'
~ₑ σ (η t) =
  coe ((λ t' → Tmₑ σ t ~ lam (app t' (var zero)))
    & (Tm-∘ₑ σ wk t ⁻¹
    ◾ (λ x → Tmₑ (drop x) t) & (idrₑ σ ◾ idlₑ σ ⁻¹)
    ◾ Tm-∘ₑ wk  (keep σ) t))
  (η (Tmₑ σ t))
~ₑ σ (β t t') =
  coe ((app (lam (Tmₑ (keep σ) t)) (Tmₑ σ t') ~_) &
    (Tm-ₑ∘ₛ (keep σ) (idₛ , Tmₑ σ t') t ⁻¹
    ◾ (λ x → Tmₛ (x , Tmₑ σ t') t) & (idrₑₛ σ ◾ idlₛₑ σ ⁻¹)
    ◾ Tm-ₛ∘ₑ (idₛ , t') σ t))
  (β (Tmₑ (keep σ) t) (Tmₑ σ t'))
~ₑ σ (lam t~t')       = lam (~ₑ (keep σ) t~t')
~ₑ σ (app t~t' x~x')  = app (~ₑ σ t~t') (~ₑ σ x~x')
~ₑ σ ~refl            = ~refl
~ₑ σ (t~t' ~⁻¹)       = ~ₑ σ t~t' ~⁻¹
~ₑ σ (t~t' ~◾ t'~t'') = ~ₑ σ t~t' ~◾ ~ₑ σ t'~t''

~ₜₑ : ∀ {Γ Δ}{A A' : Ty Γ}(σ : OPE Δ Γ) → A ~ₜ A' → Tyₑ σ A ~ₜ Tyₑ σ A'
~ₜₑ σ (El t~t')         = El (~ₑ σ t~t')
~ₜₑ σ (Π A~A' B~B')     = Π (~ₜₑ σ A~A') (~ₜₑ (keep σ) B~B')
~ₜₑ σ ~ₜrefl            = ~ₜrefl
~ₜₑ σ (A~A' ~ₜ⁻¹)       = ~ₜₑ σ A~A' ~ₜ⁻¹
~ₜₑ σ (A~A' ~ₜ◾ A'~A'') = ~ₜₑ σ A~A' ~ₜ◾ ~ₜₑ σ A'~A''

~ₛ : ∀ {Γ Δ}{t t' : Tm Γ}(σ : Sub Δ Γ) → t ~ t' → Tmₛ σ t ~ Tmₛ σ t'
~ₛ σ (β t u)          =
  coe
    ((app (lam (Tmₛ (keepₛ σ) t)) (Tmₛ σ u) ~_) &
        (Tm-∘ₛ (keepₛ σ) (idₛ , Tmₛ σ u) t ⁻¹
      ◾ (λ x → Tmₛ (x , Tmₛ σ u) t) &
           (assₛₑₛ σ wk (idₛ , Tmₛ σ u)
         ◾ (σ ∘ₛ_) & idlₑₛ idₛ
         ◾ idrₛ σ ◾ idlₛ σ ⁻¹)
      ◾ Tm-∘ₛ (idₛ , u) σ t))
    (β (Tmₛ (keepₛ σ) t) (Tmₛ σ u))
~ₛ σ (η t) =
  coe
    ((λ x → (Tmₛ σ t ~ lam (app x (var zero)))) &
        (Tm-ₛ∘ₑ σ wk t ⁻¹
      ◾ (λ x → Tmₛ x t) &
          ((_ₛ∘ₑ wk) & (idlₑₛ σ ⁻¹)
        ◾ assₑₛₑ idₑ σ wk)
        ◾ Tm-ₑ∘ₛ wk (keepₛ σ) t))
    (η (Tmₛ σ t))
~ₛ σ (app t~t' u~u')  = app (~ₛ σ t~t') (~ₛ σ u~u')
~ₛ σ (lam t~t')       = lam (~ₛ (keepₛ σ) t~t')
~ₛ σ ~refl            = ~refl
~ₛ σ (t~t' ~⁻¹)       = ~ₛ σ t~t' ~⁻¹
~ₛ σ (t~t' ~◾ t'~t'') = ~ₛ σ t~t' ~◾ ~ₛ σ t'~t''

~ₜₛ : ∀ {Γ Δ}{A A' : Ty Γ}(σ : Sub Δ Γ) → A ~ₜ A' → Tyₛ σ A ~ₜ Tyₛ σ A'
~ₜₛ σ (El t~t')         = El (~ₛ σ t~t')
~ₜₛ σ (Π A~A' B~B')     = Π (~ₜₛ σ A~A') (~ₜₛ (keepₛ σ) B~B')
~ₜₛ σ ~ₜrefl            = ~ₜrefl
~ₜₛ σ (A~A' ~ₜ⁻¹)       = ~ₜₛ σ A~A' ~ₜ⁻¹
~ₜₛ σ (A~A' ~ₜ◾ A'~A'') = ~ₜₛ σ A~A' ~ₜ◾ ~ₜₛ σ A'~A''
