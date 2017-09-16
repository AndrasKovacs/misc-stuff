{-# OPTIONS --without-K #-}

module Conversion where

open import Lib
open import Syntax
open import Embedding
open import Substitution

mutual
  norm : ∀ {n} → Tm n → Set
  norm (var _)           = ⊤
  norm (lam A t)         = normₜ A × norm t
  norm (app (var _)   u) = norm u
  norm (app (lam _ t) u) = ⊥
  norm (app (app t u) v) = norm t × norm u × norm v

  normₜ : ∀ {n} → Ty n → Set
  normₜ U       = ⊤
  normₜ (El t)  = norm t
  normₜ (Π A B) = normₜ A × normₜ B

mutual
  normₑ : ∀ {n m}(σ : OPE n m)(t : Tm m) → norm t → norm (Tmₑ σ t)
  normₑ σ (var x)   p = tt
  normₑ σ (lam A t) (p , q) = normₜₑ σ A p , normₑ (keep σ) t q
  normₑ σ (app (var x) u) p = normₑ σ u p
  normₑ σ (app (lam x t) u) ()
  normₑ σ (app (app t u) v) (p , q , r) = normₑ σ t p , normₑ σ u q , normₑ σ v r

  normₜₑ : ∀ {n m}(σ : OPE n m)(A : Ty m) → normₜ A → normₜ (Tyₑ σ A)
  normₜₑ σ U        p      = p
  normₜₑ σ (El t)   p      = normₑ σ t p
  normₜₑ σ (Π A B) (p , q) = normₜₑ σ A p , normₜₑ (keep σ) B q

-- call-by-name β-normalization
mutual
  data _~>_ {n : ℕ} : Tm n → Tm n → Set where
    β    : ∀ A t u → app (lam A t) u ~> Tmₛ (idₛ , u) t
    app  : ∀ {t t' u} → t ~> t' → app t u ~> app t' u
    lam₁ : ∀ {A A' t} → A ~>ₜ A' → lam A t ~> lam A' t
    lam₂ : ∀ {A t t'} → normₜ A → t ~> t' → lam A t ~> lam A t'

  data _~>ₜ_ {n : ℕ} : Ty n → Ty n → Set where
    El : ∀ {t t'} → t ~> t' → El t ~>ₜ El t'
    Π₁ : ∀ {A A' B} → A ~>ₜ A' → Π A B ~>ₜ Π A' B
    Π₂ : ∀ {A B B'} → normₜ A → B ~>ₜ B' → Π A B ~>ₜ Π A B'

data Star {A : Set}(R : A → A → Set) : A → A → Set where
  refl  : ∀ {t} → Star R t t
  trans : ∀ {t t' t''} → R t t' → Star R t' t'' → Star R t t''

_~>*_  = λ {n} → Star (_~>_ {n})
_~>ₜ*_ = λ {n} → Star (_~>ₜ_ {n})

infix 3 _~>_ _~>ₜ_ _~>*_ _~>ₜ*_ _~ₜ_
infixr 5 _++_

_++_ : ∀ {A R t t' t''} → Star {A} R t t' → Star R t' t'' → Star R t t''
refl      ++ q = q
trans x p ++ q = trans x (p ++ q)

_~_ : ∀ {n} → Tm n → Tm n → Set
t ~ t' = ∃ λ n → norm n × (t ~>* n) × (t' ~>* n)

_~ₜ_ : ∀ {n} → Ty n → Ty n → Set
t ~ₜ t' = ∃ λ n → normₜ n × (t ~>ₜ* n) × (t' ~>ₜ* n)

~refl : ∀ {n} (t : Tm n) → norm t → t ~ t
~refl t nt = t , nt , refl , refl

--------------------------------------------------------------------------------

mutual
  ~>ₑ : ∀ {Γ Δ}{t t' : Tm Γ}(σ : OPE Δ Γ) → t ~> t' → Tmₑ σ t ~> Tmₑ σ t'
  ~>ₑ σ (β A t u) =
    coe ((app (lam (Tyₑ σ A) (Tmₑ (keep σ) t)) (Tmₑ σ u) ~>_)
        & (Tm-ₑ∘ₛ (keep σ) (idₛ , Tmₑ σ u) t ⁻¹
        ◾ (λ x → Tmₛ (x , Tmₑ σ u) t) & (idrₑₛ σ ◾ idlₛₑ σ ⁻¹)
        ◾ Tm-ₛ∘ₑ (idₛ , u) σ t))
    (β (Tyₑ σ A) (Tmₑ (keep σ) t) (Tmₑ σ u))
  ~>ₑ σ (app t) = app (~>ₑ σ t)
  ~>ₑ σ (lam₁ A) = lam₁ (~>ₜₑ σ A)
  ~>ₑ σ (lam₂ {A} nA t) = lam₂ (normₜₑ σ A nA) (~>ₑ (keep σ) t)

  ~>ₜₑ : ∀ {Γ Δ}{A A' : Ty Γ}(σ : OPE Δ Γ) → A ~>ₜ A' → Tyₑ σ A ~>ₜ Tyₑ σ A'
  ~>ₜₑ σ (El t)   = El (~>ₑ σ t)
  ~>ₜₑ σ (Π₁ A)   = Π₁ (~>ₜₑ σ A)
  ~>ₜₑ σ (Π₂ {A} nA B) = Π₂ (normₜₑ σ A nA) (~>ₜₑ (keep σ) B)

~>*ₑ : ∀ {Γ Δ}{t t' : Tm Γ}(σ : OPE Δ Γ) → t ~>* t' → Tmₑ σ t ~>* Tmₑ σ t'
~>*ₑ σ refl        = refl
~>*ₑ σ (trans p q) = trans (~>ₑ σ p) (~>*ₑ σ q)

~>ₜ*ₑ : ∀ {Γ Δ}{A A' : Ty Γ}(σ : OPE Δ Γ) → A ~>ₜ* A' → Tyₑ σ A ~>ₜ* Tyₑ σ A'
~>ₜ*ₑ σ refl        = refl
~>ₜ*ₑ σ (trans p q) = trans (~>ₜₑ σ p ) (~>ₜ*ₑ σ q)

~ₜₑ : ∀ {Γ Δ}{A A' : Ty Γ}(σ : OPE Δ Γ) → A ~ₜ A' → Tyₑ σ A ~ₜ Tyₑ σ A'
~ₜₑ σ (B , nB , p , q) = Tyₑ σ B , normₜₑ σ B nB , ~>ₜ*ₑ σ p , ~>ₜ*ₑ σ q

--------------------------------------------------------------------------------

-- ~>ₛ : ∀ {Γ Δ A}{t t' : Tm Γ A}(σ : Sub Δ Γ) → t ~> t' → Tmₛ σ t ~> Tmₛ σ t'
-- ~>ₛ σ (β t t') =
--   coe ((app (lam (Tmₛ (keepₛ σ) t)) (Tmₛ σ t') ~>_) &
--       (Tm-∘ₛ (keepₛ σ) (idₛ , Tmₛ σ t') t ⁻¹
--     ◾ (λ x → Tmₛ (x , Tmₛ σ t') t) &
--         (assₛₑₛ σ wk (idₛ , Tmₛ σ t')
--       ◾ ((σ ∘ₛ_) & idlₑₛ idₛ ◾ idrₛ σ) ◾ idlₛ σ ⁻¹)
--     ◾ Tm-∘ₛ (idₛ , t') σ t))
--   (β (Tmₛ (keepₛ σ) t) (Tmₛ σ t'))
-- ~>ₛ σ (lam  step) = lam  (~>ₛ (keepₛ σ) step)
-- ~>ₛ σ (app₁ step) = app₁ (~>ₛ σ step)
-- ~>ₛ σ (app₂ step) = app₂ (~>ₛ σ step)

-- ~ₛ : ∀ {Γ Δ}{t t' : Tm Γ}(σ : Sub Δ Γ) → t ~ t' → Tmₛ σ t ~ Tmₛ σ t'
-- ~ₛ σ (β t u)          =
--   coe
--     ((app (lam (Tmₛ (keepₛ σ) t)) (Tmₛ σ u) ~_) &
--         (Tm-∘ₛ (keepₛ σ) (idₛ , Tmₛ σ u) t ⁻¹
--       ◾ (λ x → Tmₛ (x , Tmₛ σ u) t) &
--            (assₛₑₛ σ wk (idₛ , Tmₛ σ u)
--          ◾ (σ ∘ₛ_) & idlₑₛ idₛ
--          ◾ idrₛ σ ◾ idlₛ σ ⁻¹)
--       ◾ Tm-∘ₛ (idₛ , u) σ t))
--     (β (Tmₛ (keepₛ σ) t) (Tmₛ σ u))
-- ~ₛ σ (η t) =
--   coe
--     ((λ x → (Tmₛ σ t ~ lam (app x (var zero)))) &
--         (Tm-ₛ∘ₑ σ wk t ⁻¹
--       ◾ (λ x → Tmₛ x t) &
--           ((_ₛ∘ₑ wk) & (idlₑₛ σ ⁻¹)
--         ◾ assₑₛₑ idₑ σ wk)
--         ◾ Tm-ₑ∘ₛ wk (keepₛ σ) t))
--     (η (Tmₛ σ t))
-- ~ₛ σ (app t~t' u~u')  = app (~ₛ σ t~t') (~ₛ σ u~u')
-- ~ₛ σ (lam t~t')       = lam (~ₛ (keepₛ σ) t~t')
-- ~ₛ σ ~refl            = ~refl
-- ~ₛ σ (t~t' ~⁻¹)       = ~ₛ σ t~t' ~⁻¹
-- ~ₛ σ (t~t' ~◾ t'~t'') = ~ₛ σ t~t' ~◾ ~ₛ σ t'~t''

-- ~ₜₛ : ∀ {Γ Δ}{A A' : Ty Γ}(σ : Sub Δ Γ) → A ~ₜ A' → Tyₛ σ A ~ₜ Tyₛ σ A'
-- ~ₜₛ σ (El t~t')         = El (~ₛ σ t~t')
-- ~ₜₛ σ (Π A~A' B~B')     = Π (~ₜₛ σ A~A') (~ₜₛ (keepₛ σ) B~B')
-- ~ₜₛ σ ~ₜrefl            = ~ₜrefl
-- ~ₜₛ σ (A~A' ~ₜ⁻¹)       = ~ₜₛ σ A~A' ~ₜ⁻¹
-- ~ₜₛ σ (A~A' ~ₜ◾ A'~A'') = ~ₜₛ σ A~A' ~ₜ◾ ~ₜₛ σ A'~A''
