
open import STLC
open import Lib

data _~>_ {Γ} : ∀ {A} → Tm Γ A → Tm Γ A → Set where
  β    : ∀ {A B}(t : Tm (Γ , A) B) t'  → app (lam t) t' ~> Tmₛ (idₛ , t') t
  lam  : ∀ {A B}{t t' : Tm (Γ , A) B}     → t ~> t' →  lam t   ~> lam t'
  app₁ : ∀ {A B}{f}{f' : Tm Γ (A ⇒ B)}{a} → f ~> f' →  app f a ~> app f' a
  app₂ : ∀ {A B}{f : Tm Γ (A ⇒ B)} {a a'} → a ~> a' →  app f a ~> app f  a'
infix 3 _~>_

data _~>*_ {Γ A} : Tm Γ A → Tm Γ A → Set where
  []  : ∀ {t} → t ~>* t
  _∷_ : ∀ {t t' t''} → t ~> t' → t' ~>* t'' → t ~>* t''
infixr 5 _∷_  






