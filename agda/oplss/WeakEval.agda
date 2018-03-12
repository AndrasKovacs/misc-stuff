{-# OPTIONS --without-K #-}

open import Lib
open import STLC

data _~>_ {Γ} : ∀ {A} → Tm Γ A → Tm Γ A → Set where
  β    : ∀ {A B}(t : Tm (Γ , A) B) t' → app (lam t) t' ~> Tmₛ (idₛ , t') t
  app₁ : ∀ {A B}{f}{f' : Tm Γ (A ⇒ B)}{a} → f ~> f' → app f a ~> app f' a
infix 3 _~>_

data _~>*_ {Γ A} : Tm Γ A → Tm Γ A → Set where
  []    : ∀ {t} → t ~>* t
  _∷_   : ∀ {t t' t''} → t ~> t' → t' ~>* t'' → t ~>* t''
infixr 4 _∷_
infix 3 _~>*_

trans~>* : ∀ {Γ A}{t t' t'' : Tm Γ A} → t ~>* t' → t' ~>* t'' → t ~>* t''
trans~>* []       qs = qs
trans~>* (p ∷ ps) qs = p ∷ trans~>* ps qs

Good : ∀ {A} → Tm ∙ A → Set
Good {ι}     t = ⊥
Good {A ⇒ B} t =
  Σ _ λ t' → (t ~>* lam t') × (((a : Tm ∙ A) → Good a → Good (Tmₛ (idₛ , a) t')))

data Goodˢ : ∀ {Γ} → Sub ∙ Γ → Set where
  ∙   : Goodˢ ∙
  _,_ : ∀ {Γ A}{t : Tm ∙ A}{σ : Sub ∙ Γ} → Goodˢ σ → Good t → Goodˢ (σ , t)

Good~>⁻¹ : ∀ {A}{t t' : Tm ∙ A} → t ~> t' → Good t' → Good t
Good~>⁻¹ {ι}     t~>t' pt' = pt'
Good~>⁻¹ {A ⇒ B} t~>t' (t'' , p , q) = t'' , (t~>t' ∷ p) , q

Good~>*⁻¹ : ∀ {A}{t t' : Tm ∙ A} → t ~>* t' → Good t' → Good t
Good~>*⁻¹ []           pt' = pt'
Good~>*⁻¹ (p ∷ t~>*t') pt' = Good~>⁻¹ p (Good~>*⁻¹ t~>*t' pt')

app₁* : ∀ {A B}{t t' : Tm ∙ (A ⇒ B)}{u} → t ~>* t' → app t u ~>* app t' u
app₁* []           = []
app₁* (p ∷ t~>*t') = app₁ p ∷ app₁* t~>*t'

eval : ∀ {Γ A}(t : Tm Γ A){σ : Sub ∙ Γ} → Goodˢ σ → Good (Tmₛ σ t)
eval (var vz)     (σᴹ , pt) = pt
eval (var (vs x)) (σᴹ , _ ) = eval (var x) σᴹ
eval (lam t) {σ} σᴳ =
  Tmₛ (keepₛ σ) t , [] ,
  (λ a aᴳ →
    coe
      (Good &
        ((λ x → Tmₛ x t) & ((_, a) &
          (idrₛ σ ⁻¹ ◾ assₛₑₛ σ (drop ∙) (∙ , a) ⁻¹)) ◾ Tm-∘ₛ (keepₛ σ) (∙ , a) t))
    (eval t {σ , a} (σᴳ , aᴳ)))
eval (app t u) {σ} σᴳ with eval t σᴳ
... | t' , p , q =
o  Good~>*⁻¹ (trans~>* (app₁* p) (β t' (Tmₛ σ u) ∷ [])) (q (Tmₛ σ u) (eval u σᴳ) )

Val : ∀ {A} → Tm ∙ A → Set
Val (var _)   = ⊥
Val (lam _)   = ⊤
Val (app _ _) = ⊥

Reducible : ∀ {A} → Tm ∙ A → Set
Reducible t = Σ _ λ t' → Val t' → t ~>* t'

Quote : ∀ {A}{t : Tm ∙ A} → Good t → Reducible t
Quote {ι} ()
Quote {A ⇒ B}{t} (t' , p , q) = lam t' , (λ _ → p)

whnf : ∀ {A}(t : Tm ∙ A) → Reducible t
whnf t = coe (Reducible & Tm-idₛ t) (Quote (eval t ∙))
