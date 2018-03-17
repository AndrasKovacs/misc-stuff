
module Target.LogicalEqv where

open import Lib
open import Target.Syntax

infix 4 _≈_
_≈_ : ∀ {A} → Tm ∙ A → Tm ∙ A → Set
_≈_ {𝔹}      t u = ((t ~ true) × (u ~ true)) ⊎ ((t ~ false) × (u ~ false))
_≈_ {Top}    t u = ⊤
_≈_ {A * B}  t u = (π₁ t ≈ π₁ u) × (π₂ t ≈ π₂ u)
_≈_ {A ⇒⁺ B} t u = ∀ {a a'} → a ≈ a' → app⁺ t a ≈ app⁺ u a'
_≈_ {A ⇒ B}  t u = ∀ {a a'} → a ≈ a' → app t a ≈ app u a'

infix 6 _≈⁻¹
_≈⁻¹ : ∀ {A}{t t' : Tm ∙ A} → t ≈ t' → t' ≈ t
_≈⁻¹ {𝔹} (inl (p , q)) = inl (q , p)
_≈⁻¹ {𝔹} (inr (p , q)) = inr (q , p)
_≈⁻¹ {Top}    p       = p
_≈⁻¹ {A * B}  (p , q) = (p ≈⁻¹) , (q ≈⁻¹)
_≈⁻¹ {A ⇒ B}  p       = λ q → p (q ≈⁻¹) ≈⁻¹
_≈⁻¹ {A ⇒⁺ B} p       = λ q → p (q ≈⁻¹) ≈⁻¹

infixr 4 _≈◾_
_≈◾_ : ∀ {A}{t t' t'' : Tm ∙ A} → t ≈ t' → t' ≈ t'' → t ≈ t''
_≈◾_ {𝔹} (inl (p , q)) (inl (r , s)) = inl (p , s)
_≈◾_ {𝔹} (inl (p , q)) (inr (r , s)) = inl (p , (s ~◾ r ~⁻¹ ~◾ q))
_≈◾_ {𝔹} (inr (p , q)) (inl (r , s)) = inl ((p ~◾ q ~⁻¹ ~◾ r) , s)
_≈◾_ {𝔹} (inr (p , q)) (inr (r , s)) = inr (p , s)
_≈◾_ {A ⇒ B} p q = λ r → p r ≈◾ q (r ≈⁻¹ ≈◾ r)
_≈◾_ {A ⇒⁺ B} p q = λ r → p r ≈◾ q (r ≈⁻¹ ≈◾ r)
_≈◾_ {Top} p q = p
_≈◾_ {A * B} (p , q) (r , s) = (p ≈◾ r) , (q ≈◾ s)

infixr 4 _~◾≈_
_~◾≈_ : ∀ {A}{t t' t'' : Tm ∙ A} → t ~ t' → t' ≈ t'' → t ≈ t''
_~◾≈_ {𝔹} p (inl (q , r)) = inl ((p ~◾ q) , r)
_~◾≈_ {𝔹} p (inr (q , r)) = inr ((p ~◾ q) , r)
_~◾≈_ {Top}   p q = tt
_~◾≈_ {A * B} p (q , r) = (π₁ p ~◾≈ q) , (π₂ p ~◾≈ r)
_~◾≈_ {A ⇒ B} {t} {t'} {t''} p q {a} {a'} r = app p ~refl ~◾≈ q r
_~◾≈_ {A ⇒⁺ B} {t} {t'} {t''} p q {a} {a'} r = app⁺ p ~refl ~◾≈ q r

infixl 5 _≈◾~_
_≈◾~_ : ∀ {A}{t t' t'' : Tm ∙ A} → t ≈ t' → t' ~ t'' → t ≈ t''
p ≈◾~ q = (q ~⁻¹ ~◾≈ p ≈⁻¹) ≈⁻¹

infix 4 _≈ₛ_
_≈ₛ_ : ∀ {Γ} → Sub ∙ Γ → Sub ∙ Γ → Set
∙       ≈ₛ  ∙       = ⊤
(σ , t) ≈ₛ (δ , t') = (σ ≈ₛ δ) × (t ≈ t')

Tm≈ : ∀ {Γ A}(t : Tm Γ A) (σ σ' : Sub ∙ Γ) → σ ≈ₛ σ' → Tmₛ σ t ≈ Tmₛ σ' t
Tm≈ (var vz)     (σ , _) (σ' , _) σ≈ = ₂ σ≈
Tm≈ (var (vs x)) (σ , _) (σ' , _) σ≈ = Tm≈ (var x) σ σ' (₁ σ≈ )
Tm≈ tt         σ σ' σ≈ = tt
Tm≈ true       σ σ' σ≈ = inl (~refl , ~refl)
Tm≈ false      σ σ' σ≈ = inr (~refl , ~refl)
Tm≈ (if t u v) σ σ' σ≈ with Tm≈ t σ σ' σ≈
... | inl (p , q) =
  if p ~refl ~refl ~◾≈ true ~◾≈ Tm≈ u σ σ' σ≈ ≈◾~ (if q ~refl ~refl ~◾ true) ~⁻¹
... | inr (p , q) =
  if p ~refl ~refl ~◾≈ false ~◾≈ Tm≈ v σ σ' σ≈ ≈◾~ (if q ~refl ~refl ~◾ false) ~⁻¹
Tm≈ (π₁ t)     σ σ' σ≈ = ₁ (Tm≈ t σ σ' σ≈)
Tm≈ (π₂ t)     σ σ' σ≈ = ₂ (Tm≈ t σ σ' σ≈)
Tm≈ (t , u)    σ σ' σ≈ = (π₁β _ _ ~◾≈ Tm≈ t σ σ' σ≈ ≈◾~ π₁β _ _ ~⁻¹) ,
                         (π₂β _ _ ~◾≈ Tm≈ u σ σ' σ≈ ≈◾~ π₂β _ _ ~⁻¹)
Tm≈ (app t u)  σ σ' σ≈ = Tm≈ t σ σ' σ≈ (Tm≈ u σ σ' σ≈)
Tm≈ (app⁺ t u) σ σ' σ≈ = Tm≈ t σ σ' σ≈ (Tm≈ u σ σ' σ≈)
Tm≈ (pack t u) σ σ' σ≈ {a}{a'} p =
      βᶜ _ _ _
  ~◾≈ Tm≈ u σ σ' σ≈ {Tmₛ σ t , a}{Tmₛ σ' t , a'}
              ((π₁β _ _ ~◾≈ Tm≈ t σ σ' σ≈ ≈◾~ π₁β _ _ ~⁻¹) ,
               (π₂β _ _ ~◾≈ p ≈◾~ π₂β _ _ ~⁻¹))
  ≈◾~ βᶜ _ _ _ ~⁻¹
Tm≈ (lam t)    σ σ' σ≈ {a}{a'} p =
      β _ _
  ~◾≈ Tm≈ t (∙ , a) (∙ , a') (tt , p)
  ≈◾~ β _ _ ~⁻¹


≈refl : ∀ {A}{t : Tm ∙ A} → t ≈ t
≈refl {A} {t} = coe (_≈_ & Tm-idₛ t ⊗ Tm-idₛ t) (Tm≈ t idₛ idₛ tt)

~≈ : ∀ {A}{t t' : Tm ∙ A} → t ~ t' → t ≈ t'
~≈ p = p ~◾≈ ≈refl
