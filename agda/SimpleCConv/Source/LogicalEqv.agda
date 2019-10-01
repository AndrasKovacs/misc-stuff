
module Source.LogicalEqv where

open import Lib
open import Source.Syntax

infix 4 _≈_
_≈_ : ∀ {A} → Tm ∙ A → Tm ∙ A → Set
_≈_ {𝔹}      t u = ((t ~ true) × (u ~ true)) ⊎ ((t ~ false) × (u ~ false))
_≈_ {Top}    t u = ⊤
_≈_ {A * B}  t u = (π₁ t ≈ π₁ u) × (π₂ t ≈ π₂ u)
_≈_ {A ⇒ B}  t u = ∀ {a a'} → a ≈ a' → app t a ≈ app u a'

infixr 4 _~◾≈_
_~◾≈_ : ∀ {A}{t t' t'' : Tm ∙ A} → t ~ t' → t' ≈ t'' → t ≈ t''
_~◾≈_ {𝔹} p (inl (q , r)) = inl ((p ~◾ q) , r)
_~◾≈_ {𝔹} p (inr (q , r)) = inr ((p ~◾ q) , r)
_~◾≈_ {Top}   p q = tt
_~◾≈_ {A * B} p (q , r) = (π₁ p ~◾≈ q) , (π₂ p ~◾≈ r)
_~◾≈_ {A ⇒ B} {t} {t'} {t''} p q {a} {a'} r = app p ~refl ~◾≈ q r

infixl 5 _≈◾~_
_≈◾~_ : ∀ {A}{t t' t'' : Tm ∙ A} → t ≈ t' → t' ~ t'' → t ≈ t''
_≈◾~_ {𝔹} (inl p) q = inl ((₁ p) , (q ~⁻¹ ~◾ ₂ p))
_≈◾~_ {𝔹} (inr p) q = inr ((₁ p) , (q ~⁻¹ ~◾ ₂ p))
_≈◾~_ {Top}   p q = tt
_≈◾~_ {A * B} (p , q) r = (p ≈◾~ π₁ r) , (q ≈◾~ π₂ r)
_≈◾~_ {A ⇒ B} p q r = p r ≈◾~ app q ~refl

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
Tm≈ (lam t)    σ σ' σ≈ {a}{a'} p =
       β _ _
   ~◾≈ ≡~ (Tm-∘ₛ (keepₛ σ) (∙ , a) t ⁻¹)
   ~◾≈ ≡~ ((λ x → Tmₛ (x , a) t) & (assₛₑₛ σ wk (∙ , a) ◾ idrₛ σ))
   ~◾≈ Tm≈ t (σ , a) (σ' , a') (σ≈ , p)
   ≈◾~ ≡~ ((λ x → Tmₛ (x , a') t) & (idrₛ σ' ⁻¹ ◾ assₛₑₛ σ' wk (∙ , a') ⁻¹))
   ≈◾~ ≡~ (Tm-∘ₛ (keepₛ σ') (∙ , a') t)
   ≈◾~ β (Tmₛ (keepₛ σ') t) a' ~⁻¹

--------------------------------------------------------------------------------

≈refl : ∀ {A}{t : Tm ∙ A} → t ≈ t
≈refl {A} {t} = coe (_≈_ & Tm-idₛ t ⊗ Tm-idₛ t) (Tm≈ t idₛ idₛ tt)

~≈ : ∀ {A}{t t' : Tm ∙ A} → t ~ t' → t ≈ t'
~≈ p = p ~◾≈ ≈refl

canonicity : (t : Tm ∙ 𝔹) → t ~ true ⊎ t ~ false
canonicity t with ≈refl {_}{t}
... | inl (p , _) = inl p
... | inr (p , _) = inr p
