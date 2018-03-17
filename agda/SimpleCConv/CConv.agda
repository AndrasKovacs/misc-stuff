
{-# OPTIONS --without-K #-}

module CConv where

open import Lib
import Source.Syntax as S
import Source.LogicalEqv as S
import Source.StdModel as S
import Target.Syntax as T
import Target.LogicalEqv as T
import Target.ClosureBuilding as T

-- Closure conversion
--------------------------------------------------------------------------------

Ty⁺ : S.Ty → T.Ty
Ty⁺ S.𝔹       = T.𝔹
Ty⁺ S.Top     = T.Top
Ty⁺ (A S.* B) = Ty⁺ A T.* Ty⁺ B
Ty⁺ (A S.⇒ B) = Ty⁺ A T.⇒⁺ Ty⁺ B

Con⁺ : S.Con → T.Con
Con⁺ S.∙       = T.∙
Con⁺ (Γ S.▶ A) = Con⁺ Γ T.▶ Ty⁺ A

∈⁺ : ∀ {Γ A} → A S.∈ Γ → Ty⁺ A T.∈ Con⁺ Γ
∈⁺ S.vz     = T.vz
∈⁺ (S.vs x) = T.vs (∈⁺ x)

Tm⁺ : ∀ {Γ A} → S.Tm Γ A → T.Tm (Con⁺ Γ) (Ty⁺ A)
Tm⁺ S.true       = T.true
Tm⁺ S.false      = T.false
Tm⁺ (S.if t u v) = T.if (Tm⁺ t) (Tm⁺ u) (Tm⁺ v)
Tm⁺ (S.var x)    = T.var (∈⁺ x)
Tm⁺ (S.lam t)    = T.lam⁺ (Tm⁺ t)
Tm⁺ (S.app t u)  = T.app⁺ (Tm⁺ t) (Tm⁺ u)
Tm⁺ S.tt         = T.tt
Tm⁺ (S.π₁ t)     = T.π₁ (Tm⁺ t)
Tm⁺ (S.π₂ t)     = T.π₂ (Tm⁺ t)
Tm⁺ (t S., u)    = Tm⁺ t T., Tm⁺ u

-- Def. eq. preservation
--------------------------------------------------------------------------------

OPE⁺ : ∀ {Γ Δ} → S.OPE Γ Δ → T.OPE (Con⁺ Γ) (Con⁺ Δ)
OPE⁺ S.∙        = T.∙
OPE⁺ (S.drop σ) = T.drop (OPE⁺ σ)
OPE⁺ (S.keep σ) = T.keep (OPE⁺ σ)

∈ₑ⁺ : ∀ {Γ Δ A}(σ : S.OPE Γ Δ)(x : A S.∈ Δ) → ∈⁺ (S.∈ₑ σ x) ≡ T.∈ₑ (OPE⁺ σ) (∈⁺ x)
∈ₑ⁺ S.∙ ()
∈ₑ⁺ (S.drop σ) x        = T.vs & ∈ₑ⁺ σ x
∈ₑ⁺ (S.keep σ) S.vz     = refl
∈ₑ⁺ (S.keep σ) (S.vs x) = T.vs & ∈ₑ⁺ σ x

idₑ⁺ : ∀ {Γ} → OPE⁺ (S.idₑ {Γ}) ≡ T.idₑ
idₑ⁺ {S.∙}     = refl
idₑ⁺ {Γ S.▶ A} = T.keep & idₑ⁺ {Γ}

Tmₑ⁺ :
  ∀ {Γ Δ A}(σ : S.OPE Γ Δ)(t : S.Tm Δ A) → Tm⁺ (S.Tmₑ σ t) T.~ T.Tmₑ (OPE⁺ σ) (Tm⁺ t)
Tmₑ⁺ σ S.true       = T.~refl
Tmₑ⁺ σ S.false      = T.~refl
Tmₑ⁺ σ (S.if t u v) = T.if (Tmₑ⁺ σ t) (Tmₑ⁺ σ u) (Tmₑ⁺ σ v)
Tmₑ⁺ σ (S.var x)    = T.≡~ (T.var & ∈ₑ⁺ σ x)
Tmₑ⁺ σ (S.lam t)    = T.lam⁺~ (Tmₑ⁺ (S.keep σ) t) T.~◾ T.Tmₑ-lam⁺ (OPE⁺ σ) (Tm⁺ t) T.~⁻¹
Tmₑ⁺ σ (S.app t u)  = T.app⁺ (Tmₑ⁺ σ t) (Tmₑ⁺ σ u)
Tmₑ⁺ σ S.tt         = T.~refl
Tmₑ⁺ σ (S.π₁ t)     = T.π₁ (Tmₑ⁺ σ t)
Tmₑ⁺ σ (S.π₂ t)     = T.π₂ (Tmₑ⁺ σ t)
Tmₑ⁺ σ (t S., u)    = Tmₑ⁺ σ t T., Tmₑ⁺ σ u

Sub⁺ : ∀ {Γ Δ} → S.Sub Γ Δ → T.Sub (Con⁺ Γ) (Con⁺ Δ)
Sub⁺ S.∙       = T.∙
Sub⁺ (σ S., t) = Sub⁺ σ T., Tm⁺ t

ₛ∘ₑ⁺ : ∀ {Γ Δ Σ}(σ : S.Sub Δ Σ)(δ : S.OPE Γ Δ) → Sub⁺ (σ S.ₛ∘ₑ δ) T.~ₛ Sub⁺ σ T.ₛ∘ₑ OPE⁺ δ
ₛ∘ₑ⁺ S.∙       δ = T.~ₛrefl _
ₛ∘ₑ⁺ (σ S., t) δ = ₛ∘ₑ⁺ σ δ T., Tmₑ⁺ δ t

dropₛ⁺ : ∀ {Γ Δ A} (σ : S.Sub Γ Δ) → Sub⁺ (S.dropₛ {A} σ) T.~ₛ T.dropₛ (Sub⁺ σ)
dropₛ⁺ σ = ₛ∘ₑ⁺ σ S.wk T.~ₛ◾ T.≡~ₛ ((Sub⁺ σ T.ₛ∘ₑ_) & (T.drop & idₑ⁺))

keepₛ⁺ : ∀ {Γ Δ A} (σ : S.Sub Γ Δ) → Sub⁺ (S.keepₛ {A} σ) T.~ₛ T.keepₛ (Sub⁺ σ)
keepₛ⁺ σ = dropₛ⁺ σ T., T.~refl

idₛ⁺ : ∀ {Γ} → Sub⁺ (S.idₛ {Γ}) T.~ₛ T.idₛ
idₛ⁺ {S.∙}     = T.∙
idₛ⁺ {Γ S.▶ A} = keepₛ⁺ (S.idₛ{Γ}) T.~ₛ◾ T.keepₛ~ (idₛ⁺{Γ})

∈ₛ⁺ :
  ∀ {Γ Δ A}(σ : S.Sub Γ Δ)(x : A S.∈ Δ) → Tm⁺ (S.∈ₛ σ x) T.~ T.Tmₛ (Sub⁺ σ) (Tm⁺ (S.var x))
∈ₛ⁺ (σ S., _) S.vz     = T.~refl
∈ₛ⁺ (σ S., _) (S.vs x) = ∈ₛ⁺ σ x

Tmₛ⁺ :
  ∀ {Γ Δ A}(σ : S.Sub Γ Δ)(t : S.Tm Δ A) → Tm⁺ (S.Tmₛ σ t) T.~ T.Tmₛ (Sub⁺ σ) (Tm⁺ t)
Tmₛ⁺ σ S.true = T.~refl
Tmₛ⁺ σ S.false = T.~refl
Tmₛ⁺ σ (S.if t u v) = T.if (Tmₛ⁺ σ t) (Tmₛ⁺ σ u) (Tmₛ⁺ σ v)
Tmₛ⁺ σ (S.var x) = ∈ₛ⁺ σ x
Tmₛ⁺ σ (S.lam t) =
       T.lam⁺~ (Tmₛ⁺ (S.keepₛ σ) t
  T.~◾ T.Tmₛ~t (keepₛ⁺ σ) (Tm⁺ t))
  T.~◾ T.Tmₛ-lam⁺ (Sub⁺ σ) (Tm⁺ t) T.~⁻¹
Tmₛ⁺ σ (S.app t u) = T.app⁺ (Tmₛ⁺ σ t) (Tmₛ⁺ σ u)
Tmₛ⁺ σ S.tt        = T.~refl
Tmₛ⁺ σ (S.π₁ t)    = T.π₁ (Tmₛ⁺ σ t)
Tmₛ⁺ σ (S.π₂ t)    = T.π₂ (Tmₛ⁺ σ t)
Tmₛ⁺ σ (t S., u)   = Tmₛ⁺ σ t T., Tmₛ⁺ σ u

~⁺ : ∀ {Γ A}{t t' : S.Tm Γ A} → t S.~ t' → Tm⁺ t T.~ Tm⁺ t'
~⁺ (S.β t t') =
       T.β⁺ (Tm⁺ t) (Tm⁺ t')
  T.~◾ T.Tmₛ~t ((idₛ⁺ T.~ₛ⁻¹) T., T.~refl) (Tm⁺ t)
  T.~◾ Tmₛ⁺ (S.idₛ S., t') t T.~⁻¹
~⁺ {Γ} {t = t} {t'} (S.η {A} {B} p) =
       T.η⁺ (Tm⁺ t)
  T.~◾ T.lam⁺~ (T.app⁺ (T.≡~ ((λ x → T.Tmₑ (T.drop x) (Tm⁺ t)) & (idₑ⁺ ⁻¹)) T.~◾ Tmₑ⁺ S.wk t T.~⁻¹) T.~refl
          T.~◾ ~⁺ p T.~◾ T.app⁺ (Tmₑ⁺ S.wk t' T.~◾ T.≡~ ((λ x → T.Tmₑ (T.drop x) (Tm⁺ t')) & idₑ⁺)) T.~refl)
  T.~◾ T.η⁺ (Tm⁺ t') T.~⁻¹
~⁺ (S.lam t) = T.lam⁺~ (~⁺ t)
~⁺ (S.app t u) = T.app⁺ (~⁺ t) (~⁺ u)
~⁺ S.true = T.true
~⁺ S.false = T.false
~⁺ (S.if t u v) = T.if (~⁺ t) (~⁺ u) (~⁺ v)
~⁺ S.~refl = T.~refl
~⁺ (t S.~⁻¹) = ~⁺ t T.~⁻¹
~⁺ (t S.~◾ u) = ~⁺ t T.~◾ ~⁺ u
~⁺ (S.π₁ t)    = T.π₁ (~⁺ t)
~⁺ (S.π₂ t)    = T.π₂ (~⁺ t)
~⁺ (t S., u)   = ~⁺ t T., ~⁺ u
~⁺ (S.π₁β t u) = T.π₁β (Tm⁺ t) (Tm⁺ u)
~⁺ (S.π₂β t u) = T.π₂β (Tm⁺ t) (Tm⁺ u)
~⁺ (S.,η t)    = T.,η (Tm⁺ t)
~⁺ S.ttη       = T.ttη

-- Back-translation
--------------------------------------------------------------------------------

Ty⁻ : T.Ty → S.Ty
Ty⁻ T.𝔹        = S.𝔹
Ty⁻ T.Top      = S.Top
Ty⁻ (A T.*  B) = Ty⁻ A S.* Ty⁻ B
Ty⁻ (A T.⇒⁺ B) = Ty⁻ A S.⇒ Ty⁻ B
Ty⁻ (A T.⇒  B) = Ty⁻ A S.⇒ Ty⁻ B

Ty⁻⁺ : ∀ A → Ty⁻ (Ty⁺ A) ≡ A
Ty⁻⁺ S.𝔹       = refl
Ty⁻⁺ S.Top     = refl
Ty⁻⁺ (A S.* B) = S._*_ & Ty⁻⁺ A ⊗ Ty⁻⁺ B
Ty⁻⁺ (A S.⇒ B) = S._⇒_ & Ty⁻⁺ A ⊗ Ty⁻⁺ B

Con⁻ : T.Con → S.Con
Con⁻ T.∙       = S.∙
Con⁻ (Γ T.▶ A) = Con⁻ Γ S.▶ Ty⁻ A

Con⁻⁺ : ∀ Γ → Con⁻ (Con⁺ Γ) ≡ Γ
Con⁻⁺ S.∙ = refl
Con⁻⁺ (Γ S.▶ A) = S._▶_ & Con⁻⁺ Γ ⊗ Ty⁻⁺ A

∈⁻ : ∀ {Γ A} → A T.∈ Γ → Ty⁻ A S.∈ Con⁻ Γ
∈⁻ T.vz     = S.vz
∈⁻ (T.vs x) = S.vs (∈⁻ x)

Tm⁻ : ∀ {Γ A} → T.Tm Γ A → S.Tm (Con⁻ Γ) (Ty⁻ A)
Tm⁻ (T.var x) = S.var (∈⁻ x)
Tm⁻ T.tt = S.tt
Tm⁻ T.true = S.true
Tm⁻ T.false = S.false
Tm⁻ (T.if t u v) = S.if (Tm⁻ t) (Tm⁻ u) (Tm⁻ v)
Tm⁻ (T.π₁ t) = S.π₁ (Tm⁻ t)
Tm⁻ (T.π₂ t) = S.π₂ (Tm⁻ t)
Tm⁻ (t T., u) = Tm⁻ t S., Tm⁻ u
Tm⁻ (T.pack t u) = S.lam (S.app (S.Tmₑ S.wk (Tm⁻ u)) (S.Tmₑ S.wk (Tm⁻ t) S., S.var S.vz))
Tm⁻ (T.app⁺ t u) = S.app (Tm⁻ t) (Tm⁻ u)
Tm⁻ (T.lam t) = S.lam (S.Tmₑ (S.keep S.εₑ) (Tm⁻ t))
Tm⁻ (T.app t u) = S.app (Tm⁻ t) (Tm⁻ u)

Tm⁻' : ∀ {A} → T.Tm T.∙ (Ty⁺ A) → S.Tm S.∙ A
Tm⁻' {A} t = coe (S.Tm S.∙ & Ty⁻⁺ A) (Tm⁻ t)

-- Full abstraction
--------------------------------------------------------------------------------

infixr 4 _≈_
_≈_ : ∀ {A} → S.Tm S.∙ A → T.Tm T.∙ (Ty⁺ A) → Set
_≈_ {S.Top}   t t' = ⊤
_≈_ {A S.* B} t t' = (S.π₁ t ≈ T.π₁ t') × (S.π₂ t ≈ T.π₂ t')
_≈_ {S.𝔹}     t t' = (t S.~ S.true × (t' T.~ T.true)) ⊎ (t S.~ S.false × (t' T.~ T.false))
_≈_ {A S.⇒ B} t t' = ∀ {a a'} → a ≈ a' → S.app t a ≈ T.app⁺ t' a'

infixr 4 _◾≈_
_◾≈_ : ∀ {A}{t t' : S.Tm S.∙ A}{t'' : T.Tm T.∙ (Ty⁺ A)} → t S.≈ t' → t' ≈ t'' → t ≈ t''
_◾≈_ {S.𝔹} (inl (p , q)) (inl (r , s)) = inl (p , s)
_◾≈_ {S.𝔹} (inl (p , q)) (inr (r , s)) = inr ((p S.~◾ q S.~⁻¹ S.~◾ r) , s)
_◾≈_ {S.𝔹} (inr (p , q)) (inl (r , s)) = inl ((p S.~◾ q S.~⁻¹ S.~◾ r) , s)
_◾≈_ {S.𝔹} (inr (p , q)) (inr (r , s)) = inr (p , s)
_◾≈_ {A S.* B} (p , q) (r , s) = (p ◾≈ r) , (q ◾≈ s)
_◾≈_ {S.Top} p q = tt
_◾≈_ {A S.⇒ B} p q r = p S.≈refl ◾≈ q r

infixr 4 _~◾≈_
_~◾≈_ : ∀ {A}{t t' : S.Tm S.∙ A}{t'' : T.Tm T.∙ (Ty⁺ A)} → t S.~ t' → t' ≈ t'' → t ≈ t''
p ~◾≈ q = S.~≈ p ◾≈ q

infixl 5 _≈◾_
_≈◾_ : ∀ {A}{t : S.Tm S.∙ A}{t' t'' : T.Tm T.∙ (Ty⁺ A)} → t ≈ t' → t' T.≈ t'' → t ≈ t''
_≈◾_ {S.𝔹} (inl (p , q)) (inl (r , s)) = inl (p , s)
_≈◾_ {S.𝔹} (inl (p , q)) (inr (r , s)) = inl (p , (s T.~◾ r T.~⁻¹ T.~◾ q))
_≈◾_ {S.𝔹} (inr (p , q)) (inl (r , s)) = inr (p , (s T.~◾ r T.~⁻¹ T.~◾ q))
_≈◾_ {S.𝔹} (inr (p , q)) (inr (r , s)) = inr (p , s)
_≈◾_ {S.Top}   p q = tt
_≈◾_ {A S.* B} (p , q) (r , s) = (p ≈◾ r) , (q ≈◾ s)
_≈◾_ {A S.⇒ B} p q r = p r ≈◾ q T.≈refl

infixl 5 _≈◾~_
_≈◾~_ : ∀ {A}{t : S.Tm S.∙ A}{t' t'' : T.Tm T.∙ (Ty⁺ A)} → t ≈ t' → t' T.~ t'' → t ≈ t''
_≈◾~_ p q = p ≈◾ T.~≈ q

infixr 4 _≈ₛ_
_≈ₛ_ : ∀ {Γ} → S.Sub S.∙ Γ → T.Sub T.∙ (Con⁺ Γ) → Set
S.∙       ≈ₛ T.∙        = ⊤
(σ S., t) ≈ₛ (δ T., t') = (σ ≈ₛ δ) × t ≈ t'

--------------------------------------------------------------------------------

-- ∈⁻≈ : ∀ {Γ Γ⁺ A A⁺}(x : A⁺ T.∈ Γ⁺) (σ : S.Sub S.∙ Γ) (σ' : T.Sub T.∙ (Con⁺ Γ))
--      → (Γp : Γ⁺ ≡ Con⁺ Γ)
--      → (Ap : A⁺ ≡ Ty⁺ A)
--      → σ ≈ₛ σ'
--      → S.∈ₛ σ (coe (S._∈_ & (Ty⁻ & Ap ◾ Ty⁻⁺ A) ⊗ (Con⁻ & Γp ◾ Con⁻⁺ Γ)) (∈⁻ x))
--      ≈ T.∈ₛ σ' (coe (T._∈_ & Ap ⊗ Γp) x)
-- ∈⁻≈ {S.∙} T.vz σ σ' () Ap σ≈
-- ∈⁻≈ {Γ₁ S.▶ x} {A = A} T.vz (σ S., x₁) (σ' T., x₂) refl Ap (σ≈ , foo) = {!!}
-- ∈⁻≈ {S.∙} (T.vs x) σ σ' () Ap σ≈
-- ∈⁻≈ {Γ S.▶ A} {A = B} (T.vs x) (σ S., _) (σ' T., _) refl refl (σ≈ , _)
--   = {!∈⁻≈ x σ σ' refl refl σ≈!}

-- ⁻≈ : ∀ {Γ Γ⁺ A A⁺}(t : T.Tm Γ⁺ A⁺) (σ : S.Sub S.∙ Γ) (σ' : T.Sub T.∙ (Con⁺ Γ))
--      → (Γp : Γ⁺ ≡ Con⁺ Γ)
--      → (Ap : A⁺ ≡ Ty⁺ A)
--      → σ ≈ₛ σ'
--      → S.Tmₛ σ  (coe (S.Tm & (Con⁻ & Γp ◾ Con⁻⁺ Γ) ⊗ (Ty⁻ & Ap ◾ Ty⁻⁺ A)) (Tm⁻ t))
--      ≈ T.Tmₛ σ' (coe (T.Tm & Γp ⊗ Ap) t)
-- ⁻≈ (T.var x) σ σ' σ≈ Γp Ap = {!∈⁻≈ x σ σ' σ≈ Γp Ap!}
-- ⁻≈ T.tt σ σ' σ≈ Γp Ap = {!!}
-- ⁻≈ T.true σ σ' σ≈ Γp Ap = {!!}
-- ⁻≈ T.false σ σ' σ≈ Γp Ap = {!!}
-- ⁻≈ (T.if t u v) σ σ' σ≈ Γp Ap = {!!}
-- ⁻≈ (T.π₁ t) σ σ' σ≈ Γp Ap = {!!}
-- ⁻≈ (T.π₂ t) σ σ' σ≈ Γp Ap = {!!}
-- ⁻≈ (t T., u) σ σ' σ≈ Γp Ap = {!!}
-- ⁻≈ (T.pack t u) σ σ' σ≈ Γp Ap = {!!}
-- ⁻≈ (T.app⁺ t u) σ σ' σ≈ Γp Ap = {!!}
-- ⁻≈ (T.lam t) σ σ' σ≈ Γp Ap = {!!}
-- ⁻≈ (T.app t u) σ σ' σ≈ Γp Ap = {!!}

⁻≈' : ∀ {A}(t : T.Tm T.∙ (Ty⁺ A)) → Tm⁻' t ≈ t
⁻≈' = {!!}

triangle : ∀ {A}{t : S.Tm S.∙ A}{t' t''} → t ≈ t' → t ≈ t'' → t' T.≈ t''
triangle {S.𝔹} (inl (p , q)) (inl (r , s)) = inl (q , s)
triangle {S.𝔹} (inl (p , q)) (inr (r , s)) = ⊥-elim (S.consistent (p S.~⁻¹ S.~◾ r))
triangle {S.𝔹} (inr (p , q)) (inl (r , s)) = ⊥-elim (S.consistent (r S.~⁻¹ S.~◾ p))
triangle {S.𝔹} (inr (p , q)) (inr (r , s)) = inr (q , s)
triangle {S.Top}   p q = tt
triangle {A S.* B} (p , q) (r , s) = triangle p r , triangle q s
triangle {A S.⇒ B} p q {a} {a'} r = triangle (p (⁻≈' a)) (q ((⁻≈' a) ≈◾ r))


∈≈⁺ : ∀ {Γ A}(x : A S.∈ Γ) σ σ' → σ ≈ₛ σ' → S.∈ₛ σ x ≈ T.∈ₛ σ' (∈⁺ x)
∈≈⁺ S.vz (σ S., x) (σ' T., x₁) σ≈ = ₂ σ≈
∈≈⁺ (S.vs x) (σ S., x₁) (σ' T., x₂) σ≈ = ∈≈⁺ x σ σ' (₁ σ≈)

Tm≈⁺ : ∀ {Γ A}(t : S.Tm Γ A) σ σ' → σ ≈ₛ σ' → S.Tmₛ σ t ≈ T.Tmₛ σ' (Tm⁺ t)
Tm≈⁺ (S.var x) σ σ' σ≈ = ∈≈⁺ x σ σ' σ≈
Tm≈⁺ S.tt σ σ' σ≈ = tt
Tm≈⁺ S.true σ σ' σ≈ = inl (S.~refl , T.~refl)
Tm≈⁺ S.false σ σ' σ≈ = inr (S.~refl , T.~refl)
Tm≈⁺ (S.if t u v) σ σ' σ≈ with Tm≈⁺ t σ σ' σ≈
... | inl (p , q) =
      S.if p S.~refl S.~refl
  ~◾≈ S.true
  ~◾≈ Tm≈⁺ u σ σ' σ≈
  ≈◾~ T.true T.~⁻¹
  ≈◾~ T.if (q T.~⁻¹) T.~refl T.~refl
... | inr (p , q) =
      S.if p S.~refl S.~refl
  ~◾≈ S.false
  ~◾≈ Tm≈⁺ v σ σ' σ≈
  ≈◾~ T.false T.~⁻¹
  ≈◾~ T.if (q T.~⁻¹) T.~refl T.~refl
Tm≈⁺ (S.π₁ t) σ σ' σ≈ = Tm≈⁺ t σ σ' σ≈ .₁
Tm≈⁺ (S.π₂ t) σ σ' σ≈ = Tm≈⁺ t σ σ' σ≈ .₂
Tm≈⁺ (t S., u) σ σ' σ≈ =
  (S.π₁β _ _  ~◾≈ Tm≈⁺ t σ σ' σ≈ ≈◾~ T.π₁β _ _ T.~⁻¹) ,
  (S.π₂β _ _  ~◾≈ Tm≈⁺ u σ σ' σ≈ ≈◾~ T.π₂β _ _ T.~⁻¹)
Tm≈⁺ (S.app t u) σ σ' σ≈ = Tm≈⁺ t σ σ' σ≈ (Tm≈⁺ u σ σ' σ≈)
Tm≈⁺ (S.lam t) σ σ' σ≈ {a}{a'} p =
      S.β _ _
  ~◾≈ S.≡~ (S.Tm-∘ₛ (S.keepₛ σ) (S.idₛ S., a) t ⁻¹)
  ~◾≈ S.≡~ ((λ x → S.Tmₛ (x S., a) t) & (S.assₛₑₛ _ _ _ ◾ S.idrₛ σ))
  ~◾≈ Tm≈⁺ t (σ S., a) (σ' T., a') (σ≈ , p)
  ≈◾~ T.≡~ ((λ x → T.Tmₛ (x T., a') (Tm⁺ t)) &
           (T.idrₛ σ' ⁻¹ ◾ T.assₛₑₛ σ' T.wk (T.∙ T., a') ⁻¹))
  ≈◾~ T.≡~ (T.Tm-∘ₛ (T.keepₛ σ') (T.∙ T., a') (Tm⁺ t))
  ≈◾~ T.β⁺ (T.Tmₛ (T.keepₛ σ') (Tm⁺ t)) a' T.~⁻¹
  ≈◾~ T._~_.app⁺ (T.Tmₛ-lam⁺ σ' (Tm⁺ t)) T.~refl T.~⁻¹

Tm≈⁺' : ∀ {A}(t : S.Tm S.∙ A) → t ≈ Tm⁺ t
Tm≈⁺' {A} t = coe (_≈_ & S.Tm-idₛ t ⊗ T.Tm-idₛ (Tm⁺ t)) (Tm≈⁺ t S.idₛ T.idₛ tt)

abstraction : ∀ {A}{t t' : S.Tm S.∙ A} → t S.≈ t' → Tm⁺ t T.≈ Tm⁺ t'
abstraction {A} {t} {t'} p = triangle {A} (Tm≈⁺' t) (p ◾≈ Tm≈⁺' t')
