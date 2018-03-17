
{-# OPTIONS --without-K #-}

module CConv where

open import Lib
import Source.Syntax as S
import Source.LogicalEqv as S
import Target.Syntax as T
import Target.LogicalEqv as T
import ClosureBuilding as T

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
  T.~◾ T.lam⁺~ {t = (T.app⁺ (T.Tmₑ T.wk (Tm⁺ t)) (T.var T.vz))} {T.app⁺ (T.Tmₑ T.wk (Tm⁺ t')) (T.var T.vz)}
         (T.app⁺ (T.≡~ ((λ x → T.Tmₑ (T.drop x) (Tm⁺ t)) & (idₑ⁺ ⁻¹)) T.~◾ Tmₑ⁺ S.wk t T.~⁻¹) T.~refl T.~◾ ~⁺ p T.~◾ T.app⁺ (Tmₑ⁺ S.wk t' T.~◾ T.≡~ ((λ x → T.Tmₑ (T.drop x) (Tm⁺ t')) & idₑ⁺)) T.~refl)
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

infixl 5 _≈◾_
_≈◾_ : ∀ {A}{t : S.Tm S.∙ A}{t' t'' : T.Tm T.∙ (Ty⁺ A)} → t ≈ t' → t' T.≈ t'' → t ≈ t''
_≈◾_ {S.𝔹} (inl (p , q)) (inl (r , s)) = inl (p , s)
_≈◾_ {S.𝔹} (inl (p , q)) (inr (r , s)) = inl (p , (s T.~◾ r T.~⁻¹ T.~◾ q))
_≈◾_ {S.𝔹} (inr (p , q)) (inl (r , s)) = inr (p , (s T.~◾ r T.~⁻¹ T.~◾ q))
_≈◾_ {S.𝔹} (inr (p , q)) (inr (r , s)) = inr (p , s)
_≈◾_ {S.Top}   p q = tt
_≈◾_ {A S.* B} (p , q) (r , s) = (p ≈◾ r) , (q ≈◾ s)
_≈◾_ {A S.⇒ B} p q r = p r ≈◾ q T.≈refl

triangle : ∀ {A}{t : S.Tm S.∙ A}{t' t''} → t ≈ t' → t ≈ t'' → t' T.≈ t''
triangle {S.𝔹} (inl (p , q)) (inl (r , s)) = inl (q , s)
triangle {S.𝔹} (inl (p , q)) (inr (r , s)) = {!r S.~⁻¹ S.~◾ p!}
triangle {S.𝔹} (inr (p , q)) (inl (r , s)) = {!!}
triangle {S.𝔹} (inr (p , q)) (inr (r , s)) = inr (q , s)
triangle {S.Top}   p q = tt
triangle {A S.* B} p q = {!!}
triangle {A S.⇒ B} p q = {!!}

-- infix 6 _⁻¹
-- _⁻ : ∀ {A Γ} → T.Tm (Con⁺ Γ) (Ty⁺ A) → S.Tm Γ A
-- _⁻ = {!!}

-- ⁻≈ : ∀ {A}(t : T.Tm T.∙ (Ty⁺ A)) → t ⁻ ≈ t
-- ⁻≈ = {!!}

Tm≈⁺ : ∀ {A}(t : S.Tm S.∙ A) → t ≈ Tm⁺ t
Tm≈⁺ {A} t = {!!}

abs : ∀ {A}{t t' : S.Tm S.∙ A} → t S.≈ t' → Tm⁺ t T.≈ Tm⁺ t'
abs {A} {t} {t'} p = triangle {A} (Tm≈⁺ t) (p ◾≈ Tm≈⁺ t')
