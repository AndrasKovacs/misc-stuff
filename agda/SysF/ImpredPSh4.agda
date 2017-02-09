
{-# OPTIONS --without-K --type-in-type #-}

-- note: interpretation of universe for dependent TT PSh:

-- ⟦ U ⟧ : C → Set₀
-- ⟦ U ⟧ I = ∀ J → C(J, I) → Set₀

-- Huber thesis pg. 31: "U(I) consists of Set₀-valued presheaves over C/I (slice category over I)"
-- todo : rename Ren to OPE

module ImpredPSh4 where

open import Lib
open import JM
open import Syntax

-- the following is very neat:
-- *ᴹ : PSh OPE
-- *ᴹ I = PSh (OPE/I)

*ᴹ : ∀ {Γ'} → Con Γ' → Set₁ -- note Set₁
*ᴹ {Γ'} Γ = ∀ {Δ' Δ σ'} → OPE {Δ'} σ' Δ Γ → Set

*ᴹₑ : ∀ {Γ' Γ Δ' Δ σ'} → OPE {Δ'}{Γ'} σ' Δ Γ → *ᴹ Γ → *ᴹ Δ
*ᴹₑ σ Aᴹ δ = Aᴹ (σ ∘ₑ δ)

*ᴹ-∘ₑ :
  ∀ {Γ' Γ Δ' Δ Σ' Σ}{σ'}(σ : OPE {Δ'}{Σ'} σ' Δ Σ){δ'}(δ : OPE {Γ'}{Δ'} δ' Γ Δ)
    (Aᴹ : *ᴹ {Σ'} Σ)
  → (λ {x y z} → *ᴹₑ (σ ∘ₑ δ) Aᴹ {x}{y}{z}) ≡ *ᴹₑ δ (*ᴹₑ σ Aᴹ)
*ᴹ-∘ₑ σ δ Aᴹ = exti λ Δ' → exti λ Δ → exti λ ν' → ext λ ν → {!_∘ₑ_!}

data Con'ᴹ : Con' → ∀ {Δ'} → Con Δ' → Set where
  ∙   : ∀ {Δ' Δ} → Con'ᴹ ∙ {Δ'} Δ
  _,_ : ∀ {Γ' Δ' Δ} → Con'ᴹ Γ' {Δ'} Δ → *ᴹ Δ → Con'ᴹ (Γ' ,*) Δ

Con'ᴹₑ : ∀ {Γ' Δ' Δ Σ' Σ σ'} → OPE {Σ'} {Δ'} σ' Σ Δ → Con'ᴹ Γ' Δ → Con'ᴹ Γ' Σ
Con'ᴹₑ σ ∙          = ∙
Con'ᴹₑ σ (Γ'ᴹ , Aᴹ) = Con'ᴹₑ σ Γ'ᴹ , *ᴹₑ σ Aᴹ

Con'ᴹ-∘ₑ :
  ∀ {Γ' Γ Δ' Δ Σ' Σ σ' δ'} (σ : OPE {Δ'}{Σ'} σ' Δ Σ) (δ : OPE {Γ'}{Δ'} δ' Γ Δ) (Γ'ᴹ : Con'ᴹ Γ' Σ)
  → Con'ᴹₑ (σ ∘ₑ δ) Γ'ᴹ ≡ Con'ᴹₑ δ (Con'ᴹₑ σ Γ'ᴹ)
Con'ᴹ-∘ₑ σ δ ∙          = refl
Con'ᴹ-∘ₑ σ δ (Γ'ᴹ , Aᴹ) = _,_ & {!Con'ᴹ-∘ₑ σ δ!} ⊗ *ᴹ-∘ₑ σ δ Aᴹ

*∈ᴹ : ∀ {Γ'} → *∈ Γ' → ∀ {Δ' Δ} → Con'ᴹ Γ' {Δ'} Δ → Set
*∈ᴹ vz     {Δ'}{Δ} (Γ'ᴹ , Aᴹ) = Aᴹ idₑ  -- idₑ terminal obj. in slice cat.
*∈ᴹ (vs v) {Δ'}{Δ} (Γ'ᴹ , Aᴹ) = *∈ᴹ v Γ'ᴹ

Tyᴹ : ∀ {Γ'} → Ty Γ' → ∀ {Δ' Δ} → Con'ᴹ Γ' {Δ'} Δ → Set
Tyᴹ (var v) {Δ'}{Δ} Γ'ᴹ = *∈ᴹ v Γ'ᴹ
Tyᴹ (A ⇒ B) {Δ'}{Δ} Γ'ᴹ =
  ∀ {Σ' Σ σ'}(σ : OPE {Σ'} σ' Σ Δ) → Tyᴹ A (Con'ᴹₑ σ Γ'ᴹ) → Tyᴹ B (Con'ᴹₑ σ Γ'ᴹ)
Tyᴹ (∀' A)  {Δ'}{Δ} Γ'ᴹ =
  ∀ {Σ' Σ σ'}(σ : OPE {Σ'} σ' Σ Δ) → (Bᴹ : *ᴹ Σ) → Tyᴹ A (Con'ᴹₑ σ Γ'ᴹ , Bᴹ)

*∈ᴹₑ : ∀ {Γ'}(v : *∈ Γ'){Δ' Δ Σ' Σ σ' Γ'ᴹ}(σ : OPE {Σ'}{Δ'} σ' Σ Δ) → *∈ᴹ v Γ'ᴹ → *∈ᴹ v (Con'ᴹₑ σ Γ'ᴹ)
*∈ᴹₑ vz     {Γ'ᴹ = Γ'ᴹ , Aᴹ} σ tᴹ = {!!} -- todo: *ᴹ I : PSh (OPE/I)
*∈ᴹₑ (vs v) {Γ'ᴹ = Γ'ᴹ , _}  σ tᴹ = *∈ᴹₑ v σ tᴹ

Tyᴹₑ : ∀ {Γ'} A {Δ' Δ Σ' Σ σ' Γ'ᴹ}(σ : OPE {Σ'}{Δ'} σ' Σ Δ) → Tyᴹ {Γ'} A {Δ'}{Δ} Γ'ᴹ → Tyᴹ A (Con'ᴹₑ σ Γ'ᴹ)
Tyᴹₑ (var v) σ tᴹ = *∈ᴹₑ v σ tᴹ
Tyᴹₑ (A ⇒ B) σ tᴹ = λ δ aᴹ → coe (Tyᴹ B & {!!}) (tᴹ (σ ∘ₑ δ) (coe (Tyᴹ A & {!!}) aᴹ)) -- Con'ᴹ-∘ₑ
Tyᴹₑ (∀' A ) σ tᴹ = λ δ Bᴹ → coe {!!} (tᴹ (σ ∘ₑ δ) Bᴹ)                                -- Con'ᴹ-∘ₑ

data Conᴹ : ∀ {Γ'} → Con Γ' → ∀ {Δ'} Δ  → Con'ᴹ Γ' {Δ'} Δ → Set where
  ∙   : ∀ {Δ' Δ} → Conᴹ ∙ {Δ'} Δ ∙
  _,_ : ∀ {Γ' Γ Δ' Δ Γ'ᴹ}{A}         → Conᴹ {Γ'} Γ {Δ'} Δ Γ'ᴹ → Tyᴹ A Γ'ᴹ → Conᴹ (Γ , A) Δ Γ'ᴹ
  _,* : ∀ {Γ' Γ Δ' Δ Γ'ᴹ}{Aᴹ : *ᴹ Δ} → Conᴹ {Γ'} Γ {Δ'} Δ Γ'ᴹ → Conᴹ (Γ ,*) Δ (Γ'ᴹ , Aᴹ)

Conᴹₑ : ∀ {Γ' Γ Δ' Δ Γ'ᴹ Σ' Σ σ'} (σ : OPE {Σ'}{Δ'} σ' Σ Δ) → Conᴹ {Γ'} Γ {Δ'} Δ Γ'ᴹ → Conᴹ Γ Σ (Con'ᴹₑ σ Γ'ᴹ)
Conᴹₑ σ ∙                   = ∙
Conᴹₑ σ (_,_ {A = A} Γᴹ aᴹ) = Conᴹₑ σ Γᴹ , Tyᴹₑ A σ aᴹ
Conᴹₑ σ (Γᴹ ,*)             = Conᴹₑ σ Γᴹ ,*

OPE'ᴹ :  ∀ {Γ' Δ'} → OPE' Γ' Δ' → ∀ {Σ' Σ} → Con'ᴹ Γ' {Σ'} Σ → Con'ᴹ Δ' Σ
OPE'ᴹ ∙        Γ'ᴹ        = Γ'ᴹ
OPE'ᴹ (drop σ) (Γ'ᴹ , _ ) = OPE'ᴹ σ Γ'ᴹ
OPE'ᴹ (keep σ) (Γ'ᴹ , Aᴹ) = OPE'ᴹ σ Γ'ᴹ , Aᴹ

Sub'ᴹ :  ∀ {Γ' Δ'} → Sub' Γ' Δ' → ∀ {Σ' Σ} → Con'ᴹ Γ' {Σ'} Σ → Con'ᴹ Δ' Σ
Sub'ᴹ ∙       Γ'ᴹ = ∙
Sub'ᴹ (σ , A) Γ'ᴹ = Sub'ᴹ σ Γ'ᴹ , (λ δ → Tyᴹ A (Con'ᴹₑ δ Γ'ᴹ))

∈ᴹ : ∀ {Γ' Γ A} → _∈_ {Γ'} A Γ → ∀ {Δ' Δ}(Γ'ᴹ : Con'ᴹ Γ' {Δ'} Δ) → Conᴹ Γ Δ Γ'ᴹ → Tyᴹ A Γ'ᴹ
∈ᴹ vz      _ (Γᴹ , t) = t
∈ᴹ (vs v)  _ (Γᴹ , _) = ∈ᴹ v _ Γᴹ
∈ᴹ (vs* v) _ (Γᴹ ,* ) = coe {!!} (∈ᴹ v _ Γᴹ) -- Tyₑᴹ

Tmᴹ : ∀ {Γ' Γ A} → Tm {Γ'} Γ A → ∀ {Δ' Δ}(Γ'ᴹ : Con'ᴹ Γ' {Δ'} Δ) → Conᴹ Γ Δ Γ'ᴹ → Tyᴹ A Γ'ᴹ
Tmᴹ (var v)    Γ'ᴹ Γᴹ = ∈ᴹ v Γ'ᴹ Γᴹ
Tmᴹ (lam t)    Γ'ᴹ Γᴹ = λ σ aᴹ → Tmᴹ t (Con'ᴹₑ σ Γ'ᴹ) (Conᴹₑ σ Γᴹ , aᴹ)
Tmᴹ (app f x)  Γ'ᴹ Γᴹ = coe {!!} (Tmᴹ f Γ'ᴹ Γᴹ idₑ (coe {!!} (Tmᴹ x Γ'ᴹ Γᴹ))) -- Con'ᴹ-idₑ
Tmᴹ (tlam t)   Γ'ᴹ Γᴹ = λ σ Bᴹ → Tmᴹ t (Con'ᴹₑ σ Γ'ᴹ , Bᴹ) (Conᴹₑ σ Γᴹ ,*)
Tmᴹ (tapp t B) Γ'ᴹ Γᴹ = coe {!!} (Tmᴹ t Γ'ᴹ Γᴹ idₑ (λ δ → Tyᴹ B (Con'ᴹₑ δ Γ'ᴹ))) -- Tyₛᴹ

--------------------------------------------------------------------------------

-- quote/unquote for types!
--   probably need to make the Sub' Δ' Γ' in q/u unnecessariy

mutual
  q*∈ : ∀ {Γ'}(v : *∈ Γ') → ∀{Δ' Δ}(σ : Sub' Δ' Γ')(α : Con'ᴹ Γ' Δ) → *∈ᴹ v α → Nf Δ (*∈ₛ σ v)
  q*∈ vz     (σ , A) (α , *ᴹ) *∈ᴹ = {!!}
  q*∈ (vs v) (σ , _) (α , _ ) *∈ᴹ = q*∈ v σ α *∈ᴹ

  q : ∀ {Γ'}(A : Ty Γ') → ∀{Δ' Δ}(σ : Sub' Δ' Γ')(α : Con'ᴹ Γ' Δ) → Tyᴹ {Γ'} A α → Nf Δ (Tyₛ σ A)
  q (var v) σ α Aᴹ = q*∈ v σ α Aᴹ
  q (A ⇒ B) σ α Aᴹ =
    lam (q B σ (Con'ᴹₑ (drop idₑ) α) (Aᴹ (drop idₑ) (u A σ _ (var vz))))
  q {Γ'} (∀' A) {Δ'} {Δ} σ α Aᴹ = 
    tlam (q A (σ ₛ∘'ₑ drop id'ₑ , var vz) (Con'ᴹₑ (drop' idₑ) α , {!!}) (Aᴹ (drop' idₑ) {!!}))
    -- unquote *ᴹ

  u*∈ : ∀ {Γ'}(v : *∈ Γ') → ∀{Δ' Δ}(σ : Sub' Δ' Γ')(α : Con'ᴹ Γ' Δ) → Ne Δ (*∈ₛ σ v) → *∈ᴹ v α
  u*∈ vz     (σ , A) (α , *ᴹ) n = {!!}
  u*∈ (vs v) (σ , _) (α , _ ) n = u*∈ v σ α n

  u : ∀ {Γ'}(A : Ty Γ') → ∀{Δ' Δ}(σ : Sub' Δ' Γ')(α : Con'ᴹ Γ' Δ) → Ne Δ (Tyₛ σ A) → Tyᴹ {Γ'} A α
  u (var v) σ α n = u*∈ v σ α n
  u (A ⇒ B) σ α n {Σ'}{Σ}{δ'} δ aᴹ =
    u B (σ ₛ∘'ₑ δ') (Con'ᴹₑ δ α)
      (app (coe (Ne Σ & Ty-ₛ∘ₑ σ δ' (A ⇒ B)) (Neₑ δ n)) (q A (σ ₛ∘'ₑ δ') (Con'ᴹₑ δ α) aᴹ))
  u {Γ'} (∀' A) {Δ'} {Δ} σ α n {Σ'} {Σ} {δ'} δ Bᴹ =
    u A (σ ₛ∘'ₑ δ' , {!!}) (Con'ᴹₑ δ α , Bᴹ) (tapp (coe (Ne Σ & (∀' & {!!})) (Neₑ δ n)) {!!})
    -- quote *ᴹ



-- type sub -> term with subbed type ->

-- univ quote: ∀ {J}(σ : OPE(J, I)) → Aᴹ σ → Ne I (var (vz [ σ ]∈'ₑ))

-- mutual
--   qᴹ : ∀ {Γ' Γ Δ' Δ} A {Γ'ᴹ} → Tyᴹ {Γ'} A {Δ'}{Δ} Γ'ᴹ → Nf Γ A
--   qᴹ (var v) tᴹ = {!!}
--   qᴹ (A ⇒ B) tᴹ = lam  (qᴹ B (tᴹ (drop idₑ) (uᴹ A (var vz))))
--   qᴹ (∀' A)  tᴹ = tlam (qᴹ A (tᴹ (drop' idₑ) {!!}))
  
--   uᴹ : ∀ {Γ' Γ Δ' Δ} A {Γ'ᴹ} → Ne {Γ'} Γ A → Tyᴹ A {Δ'}{Δ} Γ'ᴹ
--   uᴹ (var v) n = {!!}
--   uᴹ {Γ'}{Γ}{Δ'}{Δ}(A ⇒ B) n {Σ'}{Σ} σ aᴹ = uᴹ {Γ'}   {Γ}    B (app {!n !} {!!})
--   uᴹ {Γ'}{Γ}{Δ'}{Δ}(∀' A)  n {Σ'}{Σ} σ Bᴹ = uᴹ {Γ' ,*}{Γ ,*} A {!!}



-- qᴹ {A = var vz} {Γ'ᴹ = Γ'ᴹ , Aᴹ} tᴹ = {!!}
-- qᴹ {A = var (vs v)} tᴹ = {!!}
-- qᴹ {A = A ⇒ B} tᴹ = {!!}
-- qᴹ {A = ∀' A}  tᴹ = {!!}

-- uᴹ : ∀ {Γ' Γ A Δ' Δ Γ'ᴹ} → Ne {Γ'} Γ A → Tyᴹ A {Δ'}{Δ} Γ'ᴹ
-- uᴹ {A = var vz} {Γ'ᴹ = Γ'ᴹ , Aᴹ} n = {!!}
-- uᴹ {A = var (vs v)} n = {!!}
-- uᴹ {A = A ⇒ B} {Γ'ᴹ = Γ'ᴹ} n σ aᴹ = uᴹ {Γ'ᴹ = Γ'ᴹ} {!_[_]ₙₑₑ n σ!}
-- uᴹ {A = ∀' A}  n σ Bᴹ = coe {!!} (uᴹ (tapp (n [ {!!} ]ₙₑₑ<) {!Bᴹ!}))


-- qᴹ : ∀ {Γ' A Δ' Δ Γ'ᴹ} → Tyᴹ {Γ'} A {Δ'}{Δ} Γ'ᴹ → Nf Δ (A [ {!!} ]')
-- qᴹ {A = var vz}     tᴹ = {!!}
-- qᴹ {A = var (vs v)} tᴹ = {!!}
-- qᴹ {A = A ⇒ B} tᴹ = {!!}
-- qᴹ {A = ∀' A}  tᴹ = {!!}





