
{-# OPTIONS --without-K --type-in-type #-}

module PShNormalization where

open import Lib
open import Syntax

record Cand {Γ'} Γ A : Set where
  constructor con
  field
    S : Set
    Q : S → Nf {Γ'} Γ A
    U : Ne Γ A → S
open Cand

-- todo: pack (*ᴹ A) functor laws in
*ᴹ : ∀ {Γ'} → Ty Γ' → Set
*ᴹ {Γ'} A = ∀ {Δ'} Δ σ' → Cand {Δ'} Δ (Tyₑ σ' A)

*ᴹₑ : ∀ {Γ' Δ' A}(σ' : OPE' Δ' Γ') → *ᴹ {Γ'} A → *ᴹ {Δ'} (Tyₑ σ' A)
*ᴹₑ {Γ'}{Δ'}{A} σ' f {Σ'} Σ δ' = coe (Cand Σ & (Ty-∘ₑ σ' δ' A ⁻¹)) (f Σ (σ' ∘'ₑ δ'))

data Con'ᴹ : (Γ' : Con') → ∀ {Δ'} → Sub' Δ' Γ' → Set where
  ∙   : ∀ {Δ'} → Con'ᴹ ∙ {Δ'} ∙
  _,_ : ∀ {Γ' Δ' σ A} → Con'ᴹ Γ' {Δ'} σ → *ᴹ A → Con'ᴹ (Γ' ,*) (σ , A)

Con'ᴹₑ : ∀ {Γ' Δ' σ' Σ'} δ' → Con'ᴹ Γ' {Δ'} σ' → Con'ᴹ Γ' {Σ'} (σ' ₛ∘'ₑ δ')
Con'ᴹₑ δ' ∙          = ∙
Con'ᴹₑ δ' (σ'ᴹ , Aᴹ) = Con'ᴹₑ δ' σ'ᴹ , *ᴹₑ δ' Aᴹ

u* : ∀ {Γ'}(v : *∈ Γ') → *ᴹ {Γ'} (var v)
u* {Γ'} v {Δ'} Δ σ' = con (Ne Δ (var (*∈ₑ σ' v))) ne (λ n → n)

*∈ᴹ : ∀ {Γ'}(v : *∈ Γ') → ∀ {Δ'} Δ (σ : Sub' Δ' Γ')(σᴹ : Con'ᴹ Γ' σ) → Cand Δ (*∈ₛ σ v)
*∈ᴹ vz     Δ (σ , A) (σᴹ , Aᴹ) = coe (Cand Δ & Ty-idₑ A) (Aᴹ Δ id'ₑ)
*∈ᴹ (vs v) Δ (σ , _) (σᴹ , _) = *∈ᴹ v Δ σ σᴹ

Tyᴹ : ∀ {Γ'}(A : Ty Γ') → ∀ {Δ'} Δ (σ' : Sub' Δ' Γ')(σ'ᴹ : Con'ᴹ Γ' σ') → Cand Δ (Tyₛ σ' A)
Tyᴹ (var v) σ' σ'ᴹ = *∈ᴹ v σ' σ'ᴹ

Tyᴹ {Γ'} (A ⇒ B) {Δ'} Δ σ' σ'ᴹ = con

  (∀ {Σ' Σ δ'}(δ : OPE {Σ'}{Δ'} δ' Σ Δ) → Tyᴹ A Σ _ (Con'ᴹₑ δ' σ'ᴹ) .S → Tyᴹ B Σ _ (Con'ᴹₑ δ' σ'ᴹ) .S)

  (λ fᴹ → lam
    (coe ((λ x → Nf (Δ , Tyₛ x A) (Tyₛ x B)) & idr'ₛₑ σ')
      (Tyᴹ B _ _ (Con'ᴹₑ id'ₑ σ'ᴹ) .Q
      (fᴹ (drop idₑ) (Tyᴹ A _ _ (Con'ᴹₑ id'ₑ σ'ᴹ) .U (var vz))))))

  (λ n {Σ'}{Σ}{δ'} δ aᴹ → let σ'ᴹ' = Con'ᴹₑ δ' σ'ᴹ in
    Tyᴹ B _ _ σ'ᴹ' .U (app (coe (Ne Σ & Ty-ₛ∘ₑ σ' δ' (A ⇒ B)) (Neₑ δ n)) (Tyᴹ A _ _ σ'ᴹ' .Q aᴹ)))

Tyᴹ {Γ'} (∀' A) {Δ'} Δ σ' σ'ᴹ = con
  (∀ {Σ' Σ δ'}(δ : OPE {Σ'}{Δ'} δ' Σ Δ) (B : Ty Σ')(Bᴹ : *ᴹ B) → Tyᴹ A Σ _ (Con'ᴹₑ δ' σ'ᴹ , Bᴹ) .S)

  (λ fᴹ →
    tlam (Tyᴹ A _ _ (Con'ᴹₑ (drop id'ₑ) σ'ᴹ , u* vz) .Q (fᴹ (drop' idₑ) _ (u* vz))))

  (λ n {Σ'}{Σ}{δ'} δ B Bᴹ →
    Tyᴹ A _ _ (Con'ᴹₑ δ' σ'ᴹ , Bᴹ) .U
      (coe
          (Ne Σ & (Ty-ₑ∘ₛ (keep δ') (id'ₛ , B) (Tyₛ (keep'ₛ σ') A)
        ◾ Ty-∘ₛ (keep'ₛ σ') ((δ' ₑ∘'ₛ id'ₛ) , B) A
        ◾ (λ x → Tyₛ (x , B) A) &
            (ass'ₛₑₛ σ' (drop id'ₑ) ((δ' ₑ∘'ₛ id'ₛ) , B)
           ◾ ((λ x → σ' ∘'ₛ id'ₑ ₑ∘'ₛ x) & idr'ₑₛ δ')
           ◾ (σ' ∘'ₛ_) & idl'ₑₛ (emb'ₑ δ')
           ◾ emb'-∘ₛ σ' δ')))
      (tappₙₑ (Neₑ δ n) B)))

*∈ᴹₑ :
  ∀ {Γ' v Δ' Δ σ' σ'ᴹ Σ' Σ δ'}(δ : OPE {Σ'}{Δ'} δ' Σ Δ)
  → *∈ᴹ {Γ'} v Δ σ' σ'ᴹ .S → *∈ᴹ v Σ _ (Con'ᴹₑ δ' σ'ᴹ) .S
*∈ᴹₑ {v = vz {Γ'}}{Δ'}{Δ}{σ' , A}{σ'ᴹ , x} {Σ'} {Σ} {δ'} δ aᴹ = {!!} -- *ᴹ A functor
*∈ᴹₑ {v = vs v}{σ'ᴹ = σ'ᴹ , x} δ aᴹ = *∈ᴹₑ{v = v}{σ'ᴹ = σ'ᴹ} δ aᴹ

Tyᴹₑ :
  ∀ {Γ' A Δ' Δ σ' σ'ᴹ Σ' Σ δ'}(δ : OPE {Σ'}{Δ'} δ' Σ Δ)
  → Tyᴹ {Γ'} A Δ σ' σ'ᴹ .S → Tyᴹ A Σ _ (Con'ᴹₑ δ' σ'ᴹ) .S
Tyᴹₑ {A = var v} δ aᴹ = *∈ᴹₑ {v = v} δ aᴹ

Tyᴹₑ {A = A ⇒ B} {σ' = σ'} {σ'ᴹ} {δ' = δ'} δ tᴹ {Ξ'} {Ξ} {ν'} ν aᴹ =
  coe (apd2' (λ x y → Tyᴹ B Ξ x y .S) (ass'ₛₑₑ σ' δ' ν' ⁻¹) {!!}) -- Con'ᴹ-∘ₑ
    (tᴹ (δ ∘ₑ ν)
    (coe (apd2' (λ x y → Tyᴹ A Ξ x y .S) (ass'ₛₑₑ σ' δ' ν') {!!}) -- Con'ᴹ-∘ₑ
      aᴹ))

Tyᴹₑ {A = ∀' A } {σ' = σ'} {σ'ᴹ} {δ' = δ'} δ tᴹ {Ξ'} {Ξ} {ν'} ν B Bᴹ =
  coe (apd2' (λ x y → Tyᴹ A Ξ (x , B) (y , Bᴹ) .S) (ass'ₛₑₑ σ' δ' ν' ⁻¹) {!!}) -- Con'ᴹ-∘ₑ
    (tᴹ (δ ∘ₑ ν) B Bᴹ)

data Conᴹ : ∀ {Γ'} → Con Γ' → ∀ {Δ'} (Δ : Con Δ'){σ'} → Con'ᴹ Γ' {Δ'} σ' → Set where
  ∙   : ∀ {Δ' Δ} → Conᴹ ∙ {Δ'} Δ ∙
  _,_ : ∀ {Γ' Γ Δ' Δ σ' σ'ᴹ A} → Conᴹ {Γ'} Γ {Δ'} Δ {σ'} σ'ᴹ → Tyᴹ A Δ σ' σ'ᴹ .S → Conᴹ (Γ , A) Δ σ'ᴹ
  _,* : ∀ {Γ' Γ Δ' Δ σ' σ'ᴹ A}{Aᴹ : *ᴹ A} → Conᴹ {Γ'} Γ {Δ'} Δ {σ'} σ'ᴹ → Conᴹ (Γ ,*) Δ (σ'ᴹ , Aᴹ)

Conᴹₑ :
  ∀ {Γ' Γ Δ' Δ σ' σ'ᴹ Σ' Σ δ'}(δ : OPE {Σ'}{Δ'} δ' Σ Δ) → Conᴹ {Γ'} Γ Δ {σ'} σ'ᴹ → Conᴹ Γ Σ (Con'ᴹₑ δ' σ'ᴹ)
Conᴹₑ δ ∙ = ∙
Conᴹₑ δ (_,_ {A = A} Γᴹ tᴹ) = Conᴹₑ δ Γᴹ , Tyᴹₑ {A = A} δ tᴹ
Conᴹₑ δ (Γᴹ ,*) = Conᴹₑ δ Γᴹ ,*

∈ᴹ : ∀ {Γ' Γ A} → _∈_ {Γ'} A Γ → ∀ {Δ' Δ σ'} σ'ᴹ → Conᴹ Γ Δ σ'ᴹ → Tyᴹ {Γ'} A {Δ'} Δ σ' σ'ᴹ .S
∈ᴹ vz       σ'ᴹ      (Γᴹ , t) = t
∈ᴹ (vs v)   σ'ᴹ      (Γᴹ , t) = ∈ᴹ v σ'ᴹ Γᴹ
∈ᴹ (vs* v) (σ'ᴹ , _) (Γᴹ ,* ) = coe {!!} (∈ᴹ v σ'ᴹ Γᴹ) -- Tyₑᴹ

Tmᴹ : ∀ {Γ' Γ A} → Tm {Γ'} Γ A → ∀ {Δ' Δ σ'} σ'ᴹ → Conᴹ Γ Δ σ'ᴹ → Tyᴹ {Γ'} A {Δ'} Δ σ' σ'ᴹ .S
Tmᴹ (var v)    σ'ᴹ Γᴹ = ∈ᴹ v σ'ᴹ Γᴹ
Tmᴹ (lam t)    σ'ᴹ Γᴹ = λ δ aᴹ → Tmᴹ t _ (Conᴹₑ δ Γᴹ , aᴹ)

Tmᴹ {A = B} (app {A} f x) {Δ = Δ} {σ'} σ'ᴹ Γᴹ =
  coe (apd2' (λ x₁ y → Tyᴹ B Δ x₁ y .S) (idr'ₛₑ σ' ) {!!}) -- Ty-idₑᴹ
    (Tmᴹ f σ'ᴹ Γᴹ idₑ
      (coe (apd2' (λ x₁ y → Tyᴹ A Δ x₁ y .S) (idr'ₛₑ σ' ⁻¹) {!!}) -- Ty-idₑᴹ
      (Tmᴹ x σ'ᴹ Γᴹ)))

Tmᴹ (tlam t)   σ'ᴹ Γᴹ = λ δ B Bᴹ → Tmᴹ t (_ , Bᴹ) (Conᴹₑ δ Γᴹ ,*)

Tmᴹ (tapp {A} t B) {Δ = Δ} {σ'} σ'ᴹ Γᴹ =
  coe {!!}  -- Tyₛᴹ
    (Tmᴹ t σ'ᴹ Γᴹ idₑ (Tyₛ σ' B)
    (λ {Σ'} Σ δ' → coe (Cand Σ & (Ty-ₛ∘ₑ σ' δ' B ⁻¹)) (Tyᴹ B Σ (σ' ₛ∘'ₑ δ') (Con'ᴹₑ δ' σ'ᴹ))))

--------------------------------------------------------------------------------

uCon' : ∀ (Γ' : Con') → Con'ᴹ Γ' {Γ'} id'ₛ
uCon' ∙       = ∙
uCon' (Γ' ,*) = Con'ᴹₑ (drop id'ₑ) (uCon' Γ') , u* vz

uCon : ∀ Γ' Γ → Conᴹ {Γ'} Γ Γ (uCon' Γ')
uCon ∙      ∙       = ∙
uCon Γ'     (Γ , A) =

  coe (apd2' (λ x y → Conᴹ Γ (Γ , A) {x} y) (idr'ₛₑ id'ₛ) {!!}) -- Ty-idₑᴹ
    (Conᴹₑ (drop {A = A} idₑ) (uCon Γ' Γ)) ,
  Tyᴹ A (Γ , A) id'ₛ (uCon' Γ') .U (coe (Ne (Γ , A) & (Ty-idₛ A ⁻¹)) (var vz))

uCon (Γ' ,*) (Γ ,*)  = Conᴹₑ (drop' idₑ) (uCon Γ' Γ) ,*

nf : ∀ {Γ' A Γ} → Tm {Γ'} Γ A → Nf Γ A
nf {Γ'}{A}{Γ} t = coe (Nf Γ & Ty-idₛ A) (Tyᴹ A Γ _ (uCon' Γ') .Q (Tmᴹ t _ (uCon Γ' Γ)))

