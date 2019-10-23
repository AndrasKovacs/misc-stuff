{-# OPTIONS --without-K --postfix-projections #-}

module Syntax where

open import Lib

infixr 6 _∘'ₑ_
infixr 6 _ₑ∘'ₛ_ _ₛ∘'ₑ_ _∘'ₛ_
infixr 3 _⇒_
infixr 4 _,_

-- Type syntax
--------------------------------------------------------------------------------

data Con' : Set where
  ∙   : Con'
  _,* : Con' → Con'

data *∈ : Con' → Set where
  vz : ∀ {Γ} → *∈ (Γ ,*)
  vs : ∀ {Γ} → *∈ Γ → *∈ (Γ ,*)

data Ty (Γ : Con') : Set where
  var : *∈ Γ → Ty Γ
  _⇒_ : Ty Γ → Ty Γ → Ty Γ
  ∀'  : Ty (Γ ,*) → Ty Γ

-- Type embedding
--------------------------------------------------------------------------------

data OPE' : Con' → Con' → Set where
  ∙    : OPE' ∙ ∙
  drop : ∀ {Γ Δ} → OPE' Γ Δ → OPE' (Γ ,*) Δ
  keep : ∀ {Γ Δ} → OPE' Γ Δ → OPE' (Γ ,*) (Δ ,*)

id'ₑ : ∀ {Γ} → OPE' Γ Γ
id'ₑ {∙}    = ∙
id'ₑ {Γ ,*} = keep (id'ₑ {Γ})

wk' : ∀ {Γ} → OPE' (Γ ,*) Γ
wk' = drop id'ₑ

*∈ₑ : ∀ {Γ Δ} → OPE' Δ Γ → *∈ Γ → *∈ Δ
*∈ₑ ∙        v      = v
*∈ₑ (drop σ) v      = vs (*∈ₑ σ v)
*∈ₑ (keep σ) vz     = vz
*∈ₑ (keep σ) (vs v) = vs (*∈ₑ σ v)

Tyₑ : ∀ {Γ Δ} → OPE' Δ Γ → Ty Γ → Ty Δ
Tyₑ σ (var v) = var (*∈ₑ σ v)
Tyₑ σ (A ⇒ B) = Tyₑ σ A ⇒ Tyₑ σ B
Tyₑ σ (∀' A)  = ∀' (Tyₑ (keep σ) A)

_∘'ₑ_ : ∀ {Γ Δ Σ} → OPE' Δ Σ → OPE' Γ Δ → OPE' Γ Σ
σ      ∘'ₑ ∙      = σ
σ      ∘'ₑ drop δ = drop (σ ∘'ₑ δ)
drop σ ∘'ₑ keep δ = drop (σ ∘'ₑ δ)
keep σ ∘'ₑ keep δ = keep (σ ∘'ₑ δ)

ass'ₑ :
  ∀ {Γ Δ Σ Ξ}(σ : OPE' Σ Ξ)(δ : OPE' Δ Σ)(ν : OPE' Γ Δ)
  → (σ ∘'ₑ δ) ∘'ₑ ν ≡ σ ∘'ₑ (δ ∘'ₑ ν)
ass'ₑ σ        δ        ∙        = refl
ass'ₑ σ        δ        (drop ν) = drop & ass'ₑ σ δ ν
ass'ₑ σ        (drop δ) (keep ν) = drop & ass'ₑ σ δ ν
ass'ₑ (drop σ) (keep δ) (keep ν) = drop & ass'ₑ σ δ ν
ass'ₑ (keep σ) (keep δ) (keep ν) = keep & ass'ₑ σ δ ν

idr'ₑ : ∀ {Γ Δ}(σ : OPE' Γ Δ) → σ ∘'ₑ id'ₑ ≡ σ
idr'ₑ ∙        = refl
idr'ₑ (drop σ) = drop & idr'ₑ σ
idr'ₑ (keep σ) = keep & idr'ₑ σ

idl'ₑ : ∀ {Γ Δ}(σ : OPE' Γ Δ) → id'ₑ ∘'ₑ σ ≡ σ
idl'ₑ ∙        = refl
idl'ₑ (drop σ) = drop & idl'ₑ σ
idl'ₑ (keep σ) = keep & idl'ₑ σ

*∈-idₑ : ∀ {Γ}(v : *∈ Γ) → *∈ₑ id'ₑ v ≡ v
*∈-idₑ vz     = refl
*∈-idₑ (vs v) = vs & *∈-idₑ v

Ty-idₑ : ∀ {Γ}(A : Ty Γ) → Tyₑ id'ₑ A ≡ A
Ty-idₑ (var v) = var & *∈-idₑ v
Ty-idₑ (A ⇒ B) = _⇒_ & Ty-idₑ A ⊗ Ty-idₑ B
Ty-idₑ (∀' A)  = ∀' & Ty-idₑ A

*∈-∘ₑ : ∀ {Γ Δ Σ}(σ : OPE' Δ Σ)(δ : OPE' Γ Δ)(v : *∈ Σ) → *∈ₑ δ (*∈ₑ σ v) ≡ *∈ₑ (σ ∘'ₑ δ) v
*∈-∘ₑ ∙        ∙        ()
*∈-∘ₑ σ        (drop δ) v      = vs & *∈-∘ₑ σ δ v
*∈-∘ₑ (drop σ) (keep δ) v      = vs & *∈-∘ₑ σ δ v
*∈-∘ₑ (keep σ) (keep δ) vz     = refl
*∈-∘ₑ (keep σ) (keep δ) (vs v) = vs & *∈-∘ₑ σ δ v

Ty-∘ₑ : ∀ {Γ Δ Σ}(σ : OPE' Δ Σ)(δ : OPE' Γ Δ)(A : Ty Σ) → Tyₑ δ (Tyₑ σ A) ≡ Tyₑ (σ ∘'ₑ δ) A
Ty-∘ₑ σ δ (var v) = var & *∈-∘ₑ σ δ v
Ty-∘ₑ σ δ (A ⇒ B) = _⇒_ & Ty-∘ₑ σ δ A ⊗ Ty-∘ₑ σ δ B
Ty-∘ₑ σ δ (∀' A)  = ∀' & Ty-∘ₑ (keep σ) (keep δ) A

-- Type substitution
--------------------------------------------------------------------------------

data Sub' (Γ : Con') : Con' → Set where
  ∙   : Sub' Γ ∙
  _,_ : ∀ {Δ} → Sub' Γ Δ → Ty Γ → Sub' Γ (Δ ,*)

_ₛ∘'ₑ_ : ∀ {Γ Δ Σ} → Sub' Δ Σ → OPE' Γ Δ → Sub' Γ Σ
∙       ₛ∘'ₑ δ = ∙
(σ , A) ₛ∘'ₑ δ = (σ ₛ∘'ₑ δ) , Tyₑ δ A

_ₑ∘'ₛ_ : ∀ {Γ Δ Σ} → OPE' Δ Σ → Sub' Γ Δ → Sub' Γ Σ
∙      ₑ∘'ₛ δ       = δ
drop σ ₑ∘'ₛ (δ , A) = σ ₑ∘'ₛ δ
keep σ ₑ∘'ₛ (δ , A) = (σ ₑ∘'ₛ δ) , A

drop'ₛ : ∀ {Γ Δ} → Sub' Γ Δ → Sub' (Γ ,*) Δ
drop'ₛ σ = σ ₛ∘'ₑ wk'

keep'ₛ : ∀ {Γ Δ} → Sub' Γ Δ → Sub' (Γ ,*) (Δ ,*)
keep'ₛ σ = drop'ₛ σ , var vz

*∈ₛ : ∀ {Γ Δ} → Sub' Δ Γ → *∈ Γ → Ty Δ
*∈ₛ (σ , A) vz     = A
*∈ₛ (σ , _) (vs v) = *∈ₛ σ v

Tyₛ : ∀ {Γ Δ} → Sub' Δ Γ → Ty Γ → Ty Δ
Tyₛ σ (var v) = *∈ₛ σ v
Tyₛ σ (A ⇒ B) = Tyₛ σ A ⇒ Tyₛ σ B
Tyₛ σ (∀' A)  = ∀' (Tyₛ (keep'ₛ σ) A)

id'ₛ : ∀ {Γ} → Sub' Γ Γ
id'ₛ {∙}    = ∙
id'ₛ {Γ ,*} = keep'ₛ id'ₛ

ass'ₛₑₑ :
  ∀ {Γ Δ Σ Ξ}(σ : Sub' Σ Ξ)(δ : OPE' Δ Σ)(ν : OPE' Γ Δ)
  → (σ ₛ∘'ₑ δ) ₛ∘'ₑ ν ≡ σ ₛ∘'ₑ (δ ∘'ₑ ν)
ass'ₛₑₑ ∙       δ ν = refl
ass'ₛₑₑ (σ , A) δ ν = _,_ & ass'ₛₑₑ σ δ ν ⊗ Ty-∘ₑ δ ν A

ass'ₑₛₑ :
  ∀ {Γ Δ Σ Ξ}(σ : OPE' Σ Ξ)(δ : Sub' Δ Σ)(ν : OPE' Γ Δ)
  → (σ ₑ∘'ₛ δ) ₛ∘'ₑ ν ≡ σ ₑ∘'ₛ (δ ₛ∘'ₑ ν)
ass'ₑₛₑ ∙        δ       ν = refl
ass'ₑₛₑ (drop σ) (δ , A) ν = ass'ₑₛₑ σ δ ν
ass'ₑₛₑ (keep σ) (δ , A) ν = (_, Tyₑ ν A) & ass'ₑₛₑ σ δ ν

*∈-ₑ∘ₛ : ∀ {Γ Δ Σ}(σ : OPE' Δ Σ)(δ : Sub' Γ Δ)(v : *∈ Σ) → *∈ₛ δ (*∈ₑ σ v) ≡ *∈ₛ (σ ₑ∘'ₛ δ) v
*∈-ₑ∘ₛ ∙        δ       ()
*∈-ₑ∘ₛ (drop σ) (δ , A) v      = *∈-ₑ∘ₛ σ δ v
*∈-ₑ∘ₛ (keep σ) (δ , A) vz     = refl
*∈-ₑ∘ₛ (keep σ) (δ , A) (vs v) = *∈-ₑ∘ₛ σ δ v

Ty-ₑ∘ₛ :
  ∀ {Γ Δ Σ}(σ : OPE' Δ Σ)(δ : Sub' Γ Δ)(A : Ty Σ)
  → Tyₛ δ (Tyₑ σ A) ≡ Tyₛ (σ ₑ∘'ₛ δ) A
Ty-ₑ∘ₛ σ δ (var v) = *∈-ₑ∘ₛ σ δ v
Ty-ₑ∘ₛ σ δ (A ⇒ B) = _⇒_ & Ty-ₑ∘ₛ σ δ A ⊗ Ty-ₑ∘ₛ σ δ B
Ty-ₑ∘ₛ σ δ (∀' A)  = ∀' & (Ty-ₑ∘ₛ (keep σ) (keep'ₛ δ) A
                        ◾ (λ x → Tyₛ (x , var vz) A) & (ass'ₑₛₑ σ δ wk' ⁻¹))

*∈-ₛ∘ₑ : ∀ {Γ Δ Σ}(σ : Sub' Δ Σ)(δ : OPE' Γ Δ)(v : *∈ Σ) → Tyₑ δ (*∈ₛ σ v) ≡ *∈ₛ (σ ₛ∘'ₑ δ) v
*∈-ₛ∘ₑ (σ , A) δ vz     = refl
*∈-ₛ∘ₑ (σ , A) δ (vs v) = *∈-ₛ∘ₑ σ δ v

Ty-ₛ∘ₑ : ∀ {Γ Δ Σ}(σ : Sub' Δ Σ)(δ : OPE' Γ Δ)(A : Ty Σ) → Tyₑ δ (Tyₛ σ A) ≡ Tyₛ (σ ₛ∘'ₑ δ) A
Ty-ₛ∘ₑ σ δ (var v) = *∈-ₛ∘ₑ σ δ v
Ty-ₛ∘ₑ σ δ (A ⇒ B) = _⇒_ & Ty-ₛ∘ₑ σ δ A ⊗ Ty-ₛ∘ₑ σ δ B
Ty-ₛ∘ₑ σ δ (∀' A)  =
  ∀' & (Ty-ₛ∘ₑ (keep'ₛ σ) (keep δ) A
     ◾ (λ x → Tyₛ (x , var vz) A) &
         (ass'ₛₑₑ σ wk' (keep δ)
       ◾ (σ ₛ∘'ₑ_) & (drop & idl'ₑ δ)
       ◾ (σ ₛ∘'ₑ_) & (drop & (idr'ₑ δ ⁻¹))
       ◾ ass'ₛₑₑ σ δ wk' ⁻¹))

idr'ₛₑ : ∀ {Γ Δ}(σ : Sub' Δ Γ) → σ ₛ∘'ₑ id'ₑ ≡ σ
idr'ₛₑ ∙       = refl
idr'ₛₑ (σ , A) = _,_ & idr'ₛₑ σ ⊗ Ty-idₑ A

*∈-idₛ : ∀ {Γ}(v : *∈ Γ) → *∈ₛ id'ₛ v ≡ var v
*∈-idₛ vz     = refl
*∈-idₛ (vs v) = *∈-ₛ∘ₑ id'ₛ wk' v ⁻¹
              ◾ Tyₑ wk' & *∈-idₛ v
              ◾ var & (vs & *∈-idₑ v)

Ty-idₛ : ∀ {Γ} A → Tyₛ {Γ} id'ₛ A ≡ A
Ty-idₛ (var v) = *∈-idₛ v
Ty-idₛ (A ⇒ B) = _⇒_ & Ty-idₛ A ⊗ Ty-idₛ B
Ty-idₛ (∀' A)  = ∀' & Ty-idₛ A

emb'ₑ : ∀ {Γ Δ} → OPE' Γ Δ → Sub' Γ Δ
emb'ₑ ∙        = ∙
emb'ₑ (drop σ) = drop'ₛ (emb'ₑ σ)
emb'ₑ (keep σ) = keep'ₛ (emb'ₑ σ)

idr'ₑₛ : ∀ {Γ Δ}(σ : OPE' Γ Δ) → σ ₑ∘'ₛ id'ₛ ≡ emb'ₑ σ
idr'ₑₛ ∙        = refl
idr'ₑₛ (drop σ) = ass'ₑₛₑ σ id'ₛ wk' ⁻¹ ◾ (_ₛ∘'ₑ wk') & idr'ₑₛ σ
idr'ₑₛ (keep σ) = _,_ & (ass'ₑₛₑ σ id'ₛ wk' ⁻¹ ◾ (_ₛ∘'ₑ wk') & idr'ₑₛ σ) ⊗ refl

idl'ₛₑ : ∀ {Γ Δ}(σ : OPE' Γ Δ) → id'ₛ ₛ∘'ₑ σ ≡ emb'ₑ σ
idl'ₛₑ ∙        = refl
idl'ₛₑ (drop σ) =
    (λ x → id'ₛ ₛ∘'ₑ drop x) & (idr'ₑ σ ⁻¹)
  ◾ ass'ₛₑₑ id'ₛ σ wk' ⁻¹
  ◾ (_ₛ∘'ₑ wk') & idl'ₛₑ σ
idl'ₛₑ (keep σ) =
  (_, var vz) & (ass'ₛₑₑ id'ₛ wk' (keep σ)
  ◾ (λ x → id'ₛ ₛ∘'ₑ drop x) & (idl'ₑ σ ◾ idr'ₑ σ ⁻¹)
  ◾ ass'ₛₑₑ id'ₛ σ wk' ⁻¹
  ◾ (_ₛ∘'ₑ wk') & idl'ₛₑ σ)

_∘'ₛ_ : ∀ {Γ Δ Σ} → Sub' Δ Σ → Sub' Γ Δ → Sub' Γ Σ
∙       ∘'ₛ δ = ∙
(σ , A) ∘'ₛ δ = (σ ∘'ₛ δ) , Tyₛ δ A

ass'ₛₑₛ :
  ∀ {Γ Δ Σ Ξ}(σ : Sub' Σ Ξ)(δ : OPE' Δ Σ)(ν : Sub' Γ Δ)
  → (σ ₛ∘'ₑ δ) ∘'ₛ ν ≡ σ ∘'ₛ (δ ₑ∘'ₛ ν)
ass'ₛₑₛ ∙       δ ν = refl
ass'ₛₑₛ (σ , A) δ ν = _,_ & ass'ₛₑₛ σ δ ν ⊗ Ty-ₑ∘ₛ δ ν A

ass'ₛₛₑ :
  ∀ {Γ Δ Σ Ξ}(σ : Sub' Σ Ξ)(δ : Sub' Δ Σ)(ν : OPE' Γ Δ)
  → (σ ∘'ₛ δ) ₛ∘'ₑ ν ≡ σ ∘'ₛ (δ ₛ∘'ₑ ν)
ass'ₛₛₑ ∙       δ ν = refl
ass'ₛₛₑ (σ , A) δ ν = _,_ & ass'ₛₛₑ σ δ ν ⊗ Ty-ₛ∘ₑ δ ν A

idl'ₑₛ : ∀ {Γ Δ}(σ : Sub' Γ Δ) → id'ₑ ₑ∘'ₛ σ ≡ σ
idl'ₑₛ ∙       = refl
idl'ₑₛ (σ , A) = _,_ & idl'ₑₛ σ ⊗ refl

*∈-∘ₛ : ∀ {Γ Δ Σ}(σ : Sub' Δ Σ)(δ : Sub' Γ Δ) v → Tyₛ δ (*∈ₛ σ v) ≡ *∈ₛ (σ ∘'ₛ δ) v
*∈-∘ₛ (σ , A) δ vz     = refl
*∈-∘ₛ (σ , A) δ (vs v) = *∈-∘ₛ σ δ v

Ty-∘ₛ : ∀ {Γ Δ Σ}(σ : Sub' Δ Σ)(δ : Sub' Γ Δ) A → Tyₛ δ (Tyₛ σ A) ≡ Tyₛ (σ ∘'ₛ δ) A
Ty-∘ₛ σ δ (var v) = *∈-∘ₛ σ δ v
Ty-∘ₛ σ δ (A ⇒ B) = _⇒_ & Ty-∘ₛ σ δ A ⊗ Ty-∘ₛ σ δ B
Ty-∘ₛ σ δ (∀' A)  = ∀' & (Ty-∘ₛ (keep'ₛ σ) (keep'ₛ δ) A
                    ◾ (λ x → Tyₛ (x , var vz) A) & (ass'ₛₑₛ σ wk' (keep'ₛ δ)
                    ◾ (σ ∘'ₛ_) & idl'ₑₛ (drop'ₛ δ)
                    ◾ ass'ₛₛₑ σ δ wk' ⁻¹))

*∈-emb : ∀ {Γ Δ}(σ : OPE' Γ Δ) v → *∈ₛ (emb'ₑ σ) v ≡ var (*∈ₑ σ v)
*∈-emb ∙ ()
*∈-emb (drop σ) v =
    *∈-ₛ∘ₑ (emb'ₑ σ) wk' v ⁻¹
  ◾ Tyₑ wk' & *∈-emb σ v
  ◾ var & (vs & *∈-idₑ (*∈ₑ σ v))
*∈-emb (keep σ) vz     = refl
*∈-emb (keep σ) (vs v) =
    *∈-ₛ∘ₑ (emb'ₑ σ) wk' v ⁻¹
  ◾ Tyₑ wk' & *∈-emb σ v
  ◾ var & (vs & *∈-idₑ (*∈ₑ σ v))

Ty-emb : ∀ {Γ Δ}(σ : OPE' Γ Δ) A → Tyₛ (emb'ₑ σ) A ≡ Tyₑ σ A
Ty-emb σ (var v) = *∈-emb σ v
Ty-emb σ (A ⇒ B) = _⇒_ & Ty-emb σ A ⊗ Ty-emb σ B
Ty-emb σ (∀' A)  = ∀' & Ty-emb (keep σ) A

emb'-∘ₛ : ∀ {Γ Δ Σ}(σ : Sub' Δ Σ)(δ : OPE' Γ Δ) → σ ∘'ₛ emb'ₑ δ ≡ σ ₛ∘'ₑ δ
emb'-∘ₛ ∙       δ = refl
emb'-∘ₛ (σ , A) δ = _,_ & emb'-∘ₛ σ δ ⊗ Ty-emb δ A

idl'ₛ : ∀ {Γ Δ}(σ : Sub' Γ Δ) → id'ₛ ∘'ₛ σ ≡ σ
idl'ₛ ∙       = refl
idl'ₛ (σ , A) = (_, A) & (ass'ₛₑₛ id'ₛ wk' (σ , A)
                       ◾ (id'ₛ ∘'ₛ_) & idl'ₑₛ σ ◾ idl'ₛ σ)

-- Terms
--------------------------------------------------------------------------------

data Con : Con' → Set where
  ∙    : Con ∙
  _,_  : ∀ {Γ'} → Con Γ' → Ty Γ' → Con Γ'
  _,*  : ∀ {Γ'} → Con Γ' → Con (Γ' ,*)

infix 3 _∈_
data _∈_ : ∀ {Δ} (A : Ty Δ) → Con Δ → Set where
  vz  : ∀ {Δ}{A : Ty Δ}{Γ}   → A ∈ (Γ , A)
  vs  : ∀ {Δ}{A : Ty Δ}{B Γ} → A ∈ Γ → A ∈ (Γ , B)
  vs* : ∀ {Δ}{A : Ty Δ}{Γ}   → A ∈ Γ → Tyₑ wk' A ∈ (Γ ,*)

data Tm {Δ} (Γ : Con Δ) : Ty Δ → Set where
  var  : ∀ {A} → A ∈ Γ → Tm Γ A
  lam  : ∀ {A B} → Tm (Γ , A) B → Tm Γ (A ⇒ B)
  app  : ∀ {A B} → Tm Γ (A ⇒ B) → Tm Γ A → Tm Γ B
  tlam : ∀ {A} → Tm (Γ ,*) A → Tm Γ (∀' A)
  tapp : ∀ {A} → Tm Γ (∀' A) → (B : Ty Δ) → Tm Γ (Tyₛ (id'ₛ , B) A)
