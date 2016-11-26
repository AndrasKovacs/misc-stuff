{-# OPTIONS --without-K #-}

module Syntax where

{-
- Type syntax + substitution calculus
- Term syntax + substitution calculus
- Normal forms + renamings
-}

open import Lib

infixr 6 _ᵣ∘'ₛ_ _ₛ∘'ᵣ_ _∘'ᵣ_ _∘ᵣ_
infixl 8 _[_]' _[_]∈' _[_]'ᵣ _[_]∈'ᵣ _[_]∈ᵣ _[_]ᵣ
infixl 5 _,_
infixr 3 _⇒_
infix 3 _∈_


-- Type syntax
--------------------------------------------------------------------------------

data Con' : Set where
  ∙   : Con'
  _,* : Con' → Con'

data *∈ : Con' → Set where
  vz : ∀ {Δ} → *∈ (Δ ,*)
  vs : ∀ {Δ} → *∈ Δ → *∈ (Δ ,*)

data Ty (Δ : Con') : Set where
  var : *∈ Δ → Ty Δ
  _⇒_ : Ty Δ → Ty Δ → Ty Δ
  ∀'  : Ty (Δ ,*) → Ty Δ

-- Type renaming
--------------------------------------------------------------------------------

data Ren' : Con' → Con' → Set where
  ∙    : Ren' ∙ ∙
  drop : ∀ {Γ Δ} → Ren' Γ Δ → Ren' (Γ ,*) Δ
  keep : ∀ {Γ Δ} → Ren' Γ Δ → Ren' (Γ ,*) (Δ ,*)

id'ᵣ : ∀ {Γ} → Ren' Γ Γ
id'ᵣ {∙}    = ∙
id'ᵣ {Γ ,*} = keep (id'ᵣ {Γ})

wk' : ∀ {Γ} → Ren' (Γ ,*) Γ
wk' = drop id'ᵣ

_[_]∈'ᵣ : ∀ {Γ Δ} → *∈ Γ → Ren' Δ Γ → *∈ Δ
()   [ ∙      ]∈'ᵣ
v    [ drop σ ]∈'ᵣ = vs (v [ σ ]∈'ᵣ)
vz   [ keep σ ]∈'ᵣ = vz
vs v [ keep σ ]∈'ᵣ = vs (v [ σ ]∈'ᵣ)

_[_]'ᵣ : ∀ {Γ Δ} → Ty Γ → Ren' Δ Γ → Ty Δ
var v   [ σ ]'ᵣ = var (v [ σ ]∈'ᵣ)
(A ⇒ B) [ σ ]'ᵣ = (A [ σ ]'ᵣ) ⇒ (B [ σ ]'ᵣ)
∀' A    [ σ ]'ᵣ = ∀' (A [ keep σ ]'ᵣ)

_∘'ᵣ_ : ∀ {Γ Δ Σ} → Ren' Δ Σ → Ren' Γ Δ → Ren' Γ Σ
σ      ∘'ᵣ ∙      = σ
σ      ∘'ᵣ drop δ = drop (σ ∘'ᵣ δ)
drop σ ∘'ᵣ keep δ = drop (σ ∘'ᵣ δ)
keep σ ∘'ᵣ keep δ = keep (σ ∘'ᵣ δ)

ass'ᵣ :
  ∀ {Γ Δ Σ Ξ}(σ : Ren' Σ Ξ)(δ : Ren' Δ Σ)(ν : Ren' Γ Δ)
  → (σ ∘'ᵣ δ) ∘'ᵣ ν ≡ σ ∘'ᵣ (δ ∘'ᵣ ν)
ass'ᵣ σ        δ        ∙        = refl
ass'ᵣ σ        δ        (drop ν) = drop & ass'ᵣ σ δ ν
ass'ᵣ σ        (drop δ) (keep ν) = drop & ass'ᵣ σ δ ν
ass'ᵣ (drop σ) (keep δ) (keep ν) = drop & ass'ᵣ σ δ ν
ass'ᵣ (keep σ) (keep δ) (keep ν) = keep & ass'ᵣ σ δ ν

idr'ᵣ : ∀ {Γ Δ}(σ : Ren' Γ Δ) → σ ∘'ᵣ id'ᵣ ≡ σ
idr'ᵣ ∙        = refl
idr'ᵣ (drop σ) = drop & idr'ᵣ σ
idr'ᵣ (keep σ) = keep & idr'ᵣ σ

idl'ᵣ : ∀ {Γ Δ}(σ : Ren' Γ Δ) → id'ᵣ ∘'ᵣ σ ≡ σ
idl'ᵣ ∙        = refl
idl'ᵣ (drop σ) = drop & idl'ᵣ σ
idl'ᵣ (keep σ) = keep & idl'ᵣ σ

id[]∈'ᵣ : ∀ {Γ}(v : *∈ Γ) → v [ id'ᵣ ]∈'ᵣ ≡ v
id[]∈'ᵣ vz     = refl
id[]∈'ᵣ (vs v) = vs & id[]∈'ᵣ v

id[]'ᵣ : ∀ {Γ}(A : Ty Γ) → A [ id'ᵣ ]'ᵣ ≡ A
id[]'ᵣ (var v) = var & id[]∈'ᵣ v
id[]'ᵣ (A ⇒ B) = _⇒_ & id[]'ᵣ A ⊗ id[]'ᵣ B
id[]'ᵣ (∀' A)  = ∀' & id[]'ᵣ A

[][]∈'ᵣ :
  ∀ {Γ Δ Σ}(v : *∈ Σ)(σ : Ren' Δ Σ)(δ : Ren' Γ Δ)
  →  v [ σ ]∈'ᵣ [ δ ]∈'ᵣ ≡ v [ σ ∘'ᵣ δ ]∈'ᵣ
[][]∈'ᵣ ()     ∙        ∙
[][]∈'ᵣ v      σ        (drop δ)  = vs & [][]∈'ᵣ v σ δ
[][]∈'ᵣ v      (drop σ) (keep δ)  = vs & [][]∈'ᵣ v σ δ
[][]∈'ᵣ vz     (keep σ) (keep δ)  = refl
[][]∈'ᵣ (vs v) (keep σ) (keep δ)  = vs & [][]∈'ᵣ v σ δ

[][]'ᵣ :
  ∀ {Γ Δ Σ}(A : Ty Σ)(σ : Ren' Δ Σ)(δ : Ren' Γ Δ)
  →  A [ σ ]'ᵣ [ δ ]'ᵣ ≡ A [ σ ∘'ᵣ δ ]'ᵣ
[][]'ᵣ (var v) σ δ = var & [][]∈'ᵣ v σ δ
[][]'ᵣ (A ⇒ B) σ δ = _⇒_ & [][]'ᵣ A σ δ ⊗ [][]'ᵣ B σ δ
[][]'ᵣ (∀' A)  σ δ = ∀' & [][]'ᵣ  A (keep σ) (keep δ)

-- Type substitution
--------------------------------------------------------------------------------

data Sub' (Γ : Con') : Con' → Set where
  ∙   : Sub' Γ ∙
  _,_ : ∀ {Δ} → Sub' Γ Δ → Ty Γ → Sub' Γ (Δ ,*)

_ₛ∘'ᵣ_ : ∀ {Γ Δ Σ} → Sub' Δ Σ → Ren' Γ Δ → Sub' Γ Σ
∙       ₛ∘'ᵣ δ = ∙
(σ , t) ₛ∘'ᵣ δ = (σ ₛ∘'ᵣ δ) , (t [ δ ]'ᵣ)

_ᵣ∘'ₛ_ : ∀ {Γ Δ Σ} → Ren' Δ Σ → Sub' Γ Δ → Sub' Γ Σ
∙      ᵣ∘'ₛ δ       = δ
drop σ ᵣ∘'ₛ (δ , t) = σ ᵣ∘'ₛ δ
keep σ ᵣ∘'ₛ (δ , t) = σ ᵣ∘'ₛ δ , t

drop'ₛ : ∀ {Γ Δ} → Sub' Γ Δ → Sub' (Γ ,*) Δ
drop'ₛ σ = σ ₛ∘'ᵣ wk'

keep'ₛ : ∀ {Γ Δ} → Sub' Γ Δ → Sub' (Γ ,*) (Δ ,*)
keep'ₛ σ = drop'ₛ σ , var vz

_[_]∈' : ∀ {Γ Δ} → *∈ Γ → Sub' Δ Γ → Ty Δ
vz   [ σ , A ]∈' = A
vs v [ σ , A ]∈' = v [ σ ]∈'

_[_]' : ∀ {Γ Δ} → Ty Γ → Sub' Δ Γ → Ty Δ
var v   [ σ ]' = v [ σ ]∈'
(A ⇒ B) [ σ ]' = (A [ σ ]') ⇒ (B [ σ ]')
∀' A    [ σ ]' = ∀' (A [ keep'ₛ σ ]')

id'ₛ : ∀ {Γ} → Sub' Γ Γ
id'ₛ {∙}    = ∙
id'ₛ {Γ ,*} = keep'ₛ id'ₛ

ass'ₛᵣᵣ :
  ∀ {Γ Δ Σ Ξ}(σ : Sub' Σ Ξ)(δ : Ren' Δ Σ)(ν : Ren' Γ Δ)
  → (σ ₛ∘'ᵣ δ) ₛ∘'ᵣ ν ≡ σ ₛ∘'ᵣ (δ ∘'ᵣ ν)
ass'ₛᵣᵣ ∙       δ ν = refl
ass'ₛᵣᵣ (σ , A) δ ν = _,_ & ass'ₛᵣᵣ σ δ ν ⊗ [][]'ᵣ A δ ν

ass'ᵣₛᵣ :
  ∀ {Γ Δ Σ Ξ}(σ : Ren' Σ Ξ)(δ : Sub' Δ Σ)(ν : Ren' Γ Δ)
  → (σ ᵣ∘'ₛ δ) ₛ∘'ᵣ ν ≡ σ ᵣ∘'ₛ (δ ₛ∘'ᵣ ν)
ass'ᵣₛᵣ ∙        δ       ν = refl
ass'ᵣₛᵣ (drop σ) (δ , A) ν = ass'ᵣₛᵣ σ δ ν
ass'ᵣₛᵣ (keep σ) (δ , A) ν = (_, A [ ν ]'ᵣ) & ass'ᵣₛᵣ σ δ ν

[][]∈'ᵣₛ :
  ∀ {Γ Δ Σ}(v : *∈ Σ)(σ : Ren' Δ Σ)(δ : Sub' Γ Δ)
  → v [ σ ]∈'ᵣ [ δ ]∈' ≡ v [ σ ᵣ∘'ₛ δ ]∈'
[][]∈'ᵣₛ ()      ∙       _
[][]∈'ᵣₛ v      (drop σ) (δ , A) = [][]∈'ᵣₛ v σ δ
[][]∈'ᵣₛ vz     (keep σ) (δ , A) = refl
[][]∈'ᵣₛ (vs v) (keep σ) (δ , A) = [][]∈'ᵣₛ v σ δ

[][]'ᵣₛ :
  ∀ {Γ Δ Σ}(A : Ty Σ)(σ : Ren' Δ Σ)(δ : Sub' Γ Δ)
  → A [ σ ]'ᵣ [ δ ]' ≡ A [ σ ᵣ∘'ₛ δ ]'
[][]'ᵣₛ (var v) σ δ = [][]∈'ᵣₛ v σ δ
[][]'ᵣₛ (A ⇒ B) σ δ = _⇒_ & [][]'ᵣₛ A σ δ ⊗ [][]'ᵣₛ B σ δ
[][]'ᵣₛ (∀' A)  σ δ =
    ∀' & ([][]'ᵣₛ A (keep σ) (keep'ₛ δ)
  ◾ (A [_]') & ((_, var vz) & (ass'ᵣₛᵣ σ δ wk' ⁻¹)))

[][]∈'ₛᵣ :
  ∀ {Γ Δ Σ}(v : *∈ Σ)(σ : Sub' Δ Σ)(δ : Ren' Γ Δ)
  → v [ σ ]∈' [ δ ]'ᵣ ≡ v [ σ ₛ∘'ᵣ δ ]∈'
[][]∈'ₛᵣ vz     (σ , _) δ = refl
[][]∈'ₛᵣ (vs v) (σ , _) δ = [][]∈'ₛᵣ v σ δ

[][]'ₛᵣ :
  ∀ {Γ Δ Σ}(A : Ty Σ)(σ : Sub' Δ Σ)(δ : Ren' Γ Δ)
  → A [ σ ]' [ δ ]'ᵣ ≡ A [ σ ₛ∘'ᵣ δ ]'
[][]'ₛᵣ (var v) σ δ = [][]∈'ₛᵣ v σ δ
[][]'ₛᵣ (A ⇒ B) σ δ = _⇒_ & [][]'ₛᵣ A σ δ ⊗ [][]'ₛᵣ B σ δ
[][]'ₛᵣ (∀' A)  σ δ =
    ∀' & ([][]'ₛᵣ A (keep'ₛ σ) (keep δ)
    ◾ (A [_]') & ((_, var vz) & (
        ass'ₛᵣᵣ σ wk' (keep δ)
      ◾ (σ ₛ∘'ᵣ_) & (drop & (idl'ᵣ δ ◾ idr'ᵣ δ ⁻¹))
      ◾ ass'ₛᵣᵣ σ δ wk' ⁻¹)))

emb'ᵣ : ∀ {Γ Δ} → Ren' Γ Δ → Sub' Γ Δ
emb'ᵣ ∙        = ∙
emb'ᵣ (drop σ) = drop'ₛ (emb'ᵣ σ)
emb'ᵣ (keep σ) = keep'ₛ (emb'ᵣ σ)

idr'ᵣₛ : ∀ {Γ Δ}(σ : Ren' Γ Δ) → σ ᵣ∘'ₛ id'ₛ ≡ emb'ᵣ σ
idr'ᵣₛ ∙        = refl
idr'ᵣₛ (drop σ) = ass'ᵣₛᵣ σ id'ₛ wk' ⁻¹ ◾ (_ₛ∘'ᵣ wk') & idr'ᵣₛ σ
idr'ᵣₛ (keep σ) = (_, var vz) & (ass'ᵣₛᵣ σ id'ₛ wk' ⁻¹ ◾ (_ₛ∘'ᵣ wk') & idr'ᵣₛ σ)

idl'ₛᵣ : ∀ {Γ Δ}(σ : Ren' Γ Δ) → id'ₛ ₛ∘'ᵣ σ ≡ emb'ᵣ σ
idl'ₛᵣ ∙        = refl
idl'ₛᵣ (drop σ) =
    (λ x → id'ₛ ₛ∘'ᵣ drop x) & (idr'ᵣ σ ⁻¹)
  ◾ ass'ₛᵣᵣ id'ₛ σ wk' ⁻¹
  ◾ (_ₛ∘'ᵣ wk') & idl'ₛᵣ σ
idl'ₛᵣ (keep σ) =
  (_, var vz) & (ass'ₛᵣᵣ id'ₛ wk' (keep σ)
  ◾ (λ x → id'ₛ ₛ∘'ᵣ drop x) & (idl'ᵣ σ ◾ idr'ᵣ σ ⁻¹)
  ◾ ass'ₛᵣᵣ id'ₛ σ wk' ⁻¹
  ◾ (_ₛ∘'ᵣ wk') & idl'ₛᵣ σ)

-- Term syntax
--------------------------------------------------------------------------------

data Con : Con' → Set where
  ∙    : Con ∙
  _,_  : ∀ {Δ} → Con Δ → Ty Δ → Con Δ
  _,*  : ∀ {Δ} → Con Δ → Con (Δ ,*)

data _∈_ : ∀ {Δ} (A : Ty Δ) → Con Δ → Set where
  vz  : ∀ {Δ}{A : Ty Δ}{Γ}   → A ∈ (Γ , A)
  vs  : ∀ {Δ}{A : Ty Δ}{B Γ} → A ∈ Γ → A ∈ (Γ , B)
  vs* : ∀ {Δ}{A : Ty Δ}{Γ}   → A ∈ Γ → A [ wk' ]'ᵣ ∈ (Γ ,*)

data Tm {Δ} (Γ : Con Δ) : Ty Δ → Set where
  var  : ∀ {A} → A ∈ Γ → Tm Γ A
  lam  : ∀ {A B} → Tm (Γ , A) B → Tm Γ (A ⇒ B)
  app  : ∀ {A B} → Tm Γ (A ⇒ B) → Tm Γ A → Tm Γ B
  tlam : ∀ {A} → Tm (Γ ,*) A → Tm Γ (∀' A)
  tapp : ∀ {A} → Tm Γ (∀' A) → (B : Ty Δ) → Tm Γ (A [ id'ₛ , B  ]')

-- Term renaming
--------------------------------------------------------------------------------

data Ren : ∀ {Γ Δ} → Ren' Γ Δ → Con Γ → Con Δ → Set where
  ∙     : Ren ∙ ∙ ∙
  drop' : ∀ {Γ Δ σ δ ν}   → Ren {Γ}{Δ} σ δ ν → Ren (drop σ) (δ ,*)          ν
  keep' : ∀ {Γ Δ σ δ ν}   → Ren {Γ}{Δ} σ δ ν → Ren (keep σ) (δ ,*)          (ν ,*)
  drop  : ∀ {Γ Δ σ δ ν A} → Ren {Γ}{Δ} σ δ ν → Ren σ        (δ , A)         ν
  keep  : ∀ {Γ Δ σ δ ν A} → Ren {Γ}{Δ} σ δ ν → Ren σ        (δ , A [ σ ]'ᵣ) (ν , A)

Ren'-of : ∀ {Γ' Δ' σ' Γ Δ} → Ren {Γ'}{Δ'} σ' Γ Δ → Ren' Γ' Δ'
Ren'-of {σ' = σ'} _ = σ'

Con'-of : ∀ {Γ} → Con Γ → Con'
Con'-of {Γ} _ = Γ

keepₜ : ∀ {Γ Δ σ δ ν A} → Ren {Γ}{Δ} σ δ ν → Ren σ (δ , A [ σ ]'ᵣ) (ν , A)
keepₜ = keep

idᵣ : ∀ {Γ'}{Γ : Con Γ'} → Ren id'ᵣ Γ Γ
idᵣ {∙}     {∙}     = ∙
idᵣ {∙}     {Γ , A} =
  coe ((λ x → Ren ∙ (Γ , x) (Γ , A)) & id[]'ᵣ A) (keepₜ idᵣ)
idᵣ {Γ' ,*} {Γ , A} =
  coe ((λ x → Ren id'ᵣ (Γ , x) (Γ , A)) & id[]'ᵣ A) (keepₜ idᵣ)
idᵣ {Γ' ,*} {Γ ,*}  = keep' (idᵣ {Γ'}{Γ})

_[_]∈ᵣ : ∀ {Γ' Δ'}{σ' : Ren' Γ' Δ'}{Γ Δ A} → A ∈ Δ → Ren σ' Γ Δ → (A [ σ' ]'ᵣ) ∈ Γ
_[_]∈ᵣ {A = A} v (drop' {σ = σ} {δ} ν) =
  coe
      ((_∈ (δ ,*)) & ([][]'ᵣ A σ wk'
    ◾ ((A [_]'ᵣ) ∘ drop) & idr'ᵣ σ))
  (vs* (v [ ν ]∈ᵣ))

vs* {A = A} v [ keep' {σ = σ} {δ} ν ]∈ᵣ =
  coe
      ((_∈ (δ ,*)) & ([][]'ᵣ A σ wk'
    ◾ ((A [_]'ᵣ) ∘ drop) & (idr'ᵣ σ ◾ idl'ᵣ σ ⁻¹)
    ◾ [][]'ᵣ A wk' (keep σ) ⁻¹))
  (vs* (v [ ν ]∈ᵣ))

()    [ ∙       ]∈ᵣ
v     [ drop σ  ]∈ᵣ = vs (v [ σ ]∈ᵣ)
vz    [ keep σ  ]∈ᵣ = vz
vs v  [ keep σ  ]∈ᵣ = vs (v [ σ ]∈ᵣ)

_[_]ᵣ : ∀ {Γ' Δ'}{σ' : Ren' Γ' Δ'}{Γ Δ A} → Tm Δ A → Ren σ' Γ Δ → Tm Γ (A [ σ' ]'ᵣ)
var v    [ σ ]ᵣ = var (v [ σ ]∈ᵣ)
lam t    [ σ ]ᵣ = lam (t [ keep σ ]ᵣ)
app f a  [ σ ]ᵣ = app (f [ σ ]ᵣ) (a [ σ ]ᵣ)
tlam t   [ σ ]ᵣ = tlam (t [ keep' σ ]ᵣ)
_[_]ᵣ {σ' = σ'} {Γ} (tapp {A} t B) σ =
  coe
      (Tm Γ & ([][]'ᵣₛ A (keep σ') (id'ₛ , B [ σ' ]'ᵣ)
    ◾ (λ x → A [ x , B [ σ' ]'ᵣ ]') & (idr'ᵣₛ σ' ◾ idl'ₛᵣ σ' ⁻¹)
    ◾ [][]'ₛᵣ A (id'ₛ , B) σ' ⁻¹))
  (tapp (t [ σ ]ᵣ) (B [ Ren'-of σ ]'ᵣ))

_∘ᵣ_ :
  ∀ {Γ' Δ' Σ' σ' δ' Γ Δ Σ} → Ren {Δ'}{Σ'} σ' Δ Σ → Ren {Γ'}{Δ'} δ' Γ Δ
  → Ren (σ' ∘'ᵣ δ') Γ Σ
σ       ∘ᵣ ∙       = σ
σ       ∘ᵣ drop' δ = drop' (σ ∘ᵣ δ)
σ       ∘ᵣ drop  δ = drop  (σ ∘ᵣ δ)
drop' σ ∘ᵣ keep' δ = drop' (σ ∘ᵣ δ)
keep' σ ∘ᵣ keep' δ = keep' (σ ∘ᵣ δ)
drop  σ ∘ᵣ keep  δ = drop  (σ ∘ᵣ δ)
_∘ᵣ_ {σ' = σ'} {δ'} (keep {ν = ν} {A} σ) (keep {δ = δ₁} δ₂) = 
  coe ((λ x → Ren (σ' ∘'ᵣ δ') (δ₁ , x) (ν , A)) & ([][]'ᵣ A σ' δ' ⁻¹))
  (keepₜ {A = A} (σ ∘ᵣ δ₂))

-- Normal forms
--------------------------------------------------------------------------------

mutual
  data Nf {Γ} (Δ : Con Γ) : Ty Γ → Set where
    lam  : ∀ {A B} → Nf (Δ , A) B → Nf Δ (A ⇒ B)
    tlam : ∀ {A} → Nf (Δ ,*) A → Nf Δ (∀' A)
    ne   : ∀ {v} → Ne Δ (var v) → Nf Δ (var v)

  data Ne {Γ}(Δ : Con Γ) : Ty Γ → Set where
    var  : ∀ {A} → A ∈ Δ → Ne Δ A
    app  : ∀ {A B} → Ne Δ (A ⇒ B) → Nf Δ A → Ne Δ B
    tapp : ∀ {A} → Ne Δ (∀' A) → (B : Ty Γ) → Ne Δ (A [ id'ₛ , B ]')

tappₙₑ : ∀ {Γ}{Δ : Con Γ}{A} → Ne Δ (∀' A) → (B : Ty Γ) → Ne Δ (A [ id'ₛ , B ]')
tappₙₑ = tapp
    
mutual
  _[_]ₙᵣ : ∀ {Γ' Δ'}{σ' : Ren' Γ' Δ'}{Γ Δ A} → Nf Δ A → Ren σ' Γ Δ → Nf Γ (A [ σ' ]'ᵣ)
  lam t    [ σ ]ₙᵣ = lam (t [ keep σ ]ₙᵣ)
  tlam t   [ σ ]ₙᵣ = tlam (t [ keep' σ ]ₙᵣ)
  ne   n   [ σ ]ₙᵣ = ne (n [ σ ]ₙₑᵣ)

  _[_]ₙₑᵣ : ∀ {Γ' Δ'}{σ' : Ren' Γ' Δ'}{Γ Δ A} → Ne Δ A → Ren σ' Γ Δ → Ne Γ (A [ σ' ]'ᵣ)
  var v    [ σ ]ₙₑᵣ = var (v [ σ ]∈ᵣ)
  app f a  [ σ ]ₙₑᵣ = app (f [ σ ]ₙₑᵣ) (a [ σ ]ₙᵣ)
  _[_]ₙₑᵣ {σ' = σ'} {Γ} (tapp {A} t B) σ =
    coe
        (Ne Γ & ([][]'ᵣₛ A (keep σ') (id'ₛ , B [ σ' ]'ᵣ)
      ◾ (λ x → A [ x , B [ σ' ]'ᵣ ]') & (idr'ᵣₛ σ' ◾ idl'ₛᵣ σ' ⁻¹)
      ◾ [][]'ₛᵣ A (id'ₛ , B) σ' ⁻¹))
    (tappₙₑ (t [ σ ]ₙₑᵣ) (B [ Ren'-of σ ]'ᵣ))

-- Term substitution
---------------------------------------------------------------------------------



