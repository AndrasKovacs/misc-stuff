
{-# OPTIONS --without-K #-}

open import Level renaming (zero to lzero; suc to lsuc)
open import Data.Nat
open import Function
open import Data.Unit.Base
open import Data.Product
open import Relation.Binary.PropositionalEquality
open import Data.Sum hiding (map)
open import Data.Empty
open import Relation.Nullary

infix 6 _⁻¹
infixr 5 _◾_
infixl 6 _▷'_
infixr 5 _∷_
infixl 9 _&_

J : ∀ {α} {A : Set α} {x : A} (P : {y : A} → x ≡ y → Set) → P refl → ∀ {y}(p : x ≡ y) → P p
J P pr refl = pr

postulate
  ext : ∀ {α β} → Extensionality α β
  LEM : ∀ {α}(A : Set α) → A ⊎ ¬ A

coe : ∀ {α}{A B : Set α} → A ≡ B → A → B
coe refl a = a
_&_ = cong
_◾_ = trans
_⁻¹ = sym
π₁  = proj₁
π₂  = proj₂
ᴷ   = const
Λ   = curry
V   = uncurry

{-# DISPLAY proj₁ = π₁ #-}
{-# DISPLAY proj₂ = π₂ #-}
{-# DISPLAY trans = _◾_ #-}
{-# DISPLAY sym   = _⁻¹ #-}
{-# DISPLAY cong  = _&_ #-}

--------------------------------------------------------------------------------

mutual
  data U' : Set where
    Π' : (A : U') → (ElU A → U') → U'
    ⊤' : U'

  ElU : U' → Set
  ElU (Π' A B) = (a : ElU A) → ElU (B a)
  ElU ⊤'       = ⊤

mutual
  data Set' : Set where
    U'' : Set'
    El' : U' → Set'

  ElS : Set' → Set
  ElS U''     = U'
  ElS (El' A) = ElU A

mutual
  Ty' = λ Γ → ElC Γ → Set'
  
  data Con' : Set where
    ∙'   : Con'
    _▷'_ : (Γ : Con') → Ty' Γ → Con'

  ElC : Con' → Set
  ElC ∙'       = ⊤
  ElC (Γ ▷' A) = Σ (ElC Γ) (ElS ∘ A)

--------------------------------------------------------------------------------

Var' = λ Γ (A : Ty' Γ) → (α : ElC Γ) → ElS (A α)
Tm'  = λ Γ (A : Ty' Γ) → (α : ElC Γ) → ElS (A α)

data Var : (Γ : Con') → Ty' Γ → Set
data Tm  : (Γ : Con') → Ty' Γ → Set

⟦_⟧ᵛ     : ∀ {Γ A} → Var Γ A → Var' Γ A
⟦_⟧      : ∀ {Γ A} → Tm Γ A → Tm' Γ A

data Var where
  vz : ∀ {Γ A} → Var (Γ ▷' A) (A ∘ π₁)
  vs : ∀ {Γ A B} → Var Γ A → Var (Γ ▷' B) (A ∘ π₁)

data Tm where
  var  : ∀ {Γ A} → Var Γ A → Tm Γ A
  app  : ∀ {Γ A B} → Tm Γ (El' ∘ (Π' ∘ A ˢ B)) → (a : Tm Γ (El' ∘ A)) → Tm Γ (El' ∘ (B ˢ ⟦ a ⟧))
  lam  : ∀ {Γ A B} → Tm (Γ ▷' (El' ∘ A)) (El' ∘ B) → Tm Γ (El' ∘ (Π' ∘ A ˢ Λ B))
  Π    : ∀ {Γ}(A : Tm Γ (ᴷ U'')) → Tm (Γ ▷' (El' ∘ ⟦ A ⟧)) (ᴷ U'') → Tm Γ (ᴷ U'')
  unit : ∀ {Γ} → Tm Γ (ᴷ U'')
  tt   : ∀ {Γ} → Tm Γ (ᴷ (El' ⊤'))

⟦ vz      ⟧ᵛ = π₂
⟦ vs v    ⟧ᵛ = ⟦ v ⟧ᵛ ∘ π₁
⟦ var x   ⟧  = ⟦ x ⟧ᵛ
⟦ app t u ⟧  = ⟦ t ⟧ ˢ ⟦ u ⟧
⟦ lam t   ⟧  = Λ ⟦ t ⟧
⟦ Π A B   ⟧  = Π' ∘ ⟦ A ⟧ ˢ Λ ⟦ B ⟧
⟦ unit    ⟧  = ᴷ ⊤'
⟦ tt      ⟧  = ᴷ tt

--------------------------------------------------------------------------------

data Nf : (Γ : Con') → Ty' Γ → Set
data Sp : (Γ : Con') → Ty' Γ → Ty' Γ → Set
⟦_⟧ₙ    : ∀ {Γ A} → Nf Γ A → Tm' Γ A

data Nf where
  lam  : ∀ {Γ A B} → Nf (Γ ▷' (El' ∘ A)) (El' ∘ V B) → Nf Γ (λ x → El' (Π' (A x) (B x)))
  Π    : ∀ {Γ}(A : Nf Γ (ᴷ U'')) → Nf (Γ ▷' (El' ∘ ⟦ A ⟧ₙ)) (ᴷ U'') → Nf Γ (ᴷ U'')  
  unit : ∀ {Γ} → Nf Γ (ᴷ U'')
  tt   : ∀ {Γ} → Nf Γ (ᴷ (El' ⊤'))
  ne   : ∀ {Γ A B} → Var Γ A → Sp Γ A B → Nf Γ B

data Sp where
  ∙   : ∀ {Γ A} → Sp Γ A A
  _∷_ : ∀ {Γ A B C}(a : Nf Γ (El' ∘ A)) → Sp Γ (El' ∘ (B ˢ ⟦ a ⟧ₙ)) C → Sp Γ (λ x → El' (Π' (A x) (B x))) C

appSp' : ∀ {Γ A B} → Tm' Γ A → Sp Γ A B → Tm' Γ B
appSp' t ∙        = t
appSp' t (a ∷ sp) = appSp' (t ˢ ⟦ a ⟧ₙ) sp

⟦ lam t   ⟧ₙ  = Λ ⟦ t ⟧ₙ
⟦ Π A B   ⟧ₙ  = Π' ∘ ⟦ A ⟧ₙ ˢ Λ ⟦ B ⟧ₙ
⟦ unit    ⟧ₙ  = ᴷ ⊤'
⟦ tt      ⟧ₙ  = ᴷ tt
⟦ ne x sp ⟧ₙ  = appSp' ⟦ x ⟧ᵛ sp

--------------------------------------------------------------------------------

OPE' = λ (Γ Δ : Con') → ElC Γ → ElC Δ

mutual
  data OPE : Con' → Con' → Set where
    ∙    : OPE ∙' ∙'
    drop : ∀ {Γ Δ A} → OPE Γ Δ → OPE (Γ ▷' A) Δ
    keep : ∀ {Γ Δ A} (σ : OPE Γ Δ) → OPE (Γ ▷' A ∘ ⟦ σ ⟧ᵉ) (Δ ▷' A)

  ⟦_⟧ᵉ : ∀ {Γ Δ} → OPE Γ Δ → OPE' Γ Δ
  ⟦ ∙      ⟧ᵉ = id
  ⟦ drop σ ⟧ᵉ = ⟦ σ ⟧ᵉ ∘ π₁
  ⟦ keep σ ⟧ᵉ = map ⟦ σ ⟧ᵉ id

Varₑ : ∀ {Γ Δ A}(σ : OPE Γ Δ) → Var Δ A → Var Γ (A ∘ ⟦ σ ⟧ᵉ)
Varₑ ∙        x      = x
Varₑ (drop σ) x      = vs (Varₑ σ x)
Varₑ (keep σ) vz     = vz
Varₑ (keep σ) (vs x) = vs (Varₑ σ x)

⟦Varₑ⟧ : ∀ {Γ Δ A}(σ : OPE Γ Δ)(x : Var Δ A) → ⟦ Varₑ σ x ⟧ᵛ ≡ ⟦ x ⟧ᵛ ∘ ⟦ σ ⟧ᵉ
⟦Varₑ⟧ ∙        x      = refl
⟦Varₑ⟧ (drop σ) x      = (_∘ π₁) & ⟦Varₑ⟧ σ x
⟦Varₑ⟧ (keep σ) vz     = refl
⟦Varₑ⟧ (keep σ) (vs x) = (_∘ π₁) & ⟦Varₑ⟧ σ x

Nfₑ   : ∀ {Γ Δ A}(σ : OPE Γ Δ) → Nf Δ A → Nf Γ (A ∘ ⟦ σ ⟧ᵉ)
⟦Nfₑ⟧ : ∀ {Γ Δ A}(σ : OPE Γ Δ)(t : Nf Δ A) → ⟦ Nfₑ σ t ⟧ₙ ≡ ⟦ t ⟧ₙ ∘ ⟦ σ ⟧ᵉ
Spₑ   : ∀ {Γ Δ A B}(σ : OPE Γ Δ) → Sp Δ A B → Sp Γ (A ∘ ⟦ σ ⟧ᵉ) (B ∘ ⟦ σ ⟧ᵉ)

Spₑ σ ∙ = ∙
Spₑ {Γ} {B = B₁} σ (_∷_ {B = B} a sp) =
  Nfₑ σ a ∷
    coe 
      ((λ y → Sp Γ (λ x → El' (B (⟦ σ ⟧ᵉ x) (y x)))
        (λ x → B₁ (⟦ σ ⟧ᵉ x))) & ⟦Nfₑ⟧ σ a ⁻¹)
      (Spₑ σ sp)

Nfₑ σ (lam t) = lam (Nfₑ (keep σ) t)
Nfₑ {Γ} σ (Π A B) =
  Π (Nfₑ σ A)
    (coe ((λ y → Nf (Γ ▷' (λ x → El' (y x))) (λ x → U'')) & ⟦Nfₑ⟧ σ A ⁻¹)
      (Nfₑ (keep σ) B))
Nfₑ σ unit = unit
Nfₑ σ tt = tt
Nfₑ σ (ne x sp) = ne (Varₑ σ x) (Spₑ σ sp)

⟦Nfₑ⟧ σ (lam t) = Λ & ⟦Nfₑ⟧ (keep σ) t
⟦Nfₑ⟧ σ (Π A B) = {!!}
⟦Nfₑ⟧ σ unit = refl
⟦Nfₑ⟧ σ tt = refl
⟦Nfₑ⟧ σ (ne x sp) = {!!}

idₑ : ∀ {Γ} → OPE Γ Γ
⟦idₑ⟧ : ∀ {Γ} → ⟦ idₑ{Γ} ⟧ᵉ ≡ id
idₑ   {∙'}     = ∙
idₑ   {Γ ▷' A} = coe ((λ y → OPE (Γ ▷' (A ∘ y)) (Γ ▷' A)) & ⟦idₑ⟧ {Γ}) (keep{Γ}{Γ}{A} idₑ)
⟦idₑ⟧ {∙'}     = refl
⟦idₑ⟧ {Γ ▷' A} = 
  J (λ {f} p → ⟦ coe ((λ y → OPE (Γ ▷' (λ x → A (y x))) (Γ ▷' A)) & p) (keep idₑ) ⟧ᵉ
                ≡ map f id)
     refl
     (⟦idₑ⟧ {Γ})

wk : ∀ {Γ A} → OPE (Γ ▷' A) Γ
wk = drop idₑ

wkNf : ∀ {Γ A B} → Nf Γ A → Nf (Γ ▷' B) (A ∘ π₁)
wkNf {Γ}{A}{B} t =
  coe ((λ y → Nf (Γ ▷' B) (λ x → A (y (π₁ x)))) & ⟦idₑ⟧)
      (Nfₑ (drop {Γ}{Γ}{B} idₑ) t)

--------------------------------------------------------------------------------

split : ∀ {Γ A} → Var Γ A → Con'
split (vz {Γ}) = Γ
split (vs x)   = split x

splitᵗ' : ∀ {Γ A}(x : Var Γ A) → Ty' (split x)
splitᵗ' (vz {A = A}) = A
splitᵗ' (vs x)       = splitᵗ' x

Sub' = λ (Γ Δ : Con') → ElC Γ → ElC Δ

mutual
  instᶜ : ∀ {Γ A}(x : Var Γ A) → Tm' (split x) (splitᵗ' x) → Con'
  instᶜ {Γ ▷' A} {_} vz     t = Γ
  instᶜ {Γ ▷' B} {.(A ∘ π₁)} (vs {_}{A}{.B} x) t = instᶜ x t ▷' B ∘ instˢ' x t

  instˢ' : ∀ {Γ A}(x : Var Γ A)(t : Tm' (split x) (splitᵗ' x)) → Sub' (instᶜ x t) Γ
  instˢ' vz     t = λ α → α , t α
  instˢ' (vs x) t = map (instˢ' x t) id

instᵛ :
  ∀ {Γ A B}(x : Var Γ A)(t' : Nf (split x) (splitᵗ' x))
  → Var Γ B
  → Var (instᶜ x ⟦ t' ⟧ₙ) (B ∘ instˢ' x ⟦ t' ⟧ₙ)
  ⊎ Nf  (instᶜ x ⟦ t' ⟧ₙ) (B ∘ instˢ' x ⟦ t' ⟧ₙ)
instᵛ vz     t' vz      = inj₂ t'
instᵛ vz     t' (vs x') = inj₁ x'
instᵛ (vs x) t' vz      = inj₁ vz
instᵛ (vs x) t' (vs x') with instᵛ x t' x'
... | inj₁ x'' = inj₁ (vs x'')
... | inj₂ t'' = inj₂ (wkNf t'')

snocSp :
  ∀ {Γ A B C} → Sp Γ A (λ x → El' (Π' (B x) (C x)))  → (b : Nf Γ (El' ∘ B))
  → Sp Γ A (El' ∘ (C ˢ ⟦ b ⟧ₙ))
snocSp ∙        b = b ∷ ∙
snocSp (a ∷ sp) b = a ∷ snocSp sp b

⊥→-unique : ∀ {α β}{A : Set α}{B : A → Set β} → ¬ A → (f g : ∀ a → B a) → f ≡ g
⊥→-unique ¬A f g = ext (⊥-elim ∘ ¬A)

El'-inj : ∀ {a b} → El' a ≡ El' b → a ≡ b
El'-inj refl = refl

Π'-inj : ∀ {A A' B B'} → Π' A B ≡ Π' A' B' → Σ (A ≡ A') λ q → coe ((λ x → ElU x → U') & q) B ≡ B'
Π'-inj refl = refl , refl

mutual
  {-# TERMINATING #-}
  inst : 
    ∀ {Γ A B}
      (x : Var Γ A)(t' : Nf (split x) (splitᵗ' x))
      → Nf Γ B → Nf (instᶜ x ⟦ t' ⟧ₙ) (B ∘ instˢ' x ⟦ t' ⟧ₙ)
  inst x t' (lam t) = lam (inst (vs x) t' t) -- !
  inst x t' (Π A B) = Π (inst x t' A) (coe {!!} (inst (vs x) t' B))
  inst x t' unit = unit
  inst x t' tt = tt
  inst x t' (ne x' sp) with instᵛ x t' x'
  ... | inj₁ x'' = ne x'' (instSp x t' sp)
  ... | inj₂ t'' = appSp t'' (instSp x t' sp)

  instSp :
    ∀ {Γ A B C}(x : Var Γ A)(t' : Nf (split x) (splitᵗ' x))
    → Sp Γ B C
    → Sp (instᶜ x ⟦ t' ⟧ₙ) (B ∘ instˢ' x ⟦ t' ⟧ₙ) (C ∘ instˢ' x ⟦ t' ⟧ₙ) 
  instSp x t' ∙        = ∙
  instSp x t' (t ∷ sp) = inst x t' t ∷ coe {!!} (instSp x t' sp)

  appSp :
    ∀ {Γ A B} → Nf Γ A → Sp Γ A B → Nf Γ B
  appSp t ∙        = t
  appSp t (a ∷ sp) = appSp (nfApp refl t a) sp

  -- no injectivity for Π' !
  nfApp :
    ∀ {Γ A B C} → C ≡ (λ x → El' (Π' (A x) (B x))) → Nf Γ C  → (a : Nf Γ (El' ∘ A))
    → Nf Γ (El' ∘ (B ˢ ⟦ a ⟧ₙ))
  nfApp {Γ} {A} {B} eq (lam {A = A'} {B'} t) a =
    inst {Γ ▷' El' ∘ A}{(El' ∘ A) ∘ π₁}{El' ∘ V B} vz a
         (coe {!!} t)
    
  nfApp {Γ} {A} {B} refl (ne x sp) a = ne x (snocSp sp a)  
  
  nfApp {Γ} {A} {B} eq (Π C D) a with LEM (ElC Γ)
  ... | inj₂ ¬p = coe (Nf Γ & ⊥→-unique ¬p _ _) tt
  ... | inj₁ p  with (λ f → f p) & eq
  ... | ()  
  nfApp {Γ} {A} {B} eq unit a with LEM (ElC Γ)
  ... | inj₂ ¬p = coe (Nf Γ & ⊥→-unique ¬p _ _) tt
  ... | inj₁ p  with (λ f → f p) & eq
  ... | ()
  nfApp {Γ} {A} {B} eq tt a with LEM (ElC Γ)
  ... | inj₂ ¬p = coe (Nf Γ & ⊥→-unique ¬p _ _) tt  
  ... | inj₁ p with (λ f → f p) & eq
  ... | ()

