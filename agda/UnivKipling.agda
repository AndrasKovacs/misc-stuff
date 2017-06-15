
{-# OPTIONS --without-K #-}

open import Level renaming (zero to lzero; suc to lsuc)
open import Data.Nat
open import Function
open import Data.Unit.Base
open import Data.Product
open import Relation.Binary.PropositionalEquality

infix 6 _⁻¹
infixr 5 _◾_
infixl 6 _▷'_
infixl 9 _&_

-- postulate
--   ext : ∀ {α β} → Extensionality α β

J : ∀ {α} {A : Set α} {x : A} (P : {y : A} → x ≡ y → Set) → P refl → ∀ {y}(p : x ≡ y) → P p
J P pr refl = pr

coe : ∀ {α}{A B : Set α} → A ≡ B → A → B
coe refl a = a
_&_ = cong
_◾_ = trans
_⁻¹ = sym
π₁  = proj₁
π₂  = proj₂
ᴷ   = const
Λ   = curry

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

-- data Ty  : Con' → Set
data Var : (Γ : Con') → Ty' Γ → Set
data Tm  : (Γ : Con') → Ty' Γ → Set

⟦_⟧ᵛ     : ∀ {Γ A} → Var Γ A → Var' Γ A
⟦_⟧      : ∀ {Γ A} → Tm Γ A → Tm' Γ A

-- data Ty where
--   U  : ∀ {Γ} → Ty Γ
--   El : ∀ {Γ} → Tm Γ (ᴷ U'') → Ty Γ

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

OPE' = λ (Γ Δ : Con') → ElC Γ → ElC Δ

mutual
  data OPE : Con' → Con' → Set where
    ∙    : OPE ∙' ∙'
    drop : ∀ {Γ Δ A} → OPE Γ Δ → OPE (Γ ▷' A) Δ
    keep : ∀ {Γ Δ A} (σ : OPE Γ Δ) → OPE (Γ ▷' A ∘ ⟦ σ ⟧ᵒ) (Δ ▷' A)

  ⟦_⟧ᵒ : ∀ {Γ Δ} → OPE Γ Δ → OPE' Γ Δ
  ⟦ ∙      ⟧ᵒ = id
  ⟦ drop σ ⟧ᵒ = ⟦ σ ⟧ᵒ ∘ π₁
  ⟦ keep σ ⟧ᵒ = map ⟦ σ ⟧ᵒ id

Varₑ : ∀ {Γ Δ A}(σ : OPE Γ Δ) → Var Δ A → Var Γ (A ∘ ⟦ σ ⟧ᵒ)
Varₑ ∙        x      = x
Varₑ (drop σ) x      = vs (Varₑ σ x)
Varₑ (keep σ) vz     = vz
Varₑ (keep σ) (vs x) = vs (Varₑ σ x)

⟦Varₑ⟧ : ∀ {Γ Δ A}(σ : OPE Γ Δ)(x : Var Δ A) → ⟦ Varₑ σ x ⟧ᵛ ≡ ⟦ x ⟧ᵛ ∘ ⟦ σ ⟧ᵒ
⟦Varₑ⟧ ∙        x      = refl
⟦Varₑ⟧ (drop σ) x      = (_∘ π₁) & ⟦Varₑ⟧ σ x
⟦Varₑ⟧ (keep σ) vz     = refl
⟦Varₑ⟧ (keep σ) (vs x) = (_∘ π₁) & ⟦Varₑ⟧ σ x

Tmₑ   : ∀ {Γ Δ A}(σ : OPE Γ Δ) → Tm Δ A → Tm Γ (A ∘ ⟦ σ ⟧ᵒ)
⟦Tmₑ⟧ : ∀ {Γ Δ A}(σ : OPE Γ Δ)(t : Tm Δ A) → ⟦ Tmₑ σ t ⟧ ≡ ⟦ t ⟧ ∘ ⟦ σ ⟧ᵒ

Tmₑ σ (var x) = var (Varₑ σ x)

Tmₑ {Γ} {Δ} σ (app {A = A} {B} t u) =
  coe ((λ y → Tm Γ (λ x → El' (B (⟦ σ ⟧ᵒ x) (y x)))) & ⟦Tmₑ⟧ σ u) (app (Tmₑ σ t) (Tmₑ σ u))
  
Tmₑ σ (lam t) = lam (Tmₑ (keep σ) t)

Tmₑ {Γ} σ (Π A B) =
  Π (Tmₑ σ A) (coe ((λ y → Tm (Γ ▷' (λ x → El' (y x))) (λ _ → U'')) & (⟦Tmₑ⟧ σ A ⁻¹)) (Tmₑ (keep σ) B))
      
Tmₑ σ unit      = unit
Tmₑ σ tt        = tt

⟦Tmₑ⟧ σ (var x)   = ⟦Varₑ⟧ σ x
⟦Tmₑ⟧ {Γ} σ (app {A = A} {B} t u) =
  J {x = ⟦ Tmₑ σ u ⟧}
    (λ {z} p → ⟦ coe ((λ y → Tm Γ (λ x → El' (B (⟦ σ ⟧ᵒ x) (y x)))) & p) (app (Tmₑ σ t) (Tmₑ σ u)) ⟧
               ≡ (⟦ t ⟧ ∘ ⟦ σ ⟧ᵒ ˢ z))
      ((_ˢ ⟦ Tmₑ σ u ⟧) & ⟦Tmₑ⟧ σ t)
      (⟦Tmₑ⟧ σ u)
      
⟦Tmₑ⟧ σ (lam t) = Λ & ⟦Tmₑ⟧ (keep σ) t

⟦Tmₑ⟧ {Γ} σ (Π A B) =
  (J {x = ⟦ A ⟧ ∘ ⟦ σ ⟧ᵒ}
     (λ {z} p → (λ x →
           Π' (z x)
           (λ y → ⟦ coe ((λ y → Tm (Γ ▷' El' ∘ y) (ᴷ U'')) & p)
                        (Tmₑ (keep σ) B) ⟧
                  (x , y)))
           ≡ (λ x → Π' (⟦ A ⟧ (⟦ σ ⟧ᵒ x)) (λ y → ⟦ B ⟧ (⟦ σ ⟧ᵒ x , y))))
      ((λ foo → Π' ∘ (⟦ A ⟧ ∘ ⟦ σ ⟧ᵒ) ˢ Λ foo) & ⟦Tmₑ⟧ (keep σ) B)
      (⟦Tmₑ⟧ σ A ⁻¹))      

⟦Tmₑ⟧ σ unit = refl
⟦Tmₑ⟧ σ tt   = refl

-- Tyₑ : ∀ {Γ Δ} → OPE Γ Δ → Ty Δ → Ty Γ
-- Tyₑ σ U      = U
-- Tyₑ σ (El t) = El (Tmₑ σ t )

--------------------------------------------------------------------------------

-- data NfTy : Con' → Set
data NfTm : (Γ : Con') → Ty' Γ → Set
data NeTm : (Γ : Con') → Ty' Γ → Set

⟦_⟧ₙ      : ∀ {Γ A} → NfTm Γ A → Tm' Γ A
⟦_⟧ₙₑ     : ∀ {Γ A} → NeTm Γ A → Tm' Γ A

-- data NfTy where
--   U  : ∀ {Γ} → NfTy Γ
--   El : ∀ {Γ} → NfTm Γ (ᴷ U'') → NfTy Γ

data NfTm where
  ne   : ∀ {Γ}(A : NeTm Γ (ᴷ U'')) → NeTm Γ (El' ∘ ⟦ A ⟧ₙₑ) → NfTm Γ (El' ∘ ⟦ A ⟧ₙₑ)
  lam  : ∀ {Γ A B} → NfTm (Γ ▷' (El' ∘ A)) (El' ∘ B) → NfTm Γ (El' ∘ (Π' ∘ A ˢ Λ B))
  Π    : ∀ {Γ}(A : NfTm Γ (ᴷ U'')) → NfTm (Γ ▷' (El' ∘ ⟦ A ⟧ₙ)) (ᴷ U'') → NfTm Γ (ᴷ U'')  
  unit : ∀ {Γ} → NfTm Γ (ᴷ U'')
  tt   : ∀ {Γ} → NfTm Γ (ᴷ (El' ⊤'))

data NeTm where
  var : ∀ {Γ A} → Var Γ A → NeTm Γ A
  app : ∀ {Γ A B} → NeTm Γ (El' ∘ (Π' ∘ A ˢ B)) → (a : NfTm Γ (El' ∘ A)) → NeTm Γ (El' ∘ (B ˢ ⟦ a ⟧ₙ))

⟦ ne A x  ⟧ₙ  = ⟦ x ⟧ₙₑ
⟦ lam t   ⟧ₙ  = Λ ⟦ t ⟧ₙ
⟦ Π A B   ⟧ₙ  = Π' ∘ ⟦ A ⟧ₙ ˢ Λ ⟦ B ⟧ₙ
⟦ unit    ⟧ₙ  = ᴷ ⊤'
⟦ tt      ⟧ₙ  = ᴷ tt
⟦ var x   ⟧ₙₑ = ⟦ x ⟧ᵛ
⟦ app t a ⟧ₙₑ = ⟦ t ⟧ₙₑ ˢ ⟦ a ⟧ₙ

