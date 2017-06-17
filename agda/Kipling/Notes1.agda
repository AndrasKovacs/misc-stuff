
{-# OPTIONS --without-K #-}

open import Level renaming (zero to lzero; suc to lsuc)
open import Data.Nat
open import Function
open import Data.Unit.Base
open import Data.Product
open import Relation.Binary.PropositionalEquality

infix 6 _⁻¹
infixr 5 _◾_
infixl 6 _▷'_ _▷_
infixl 9 _&_

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

Tmₑ   : ∀ {Γ Δ A}(σ : OPE Γ Δ) → Tm Δ A → Tm Γ (A ∘ ⟦ σ ⟧ᵉ)
⟦Tmₑ⟧ : ∀ {Γ Δ A}(σ : OPE Γ Δ)(t : Tm Δ A) → ⟦ Tmₑ σ t ⟧ ≡ ⟦ t ⟧ ∘ ⟦ σ ⟧ᵉ

Tmₑ σ (var x) = var (Varₑ σ x)

Tmₑ {Γ} {Δ} σ (app {A = A} {B} t u) =
  coe ((λ y → Tm Γ (λ x → El' (B (⟦ σ ⟧ᵉ x) (y x)))) & ⟦Tmₑ⟧ σ u) (app (Tmₑ σ t) (Tmₑ σ u))
  
Tmₑ σ (lam t) = lam (Tmₑ (keep σ) t)

Tmₑ {Γ} σ (Π A B) =
  Π (Tmₑ σ A) (coe ((λ y → Tm (Γ ▷' (λ x → El' (y x))) (λ _ → U'')) & (⟦Tmₑ⟧ σ A ⁻¹)) (Tmₑ (keep σ) B))
      
Tmₑ σ unit      = unit
Tmₑ σ tt        = tt

⟦Tmₑ⟧ σ (var x)   = ⟦Varₑ⟧ σ x
⟦Tmₑ⟧ {Γ} σ (app {A = A} {B} t u) =
  J {x = ⟦ Tmₑ σ u ⟧}
    (λ {z} p → ⟦ coe ((λ y → Tm Γ (λ x → El' (B (⟦ σ ⟧ᵉ x) (y x)))) & p) (app (Tmₑ σ t) (Tmₑ σ u)) ⟧
               ≡ (⟦ t ⟧ ∘ ⟦ σ ⟧ᵉ ˢ z))
      ((_ˢ ⟦ Tmₑ σ u ⟧) & ⟦Tmₑ⟧ σ t)
      (⟦Tmₑ⟧ σ u)
      
⟦Tmₑ⟧ σ (lam t) = Λ & ⟦Tmₑ⟧ (keep σ) t

⟦Tmₑ⟧ {Γ} σ (Π A B) =
  (J {x = ⟦ A ⟧ ∘ ⟦ σ ⟧ᵉ}
     (λ {z} p → (λ x →
           Π' (z x)
           (λ y → ⟦ coe ((λ y → Tm (Γ ▷' El' ∘ y) (ᴷ U'')) & p)
                        (Tmₑ (keep σ) B) ⟧
                  (x , y)))
           ≡ (λ x → Π' (⟦ A ⟧ (⟦ σ ⟧ᵉ x)) (λ y → ⟦ B ⟧ (⟦ σ ⟧ᵉ x , y))))
      ((λ foo → Π' ∘ (⟦ A ⟧ ∘ ⟦ σ ⟧ᵉ) ˢ Λ foo) & ⟦Tmₑ⟧ (keep σ) B)
      (⟦Tmₑ⟧ σ A ⁻¹))      

⟦Tmₑ⟧ σ unit = refl
⟦Tmₑ⟧ σ tt   = refl

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

--------------------------------------------------------------------------------

Sub' = λ (Γ Δ : Con') → ElC Γ → ElC Δ

mutual
  data Sub (Γ : Con') : Con' → Set where
    ∙    : Sub Γ ∙'
    _▷_ : ∀ {Δ A}(σ : Sub Γ Δ) → Tm Γ (A ∘ ⟦ σ ⟧ˢ) → Sub Γ (Δ ▷' A)

  ⟦_⟧ˢ : ∀ {Γ Δ} → Sub Γ Δ → Sub' Γ Δ
  ⟦ ∙     ⟧ˢ = ᴷ tt
  ⟦ σ ▷ t ⟧ˢ = _,_ ∘ ⟦ σ ⟧ˢ ˢ ⟦ t ⟧

infixr 6 _ₛ∘ₑ_ 
_ₛ∘ₑ_ : ∀ {Γ Δ Σ} → Sub Δ Σ → OPE Γ Δ → Sub Γ Σ
⟦ₛ∘ₑ⟧ : ∀ {Γ Δ Σ}(σ : Sub Δ Σ)(δ : OPE Γ Δ) → ⟦ σ ₛ∘ₑ δ ⟧ˢ ≡ ⟦ σ ⟧ˢ ∘ ⟦ δ ⟧ᵉ
∙        ₛ∘ₑ  δ = ∙
_ₛ∘ₑ_ {Γ} (_▷_ {Δ} {A} σ t) δ = (σ ₛ∘ₑ δ) ▷ coe (Tm Γ & ((A ∘_) & (⟦ₛ∘ₑ⟧ σ δ ⁻¹))) (Tmₑ δ t) -- 
⟦ₛ∘ₑ⟧ ∙ δ = refl
⟦ₛ∘ₑ⟧ {Γ} (_▷_ {A = A} σ t) δ =
  J (λ {y} p →
       (λ x → y x , ⟦ coe (Tm Γ & ((λ g x₁ → A (g x₁)) & p)) (Tmₑ δ t) ⟧ x)
        ≡ (λ x → ⟦ σ ⟧ˢ (⟦ δ ⟧ᵉ x) , ⟦ t ⟧ (⟦ δ ⟧ᵉ x)))
     ((λ y → (λ x → ⟦ σ ⟧ˢ (⟦ δ ⟧ᵉ x) , y x)) & ⟦Tmₑ⟧ δ t)
     (⟦ₛ∘ₑ⟧ σ δ ⁻¹)

keepₛ : ∀ {Γ Δ A}(σ : Sub Γ Δ) → Sub (Γ ▷' A ∘ ⟦ σ ⟧ˢ) (Δ ▷' A)
keepₛ {Γ}{Δ}{A} σ =
  (σ ₛ∘ₑ drop idₑ) ▷
  coe
    ((λ y → Tm (Γ ▷' (λ x → A (⟦ σ ⟧ˢ x))) (A ∘ y)) &
        ((⟦ σ ⟧ˢ ∘_) & ((_∘ π₁) & ⟦idₑ⟧ ⁻¹)
      ◾ ⟦ₛ∘ₑ⟧ σ (drop idₑ) ⁻¹))
    (var (vz {_}{A ∘ ⟦ σ ⟧ˢ}))

Varₛ : ∀ {Γ Δ A}(σ : Sub Γ Δ) → Var Δ A → Tm Γ (A ∘ ⟦ σ ⟧ˢ)
Varₛ (σ ▷ t) vz     = t
Varₛ (σ ▷ t) (vs x) = Varₛ σ x

⟦Varₛ⟧ : ∀ {Γ Δ A}(σ : Sub Γ Δ)(x : Var Δ A) → ⟦ Varₛ σ x ⟧ ≡ ⟦ x ⟧ᵛ ∘ ⟦ σ ⟧ˢ
⟦Varₛ⟧ (σ ▷ t) vz     = refl
⟦Varₛ⟧ (σ ▷ t) (vs x) = ⟦Varₛ⟧ σ x

Tmₛ   : ∀ {Γ Δ A}(σ : Sub Γ Δ) → Tm Δ A → Tm Γ (A ∘ ⟦ σ ⟧ˢ)
⟦Tmₛ⟧ : ∀ {Γ Δ A}(σ : Sub Γ Δ)(t : Tm Δ A) → ⟦ Tmₛ σ t ⟧ ≡ ⟦ t ⟧ ∘ ⟦ σ ⟧ˢ

Tmₛ σ (var x)   = Varₛ σ x
Tmₛ {Γ} σ (app {B = B} t u) =
  coe ((λ y → Tm Γ (λ x → El' (B (⟦ σ ⟧ˢ x) (y x)))) & ⟦Tmₛ⟧ σ u)
    (app (Tmₛ σ t) (Tmₛ σ u))
    
Tmₛ {Γ} σ (lam {A = A} {B} t) = lam (coe {!!} (Tmₛ (keepₛ σ) t))

Tmₛ {Γ} σ (Π A B) =
  Π (Tmₛ σ A)
    (coe ((λ y → Tm (Γ ▷' El' ∘ y) (λ x → U'')) & (⟦Tmₛ⟧ σ A ⁻¹)) (Tmₛ (keepₛ σ ) B))
    
Tmₛ σ unit      = unit
Tmₛ σ tt        = tt

⟦Tmₛ⟧ σ (var x)   = ⟦Varₛ⟧ σ x
⟦Tmₛ⟧ {Γ} σ (app {B = B} t u) = {!!}
⟦Tmₛ⟧ σ (lam t)   = {!!}
⟦Tmₛ⟧ σ (Π A B)   = {!!}
⟦Tmₛ⟧ σ unit      = refl
⟦Tmₛ⟧ σ tt        = refl

--------------------------------------------------------------------------------

-- module NfSimple where
--   data NfTm : (Γ : Con') → Ty' Γ → Set
--   data NeTm : (Γ : Con') → Ty' Γ → Set  
--   ⟦_⟧ₙ      : ∀ {Γ A} → NfTm Γ A → Tm' Γ A
--   ⟦_⟧ₙₑ     : ∀ {Γ A} → NeTm Γ A → Tm' Γ A
  
--   data NfTm where
--     ne   : ∀ {Γ}(A : NeTm Γ (ᴷ U'')) → NeTm Γ (El' ∘ ⟦ A ⟧ₙₑ) → NfTm Γ (El' ∘ ⟦ A ⟧ₙₑ)
--     lam  : ∀ {Γ A B} → NfTm (Γ ▷' (El' ∘ A)) (El' ∘ B) → NfTm Γ (El' ∘ (Π' ∘ A ˢ Λ B))
--     Π    : ∀ {Γ}(A : NfTm Γ (ᴷ U'')) → NfTm (Γ ▷' (El' ∘ ⟦ A ⟧ₙ)) (ᴷ U'') → NfTm Γ (ᴷ U'')  
--     unit : ∀ {Γ} → NfTm Γ (ᴷ U'')
--     tt   : ∀ {Γ} → NfTm Γ (ᴷ (El' ⊤'))
  
--   data NeTm where
--     var : ∀ {Γ A} → Var Γ A → NeTm Γ A
--     app : ∀ {Γ A B} → NeTm Γ (El' ∘ (Π' ∘ A ˢ B)) → (a : NfTm Γ (El' ∘ A)) → NeTm Γ (El' ∘ (B ˢ ⟦ a ⟧ₙ))
  
--   ⟦ ne A x  ⟧ₙ  = ⟦ x ⟧ₙₑ
--   ⟦ lam t   ⟧ₙ  = Λ ⟦ t ⟧ₙ
--   ⟦ Π A B   ⟧ₙ  = Π' ∘ ⟦ A ⟧ₙ ˢ Λ ⟦ B ⟧ₙ
--   ⟦ unit    ⟧ₙ  = ᴷ ⊤'
--   ⟦ tt      ⟧ₙ  = ᴷ tt
--   ⟦ var x   ⟧ₙₑ = ⟦ x ⟧ᵛ
--   ⟦ app t a ⟧ₙₑ = ⟦ t ⟧ₙₑ ˢ ⟦ a ⟧ₙ

