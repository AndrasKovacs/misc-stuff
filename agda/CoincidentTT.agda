{-# OPTIONS --rewriting #-}

open import Level renaming (zero to lzero; suc to lsuc)
open import Function
open import Data.Unit.Base
open import Data.Empty
open import Data.Product
open import Relation.Binary.PropositionalEquality

infix 6 _⁻¹
infixr 5 _◾_

coe : ∀ {α}{A B : Set α} → A ≡ B → A → B
coe refl a = a
ap = cong
_◾_ = trans
_⁻¹ = sym

mutual
  data UU : Set where
    Π' Σ' : (A : UU) → (EL A → UU) → UU
    ⊤'    : UU
    U'    : UU
    El'   : EL U' → UU

  EL : UU → Set
  EL (Π' A B) = (a : EL A) → EL (B a)
  EL (Σ' A B) = Σ (EL A) (λ a → EL (B a))
  EL ⊤'       = ⊤
  EL U'       = ⊥
  EL (El' _)  = ⊥

infixl 6 _▷_
infixr 4 _∘ₛ_

data Con : Set
data Ty  : Con → Set
data Tm  : (Γ : Con) → Ty Γ → Set
data Sub : Con → Con → Set

⟦_⟧ᶜ : Con → UU
⟦_⟧ᵗ : ∀ {Γ} → Ty Γ → EL (⟦ Γ ⟧ᶜ) → UU
⟦_⟧ˢ : ∀ {Γ Δ} → Sub Γ Δ → EL ⟦ Γ ⟧ᶜ → EL ⟦ Δ ⟧ᶜ
⟦_⟧  : ∀ {Γ A} → Tm Γ A → ∀ ⟦Γ⟧ → EL (⟦ A ⟧ᵗ ⟦Γ⟧)

data Con where
  ∙   : Con
  _▷_ : (Γ : Con) → Ty Γ → Con

data Ty where
  U   : ∀ {Γ} → Ty Γ
  El  : ∀ {Γ} → Tm Γ U → Ty Γ
  Π   : ∀ {Γ}(A : Ty Γ) → Ty (Γ ▷ A) → Ty Γ
  Tyₛ : ∀ {Γ Δ} → Sub Γ Δ → Ty Δ → Ty Γ

data Sub where
  ∙    : ∀ {Γ} → Sub Γ ∙
  _▷_  : ∀ {Γ Δ A}(σ : Sub Γ Δ) → Tm Γ (Tyₛ σ A) → Sub Γ (Δ ▷ A)
  idₛ  : ∀ {Γ} → Sub Γ Γ
  _∘ₛ_ : ∀ {Γ Δ Σ} → Sub Δ Σ → Sub Γ Δ → Sub Γ Σ
  π₁   : ∀ {Γ Δ A} → Sub Γ (Δ ▷ A) → Sub Γ Δ

data Tm where
  π₂  : ∀ {Γ Δ A} → (σ : Sub Γ (Δ ▷ A)) → Tm Γ (Tyₛ (π₁ σ) A)
  lam : ∀ {Γ A B} → Tm (Γ ▷ A) B → Tm Γ (Π A B)
  app : ∀ {Γ A B} → Tm Γ (Π A B) → Tm (Γ ▷ A) B
  Tmₛ : ∀ {Γ Δ A} → (σ : Sub Γ Δ) → Tm Δ A → Tm Γ (Tyₛ σ A)

⟦ ∙       ⟧ᶜ = ⊤'
⟦ Γ ▷ A   ⟧ᶜ = Σ' ⟦ Γ ⟧ᶜ ⟦ A ⟧ᵗ
⟦ U       ⟧ᵗ = λ _ → U'
⟦ El t    ⟧ᵗ = λ ⟦Γ⟧ → El' (⟦ t ⟧ ⟦Γ⟧)
⟦ Π A B   ⟧ᵗ = λ ⟦Γ⟧ → Π' (⟦ A ⟧ᵗ ⟦Γ⟧) (λ ⟦a⟧ → ⟦ B ⟧ᵗ (⟦Γ⟧ , ⟦a⟧))
⟦ Tyₛ σ A ⟧ᵗ = λ ⟦Γ⟧ → ⟦ A ⟧ᵗ (⟦ σ ⟧ˢ ⟦Γ⟧)
⟦ ∙       ⟧ˢ = λ _ → tt
⟦ σ ▷ t   ⟧ˢ = λ ⟦Γ⟧ → ⟦ σ ⟧ˢ ⟦Γ⟧ , ⟦ t ⟧ ⟦Γ⟧
⟦ idₛ     ⟧ˢ = id
⟦ σ ∘ₛ δ  ⟧ˢ = ⟦ σ ⟧ˢ ∘ ⟦ δ ⟧ˢ
⟦ π₁ σ    ⟧ˢ = proj₁ ∘ ⟦ σ ⟧ˢ
⟦ π₂ σ    ⟧  = proj₂ ∘ ⟦ σ ⟧ˢ
⟦ lam t   ⟧  = curry   ⟦ t ⟧
⟦ app t   ⟧  = uncurry ⟦ t ⟧
⟦ Tmₛ σ t ⟧  = ⟦ t ⟧ ∘ ⟦ σ ⟧ˢ

postulate
  conv    : ∀ {Γ}(A B : Ty Γ) → ⟦ A ⟧ᵗ ≡ ⟦ B ⟧ᵗ → A ≡ B
  ⟦conv⟧ᵗ : ∀ {Γ} (A B : Ty Γ) (p : ⟦ A ⟧ᵗ ≡ ⟦ B ⟧ᵗ) → ap ⟦_⟧ᵗ (conv A B p) ≡ p

  







-- -- based on https://github.com/effectfully/random-stuff/blob/master/EatEval.agda

-- {-# OPTIONS --without-K #-}

-- open import Level renaming (zero to lzero; suc to lsuc)
-- open import Function
-- open import Data.Unit.Base
-- open import Data.Empty
-- open import Data.Product
-- open import Relation.Binary.PropositionalEquality

-- --------------------------------------------------------------------------------

-- -- We need this in order to put equality of type codes in Set₀
-- -- Having _≡_ always return in Set₀ is incompatible with univalence
-- mutual
--   data UU : Set where
--     Π' Σ' : (A : UU) → (EL A → UU) → UU
--     ⊤'    : UU
--     U'    : UU
--     El'   : EL U' → UU

--   EL : UU → Set
--   EL (Π' A B) = (a : EL A) → EL (B a)
--   EL (Σ' A B) = Σ (EL A) (λ a → EL (B a))
--   EL ⊤'       = ⊤
--   EL U'       = ⊥
--   EL (El' _)  = ⊥

-- --------------------------------------------------------------------------------

-- infixl 6 _▷_
-- infixr 4 _∘ₛ_

-- data Con : Set
-- data Ty  : Con → Set
-- data Tm  : (Γ : Con) → Ty Γ → Set
-- data Sub : Con → Con → Set

-- ⟦_⟧ᶜ : Con → UU
-- ⟦_⟧ᵗ : ∀ {Γ} → Ty Γ → EL (⟦ Γ ⟧ᶜ) → UU
-- ⟦_⟧ˢ : ∀ {Γ Δ} → Sub Γ Δ → EL ⟦ Γ ⟧ᶜ → EL ⟦ Δ ⟧ᶜ
-- ⟦_⟧  : ∀ {Γ A} → Tm Γ A → ∀ ⟦Γ⟧ → EL (⟦ A ⟧ᵗ ⟦Γ⟧)

-- _~ᵗ_ : ∀ {Γ} → Ty Γ → Ty Γ → Set
-- A ~ᵗ B = ⟦ A ⟧ᵗ ≡ ⟦ B ⟧ᵗ

-- data Con where
--   ∙   : Con
--   _▷_ : (Γ : Con) → Ty Γ → Con

-- data Ty where
--   U   : ∀ {Γ} → Ty Γ
--   El  : ∀ {Γ} → Tm Γ U → Ty Γ
--   Π   : ∀ {Γ}(A : Ty Γ) → Ty (Γ ▷ A) → Ty Γ
--   Tyₛ : ∀ {Γ Δ} → Sub Γ Δ → Ty Δ → Ty Γ

-- data Sub where
--   ∙    : ∀ {Γ} → Sub Γ ∙
--   _▷_  : ∀ {Γ Δ A}(σ : Sub Γ Δ) → Tm Γ (Tyₛ σ A) → Sub Γ (Δ ▷ A)
--   idₛ  : ∀ {Γ} → Sub Γ Γ
--   _∘ₛ_ : ∀ {Γ Δ Σ} → Sub Δ Σ → Sub Γ Δ → Sub Γ Σ
--   π₁   : ∀ {Γ Δ A} → Sub Γ (Δ ▷ A) → Sub Γ Δ

-- data Tm where
--   π₂  : ∀ {Γ Δ A} → (σ : Sub Γ (Δ ▷ A)) → Tm Γ (Tyₛ (π₁ σ) A)
--   lam : ∀ {Γ A B} → Tm (Γ ▷ A) B → Tm Γ (Π A B)
--   app : ∀ {Γ A B} → Tm Γ (Π A B) → Tm (Γ ▷ A) B
--   Tmₛ : ∀ {Γ Δ A} → (σ : Sub Γ Δ) → Tm Δ A → Tm Γ (Tyₛ σ A)
--   coe : ∀ {Γ A B} → A ~ᵗ B → Tm Γ A → Tm Γ B

-- ⟦ ∙       ⟧ᶜ = ⊤'
-- ⟦ Γ ▷ A   ⟧ᶜ = Σ' ⟦ Γ ⟧ᶜ ⟦ A ⟧ᵗ
-- ⟦ U       ⟧ᵗ = λ _ → U'
-- ⟦ El t    ⟧ᵗ = λ ⟦Γ⟧ → El' (⟦ t ⟧ ⟦Γ⟧)
-- ⟦ Π A B   ⟧ᵗ = λ ⟦Γ⟧ → Π' (⟦ A ⟧ᵗ ⟦Γ⟧) (λ ⟦a⟧ → ⟦ B ⟧ᵗ (⟦Γ⟧ , ⟦a⟧))
-- ⟦ Tyₛ σ A ⟧ᵗ = λ ⟦Γ⟧ → ⟦ A ⟧ᵗ (⟦ σ ⟧ˢ ⟦Γ⟧)
-- ⟦ ∙       ⟧ˢ = λ _ → tt
-- ⟦ σ ▷ t   ⟧ˢ = λ ⟦Γ⟧ → ⟦ σ ⟧ˢ ⟦Γ⟧ , ⟦ t ⟧ ⟦Γ⟧
-- ⟦ idₛ     ⟧ˢ = id
-- ⟦ σ ∘ₛ δ  ⟧ˢ = ⟦ σ ⟧ˢ ∘ ⟦ δ ⟧ˢ
-- ⟦ π₁ σ    ⟧ˢ = proj₁ ∘ ⟦ σ ⟧ˢ
-- ⟦ π₂ σ    ⟧  = proj₂ ∘ ⟦ σ ⟧ˢ
-- ⟦ lam t   ⟧  = curry   ⟦ t ⟧
-- ⟦ app t   ⟧  = uncurry ⟦ t ⟧
-- ⟦ Tmₛ σ t ⟧  = ⟦ t ⟧ ∘ ⟦ σ ⟧ˢ
-- ⟦ coe p t ⟧  = λ ⟦Γ⟧ → subst (λ x → EL (x ⟦Γ⟧)) p (⟦ t ⟧ ⟦Γ⟧)

-- --------------------------------------------------------------------------------

-- wk : ∀ {Γ A} → Sub (Γ ▷ A) Γ
-- wk = π₁ idₛ

-- vz : ∀ {Γ A} → Tm (Γ ▷ A) (Tyₛ wk A)
-- vz = π₂ idₛ

-- vs : ∀ {Γ A B} → Tm Γ A → Tm (Γ ▷ B) (Tyₛ wk A)
-- vs = Tmₛ wk

-- <_> : ∀ {Γ A} → Tm Γ A → Sub Γ (Γ ▷ A)
-- < t > = idₛ ▷ coe refl t

-- infixl 8 _⊗_
-- _⊗_ : ∀ {Γ A B} → Tm Γ (Π A B) → (a : Tm Γ A) → Tm Γ (Tyₛ < a > B)
-- f ⊗ a = Tmₛ (idₛ ▷ coe refl a) (app f)

-- mutual
--   data OPE : Con → Con → Set where
--     ∙    : OPE ∙ ∙
--     drop : ∀ {Γ Δ A} → OPE Γ Δ → OPE (Γ ▷ A) Δ
--     keep : ∀ {Γ Δ A} → (σ : OPE Γ Δ) → OPE (Γ ▷ Tyₛ ⌜ σ ⌝ᵒ A) (Δ ▷ A)

--   ⌜_⌝ᵒ : ∀ {Γ Δ} → OPE Γ Δ → Sub Γ Δ
--   ⌜ ∙      ⌝ᵒ = ∙
--   ⌜ drop σ ⌝ᵒ =  ⌜ σ ⌝ᵒ ∘ₛ π₁ idₛ
--   ⌜ keep σ ⌝ᵒ = (⌜ σ ⌝ᵒ ∘ₛ π₁ idₛ) ▷ coe refl vz


-- --------------------------------------------------------------------------------

-- data Var : (Γ : Con) → Ty Γ → Set where
--   vzₙ  : ∀ {Γ A} → Var (Γ ▷ A) (Tyₛ wk A)
--   vsₙ  : ∀ {Γ A B} → Var Γ A → Var (Γ ▷ B) (Tyₛ wk A)
--   coeᵥ : ∀ {Γ A B} → A ~ᵗ B → Var Γ A → Var Γ B

-- -- coeᵥ ruins uniqueness of normal forms
-- -- this does not seem to actually work without quotients

-- ⌜_⌝ᵛ : ∀ {Γ A} → Var Γ A → Tm Γ A
-- ⌜ vzₙ      ⌝ᵛ = vz
-- ⌜ vsₙ v    ⌝ᵛ = vs ⌜ v ⌝ᵛ
-- ⌜ coeᵥ p v ⌝ᵛ = coe p ⌜ v ⌝ᵛ

-- Varₑ : ∀ {Γ Δ A} → (σ : OPE Δ Γ) → Var Γ A → Var Δ (Tyₛ ⌜ σ ⌝ᵒ A)
-- Varₑ ∙        v          = coeᵥ refl v
-- Varₑ (drop σ) v          = coeᵥ refl (vsₙ (Varₑ σ v))
-- Varₑ (keep σ) vzₙ        = coeᵥ refl vzₙ
-- Varₑ (keep σ) (vsₙ v)    = coeᵥ refl (vsₙ (Varₑ σ v))
-- Varₑ (keep σ) (coeᵥ p v) =
--   coeᵥ (cong (λ x → (λ ⟦Γ⟧ → x (⟦ ⌜ σ ⌝ᵒ ⟧ˢ (proj₁ ⟦Γ⟧) , proj₂ ⟦Γ⟧))) p)
--        (Varₑ (keep σ) v)

-- data Ne (Γ : Con) : Ty Γ → Set
-- data Nf (Γ : Con) : Ty Γ → Set
-- ⌜_⌝ⁿᶠ : ∀ {Γ A} → Nf Γ A → Tm Γ A
-- ⌜_⌝ⁿᵉ : ∀ {Γ A} → Ne Γ A → Tm Γ A

-- data Ne Γ where
--   var : ∀ {A} → Var Γ A → Ne Γ A
--   app : ∀ {A B} (f : Ne Γ (Π A B))(a : Nf Γ A) → Ne Γ (Tyₛ < ⌜ a ⌝ⁿᶠ > B)

-- data Nf (Γ : Con) where
--   lam  : ∀ {A B} → Nf (Γ ▷ A) B → Nf Γ (Π A B)
--   neU  : Ne Γ U → Nf Γ U
--   neEl : ∀ {A} → Ne Γ (El A) → Nf Γ (El A)

-- ⌜ lam n   ⌝ⁿᶠ = lam ⌜ n ⌝ⁿᶠ
-- ⌜ neU n   ⌝ⁿᶠ = ⌜ n ⌝ⁿᵉ
-- ⌜ neEl n  ⌝ⁿᶠ = ⌜ n ⌝ⁿᵉ
-- ⌜ var v   ⌝ⁿᵉ = ⌜ v ⌝ᵛ
-- ⌜ app n a ⌝ⁿᵉ = ⌜ n ⌝ⁿᵉ ⊗ ⌜ a ⌝ⁿᶠ

-- Neₑ : ∀ {Γ Δ A} → (σ : OPE Δ Γ) → Ne Γ A → Ne Δ (Tyₛ ⌜ σ ⌝ᵒ A)
-- Neₑ σ (var v)   = var (Varₑ σ v)
-- Neₑ σ (app n a) = {!!}

-- Nfₑ : ∀ {Γ Δ A} → (σ : OPE Δ Γ) → Nf Γ A → Ne Δ (Tyₛ ⌜ σ ⌝ᵒ A)
-- Nfₑ σ (lam t)  = {!!}
-- Nfₑ σ (neU n)  = {!!}
-- Nfₑ σ (neEl n) = {!!}


