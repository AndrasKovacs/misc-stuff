
module Norm where

open import Basic hiding (_∘_)

open import Data.Product renaming (map to pmap)
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Data.Sum renaming (map to smap) hiding ([_,_])
open import Function using (_$_; id; _∘_)
import Function as F
open import Data.Unit
open import Data.Empty

-- Reduction
--------------------------------------------------------------------------------

data _~>_ {Γ} : ∀ {A} → Tm Γ A → Tm Γ A → Set where
  β  : ∀ {A B}(t : Tm (Γ ▷ A) B) t'                →  ƛ t ∙ t' ~> sub vz t' t
  ƛ  : ∀ {A B}{t : Tm (Γ ▷ A) B} t'      → t ~> t' →  ƛ t      ~> ƛ t'
  ∙₁ : ∀ {A B}{f} (f' : Tm Γ (A ⇒ B)){x} → f ~> f' →  (f ∙ x)  ~> (f' ∙ x)
  ∙₂ : ∀ {A B}{f : Tm Γ (A ⇒ B)} {x} x'  → x ~> x' →  (f ∙ x)  ~> (f ∙ x')
infix 3 _~>_

-- Strong normalization
--------------------------------------------------------------------------------

data SN {Γ A} (t : Tm Γ A) : Set where
  sn : (∀ {t'} → t ~> t' → SN t') → SN t
-- (AGDA BUG : if SN is an inductive record, CR₃ fails termination check)

--------------------------------------------------------------------------------

neu : ∀ {Γ A} → Tm Γ A → Set
neu (var _) = ⊤
neu (_ ∙ _) = ⊤
neu (ƛ _)   = ⊥

--------------------------------------------------------------------------------

⟦_⟧ : (A : Ty) → ∀ {Γ} → Tm Γ A → Set
⟦ ⋆     ⟧ = SN
⟦ A ⇒ B ⟧ = λ f → SN f × (∀ a → ⟦ A ⟧ a → ⟦ B ⟧ (f ∙ a))


-- ∀ A → (⟦ A ⟧ is a reducibility candidate)
--------------------------------------------------------------------------------

mutual
  CR₁ : ∀ {Γ} {A t} → ⟦ A ⟧ {Γ} t → SN t
  CR₁ {A = ⋆}     = id
  CR₁ {A = A ⇒ B} = proj₁

  CR₂ : ∀ {Γ} {A t t'} → t ~> t' → ⟦ A ⟧ {Γ} t → ⟦ A ⟧ t'
  CR₂ {A = ⋆}     t~>t' (sn n)       = n t~>t'
  CR₂ {A = A ⇒ B} t~>t' (sn st , rt) = st t~>t' , λ a ra → CR₂ (∙₁ _ t~>t') (rt a ra)

  CR₃ : ∀ {Γ A}(t : Tm Γ A) → neu t → (∀ {t'} → t ~> t' → ⟦ A ⟧ t') → ⟦ A ⟧ t
  CR₃ {A = ⋆}     t nt cr₂ = sn cr₂
  CR₃ {A = A ⇒ B} t nt cr₂ = sn (proj₁ F.∘ cr₂) , λ a ra → CR₃ (t ∙ a) _ (go nt cr₂ a ra (CR₁ ra) _)
    where
      go :
        ∀ {Γ A B}{t : Tm Γ (A ⇒ B)} → neu t → (∀ {t'} → t ~> t' → ⟦ A ⇒ B ⟧ t')
        → ∀ a → ⟦ A ⟧ a → SN a → ∀ t' → t ∙ a ~> t' → ⟦ B ⟧ t'
      go () _   _ _  _        _ (β _ _)
      go nt cr₂ a ra sna      _ (∙₁ t' t~>t') = proj₂ (cr₂ t~>t') a ra
      go nt cr₃ a ra (sn sna) _ (∙₂ a' a~>a') =
        CR₃ (_ ∙ a') _ (go nt cr₃ a' (CR₂ a~>a' ra) (sna a~>a') _)

-- ⟦_⟧ is closed under abstraction
--------------------------------------------------------------------------------

abs' :
  ∀ {Γ A B} (a : Tm Γ A) (b : Tm (Γ ▷ A) B)
  → (∀ a → ⟦ A ⟧ a → ⟦ B ⟧ (sub vz a b))
  → ⟦ A ⟧ a → SN a → ⟦ B ⟧ (ƛ b ∙ a)
abs' {Γ}{A}{B} a b cr₃ ra sna = CR₃ (ƛ b ∙ a) _ (go a b cr₃ ra sna) where
  go :
    ∀ (a : Tm Γ A) (b : Tm (Γ ▷ A) B)
    → (∀ a → ⟦ A ⟧ a → ⟦ B ⟧ (sub vz a b)) → ⟦ A ⟧ a → SN a → ∀ {t'} → ƛ b ∙ a ~> t' → ⟦ B ⟧ t'
  go a b cr₃ ra sna      (β .b .a)           = cr₃ a ra
  go a b cr₃ ra sna      (∙₁ _ (ƛ b' b~>b')) = {!abs a b'!} -- ?
  go a b cr₃ ra (sn sna) (∙₂ a' a~>a')       = abs' a' b cr₃ (CR₂ a~>a' ra) (sna a~>a')

abs :
  ∀ {Γ A B} (a : Tm Γ A) (b : Tm (Γ ▷ A) B)
  → (∀ a → ⟦ A ⟧ a → ⟦ B ⟧ (sub vz a b))
  → ⟦ A ⟧ a → ⟦ B ⟧ (ƛ b ∙ a)
abs a b f ra = abs' a b f ra (CR₁ ra)

--------------------------------------------------------------------------------


-- Idea:
     -- Define susbstitutions generally
     -- Define renaming as special substitution
     -- Define the interpretation of "Sub Γ Δ" as a logical predicate

⟦_⟧ᶜ : Con → Set
⟦ ε     ⟧ᶜ = ⊤
⟦ Γ ▷ A ⟧ᶜ = ⟦ Γ ⟧ᶜ × ∃ (⟦ A ⟧ {Γ})

_[_]∈ : ∀ {Γ A} → A ∈ Γ → ⟦ Γ ⟧ᶜ → Tm Γ A
vz     [ γ , a , _  ]∈ = ren (add refl) a
(vs v) [ γ , _      ]∈ = ren (add refl) (v [ γ ]∈) 

_[_] : ∀ {Γ A} → Tm Γ A → ⟦ Γ ⟧ᶜ → Tm Γ A
var v       [ γ ] = v [ γ ]∈ 
(f ∙ x)     [ γ ] = f [ γ ] ∙ x [ γ ]
ƛ {A = A} t [ γ ] = {!!} -- ƛ (t [ γ , var  , CR₃ (var (vz {A})) _ (λ ()) ])

⟦∙⟧ :
  ∀ {Γ A B}{f : Tm Γ (A ⇒ B)}{x}
  → (γ : ⟦ Γ ⟧ᶜ) → ⟦ A ⇒ B ⟧ (f [ γ ]) → ⟦ A ⟧ (x [ γ ]) → ⟦ B ⟧ ((f ∙ x) [ γ ])
⟦∙⟧ γ ⟦f⟧ ⟦x⟧ = {!!}




⟦_⟧ᵗ : ∀ {Γ A} → (a : Tm Γ A) → (γ : ⟦ Γ ⟧ᶜ) → ⟦ A ⟧ (a [ γ ])
⟦ var v  ⟧ᵗ γ = {!!}
⟦ f ∙ x  ⟧ᵗ γ = ⟦∙⟧ γ (⟦ f ⟧ᵗ γ) ((⟦ x ⟧ᵗ γ))
⟦_⟧ᵗ  {Γ}{A ⇒ B}(ƛ t) γ =  
  -- t is reducible 
  {!!} , (λ a ⟦a⟧ → {!⟦ t ⟧ᵗ (γ , a , ⟦a⟧)!})



