
module Norm where

open import Basic hiding (_∘_)

open import Data.Product renaming (map to pmap)
open import Relation.Binary.PropositionalEquality
open import Data.Sum renaming (map to smap)
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

-- Reducibility
--------------------------------------------------------------------------------

RED : {A : Ty} → ∀ {Γ} (t : Tm Γ A) → Set
RED {⋆}     = SN
RED {A ⇒ B} = λ f → SN f × (∀ a → RED a → RED (f ∙ a))

-- Properties of reducibility candidates
--------------------------------------------------------------------------------

neu : ∀ {Γ A} → Tm Γ A → Set
neu (var _) = ⊤
neu (_ ∙ _) = ⊤
neu (ƛ _)   = ⊥

mutual
  CR₁ : ∀ {Γ} {A t} → RED {A}{Γ} t → SN t
  CR₁ {A = ⋆}     = id
  CR₁ {A = A ⇒ B} = proj₁

  CR₂ : ∀ {Γ} {A t t'} → t ~> t' → RED {A}{Γ} t → RED t'
  CR₂ {A = ⋆}     t~>t' (sn n)       = n t~>t'
  CR₂ {A = A ⇒ B} t~>t' (sn st , rt) = st t~>t' , λ a ra → CR₂ (∙₁ _ t~>t') (rt a ra)

  CR₃ : ∀ {Γ A}(t : Tm Γ A) → neu t → (∀ {t'} → t ~> t' → RED {A} t') → RED t
  CR₃ {A = ⋆}     t nt cr₂ = sn cr₂
  CR₃ {A = A ⇒ B} t nt cr₂ = sn (proj₁ F.∘ cr₂) , λ a ra → CR₃ (t ∙ a) _ (go nt cr₂ a ra (CR₁ ra) _)
    where
      go :
        ∀ {Γ A B}{t : Tm Γ (A ⇒ B)} → neu t → (∀ {t'} → t ~> t' → RED {A ⇒ B} t')
        → ∀ a → RED a → SN a → ∀ t' → t ∙ a ~> t' → RED t'
      go () _   _ _  _        _ (β _ _)
      go nt cr₂ a ra sna      _ (∙₁ t' t~>t') = proj₂ (cr₂ t~>t') a ra
      go nt cr₃ a ra (sn sna) _ (∙₂ a' a~>a') =
        CR₃ (_ ∙ a') _ (go nt cr₃ a' (CR₂ a~>a' ra) (sna a~>a') _)

-- Abstraction lemma
--------------------------------------------------------------------------------

lem :
  ∀ {Γ A B}(v : A ∈ Γ)(a : Tm (drop v) A)(b b' : Tm Γ B)
  → RED a
  → RED (sub v a b) → b ~> b' → RED (sub v a b')
lem v a _ _ rb ra (β t t')      = {!!}
lem v a _ _ rb ra (ƛ t' b~>b')  = {!!}
lem v a _ _ rb ra (∙₁ f' b~>b') = {!!}
lem v a _ _ rb ra (∙₂ x' b~>b') = {!!}




-- abs :
--   ∀ {Γ A B} (a : Tm Γ A) (b : Tm (Γ ▷ A) B)
--   → (∀ a → RED a → RED (sub vz a b))
--   → RED b → SN b
--   → RED a → SN a → RED (ƛ b ∙ a)
-- abs {Γ}{A}{B} a b cr₃ rb snb ra sna = CR₃ (ƛ b ∙ a) _ (go a b cr₃ rb snb ra sna) where
--   go :
--     ∀ (a : Tm Γ A) (b : Tm (Γ ▷ A) B)
--     → (∀ a → RED a → RED (sub vz a b)) → RED b → SN b → RED a → SN a → ∀ {t'} → ƛ b ∙ a ~> t' → RED t'
--   go a b cr₃ rb snb ra sna      (β .b .a)           = cr₃ a ra
--   go a b cr₃ rb (sn snb) ra sna (∙₁ _ (ƛ b' b~>b')) =
--     abs a b' (λ a' ra' → {!!}) (CR₂ b~>b' rb) (snb b~>b') ra sna
--   go a b cr₃ rb snb ra (sn sna) (∙₂ a' a~>a')       = abs a' b cr₃ rb snb (CR₂ a~>a' ra) (sna a~>a')

-- abs :
--   ∀ {Γ A B} (a : Tm Γ A) (b : Tm (Γ ▷ A) B)
--   → (∀ a → RED a → RED (sub vz a b))
--   → RED a → SN a → RED (ƛ b ∙ a)
-- abs {Γ}{A}{B} a b cr₃ ra sna = CR₃ (ƛ b ∙ a) _ (go a b cr₃ ra sna) where
--   go :
--     ∀ (a : Tm Γ A) (b : Tm (Γ ▷ A) B)
--     → (∀ a → RED a → RED (sub vz a b)) → RED a → SN a → ∀ {t'} → ƛ b ∙ a ~> t' → RED t'
--   go a b cr₃ ra sna      (β .b .a)           = cr₃ a ra
--   go a b cr₃ ra sna      (∙₁ _ (ƛ b' b~>b')) = {!abs a b'!}
--   go a b cr₃ ra (sn sna) (∙₂ a' a~>a')       = abs a' b cr₃ (CR₂ a~>a' ra) (sna a~>a')

