{-# OPTIONS --without-K --rewriting #-}

open import Basics
open import Function

postulate
  S¹   : Set
  base : S¹
  loop : base ≡ base

  S¹-elim :
    ∀ {α}(P : S¹ → Set α)(base* : P base)(loop* : base* ≡[ ap P loop ] base*)(s : S¹)
    → P s

postulate
  β-base :
    ∀ {α}(P : S¹ → Set α)(base* : P base)(loop* : base* ≡[ ap P loop ] base*)
    → S¹-elim P base* loop* base ≡ base*
{-# REWRITE β-base #-}

postulate
  β-loop :
    ∀ {α}(P : S¹ → Set α)(base* : P base)(loop* : base* ≡[ ap P loop ] base*)
    → apd (S¹-elim P base* loop*) loop ≡ loop*

trans-const :
  ∀ {i j}{A : Set i}{B : Set j}{b b' : B} a
  → (p : b ≡ b') → trans (const A) p a ≡ a
trans-const _ refl = refl

postulate
  S¹-rec : ∀ {α}{A : Set α} (base* : A) → base* ≡ base* → S¹ → A
  β-base-rec :
    ∀ {α}{A : Set α} (base* : A)(loop* : base* ≡ base*)(s : S¹)
    → S¹-rec base* loop* base ≡ base*
  {-# REWRITE β-base-rec #-}

postulate
  β-loop-rec :
    ∀ {α}{A : Set α} (base* : A)(loop* : base* ≡ base*)
    → ap (S¹-rec base* loop*) loop ≡ loop*

-- β-loop-rec' :
--   ∀ {α}{A : Set α} (base* : A)(loop* : base* ≡ base*)
--   → ap (S¹-rec base* loop*) loop ≡ loop*
-- β-loop-rec' base* loop* s = {!!}

-- TODO: how can I prove β-loop-rec from β-loop?

-- refl ≢ loop (i. e. ¬ IsSet S¹)
--------------------------------------------------------------------------------

open import Data.Bool
open import Function
open import Data.Product

notEqv : Bool ~ Bool
notEqv = not , not ,
 (λ {true → refl; false → refl}) , ((λ {true → refl; false → refl}))

f : S¹ → Set
f = S¹-rec Bool (ua notEqv)

g : base ≡ base → Bool → Bool
g p = trans f p

gloop : g loop ≡ not
gloop = ap coe (β-loop-rec Bool (ua notEqv)) ∙ ap ⟶ (ua-β notEqv)

p : loop ≢ refl
p eq with ap (_$ true) (gloop ⁻¹ ∙ ap g eq)
... | ()





