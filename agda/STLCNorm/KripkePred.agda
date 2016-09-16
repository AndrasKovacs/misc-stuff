
module KripkePred where

open import Basic

open import Data.Product renaming (map to pmap)
open import Relation.Binary.PropositionalEquality
open import Data.Sum renaming (map to smap)
open import Function using (_$_)
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
RED {A ⇒ B} = λ f → ∀ a → RED a → RED (f ∙ a)

-- Renaming preserves reduction
--------------------------------------------------------------------------------

ren~>-→ : ∀ {Γ Δ A}(r : Γ ⊆ Δ){t t' : Tm Γ A} → t ~> t' → ren r t ~> ren r t'
ren~>-→ r (β t t') rewrite ren-sub (keep r) vz t' t = β (ren (keep r) t) (ren r t')
ren~>-→ r (ƛ t' t~>t')  = ƛ (ren (keep r) t') (ren~>-→ (keep r) t~>t')
ren~>-→ r (∙₁ f' f~>f') = ∙₁ (ren r f') (ren~>-→ r f~>f')
ren~>-→ r (∙₂ x' x~>x') = ∙₂ (ren r x') (ren~>-→ r x~>x')

ren~>-str : ∀ {Γ Δ A}(r : Γ ⊆ Δ){t : Tm Γ A}{t'} → ren r t ~> t' → ∃ λ t'' → t' ≡ ren r t''
ren~>-str r {var x} ()
ren~>-str r {ƛ f ∙ x} (β _ _) =
  sub vz x f , (sym $ ren-sub (keep r) vz x f)
ren~>-str r {var v ∙ x} (∙₁ f' ())
ren~>-str r {var v ∙ x} (∙₂ x' rt~>t') =
  pmap (var v ∙_) (cong (var (ren-∈ r v) ∙_)) (ren~>-str r rt~>t')
ren~>-str r {f ∙ x ∙ y} (∙₁ f' rt~>t') =
  pmap (_∙ y) (cong (_∙ ren r y)) (ren~>-str r rt~>t')
ren~>-str r {f ∙ x ∙ y} (∙₂ x' rt~>t') =
  pmap ((f ∙ x) ∙_) (cong ((ren r f ∙ ren r x) ∙_)) (ren~>-str r rt~>t')
ren~>-str r {ƛ f ∙ x} (∙₁ _ (ƛ t' rt~>t')) =
  pmap (λ t'' → ƛ t'' ∙ x) (cong (λ t' → ƛ t' ∙ ren r x)) (ren~>-str (keep r) rt~>t')
ren~>-str r {ƛ f ∙ x} (∙₂ x' rt~>t') =
  pmap (ƛ f ∙_) (cong (ƛ (ren (keep r) f) ∙_)) (ren~>-str r rt~>t')
ren~>-str r {ƛ t}   (ƛ t' rt~>t') =
  pmap ƛ (cong ƛ) (ren~>-str (keep r) rt~>t')

ren~>-← : ∀ {Γ Δ A}(r : Γ ⊆ Δ){t t' : Tm Γ A} → ren r t ~> ren r t' → t ~> t'
ren~>-← r = go r refl where

  go : ∀ {Γ Δ A}(r : Γ ⊆ Δ){t t' : Tm Γ A}{t''} → t'' ≡ ren r t' → ren r t ~> t'' → t ~> t'

  go r {var v ∙ x} {t' ∙ t''} eq (∙₂ x' rt~>rt') with ren~>-str r rt~>rt'
  go r {var v ∙ x} {t' ∙ t''} eq (∙₂ _ rt~>rt') | x'' , refl
    rewrite sym $ ren-inj r eq = ∙₂ x'' (go r refl rt~>rt')

  go r {f ∙ x ∙ y} eq (∙₁ f' rt~>rt') with ren~>-str r rt~>rt'
  go r {f ∙ x ∙ y} eq (∙₁ _ rt~>rt') | t'' , refl
    rewrite sym $ ren-inj r eq = ∙₁ t'' (go r refl rt~>rt')

  go r {f ∙ x ∙ y} eq (∙₂ x' rt~>rt') with ren~>-str r rt~>rt'
  go r {f ∙ x ∙ y} eq (∙₂ _  rt~>rt') | x'' , refl
    rewrite sym $ ren-inj r eq = ∙₂ x'' (go r refl rt~>rt')

  go r {ƛ f ∙ x} eq (β _ _) =
    subst (_ ~>_) (ren-inj r (trans (ren-sub (keep r) vz x f) eq)) (β f x)

  go r {ƛ f ∙ x} eq (∙₁ _ (ƛ t' rt~>rt')) with ren~>-str (keep r) rt~>rt'
  go r {ƛ f ∙ x} eq (∙₁ _ (ƛ _ rt~>rt')) | f' , refl
    rewrite sym $ ren-inj r eq = ∙₁ _ (ƛ _ (go (keep r) refl rt~>rt'))

  go r {ƛ f ∙ x} eq (∙₂ x' rt~>rt') with ren~>-str r rt~>rt'
  go r {ƛ f ∙ x} eq (∙₂ _  rt~>rt') | x'' , refl
    rewrite sym $ ren-inj r eq = ∙₂ x'' (go r refl rt~>rt')

  go r {ƛ t} {ƛ t'} eq (ƛ _ rt~>rt') =
    ƛ t' (go (keep r) (ƛ-inj eq) rt~>rt')

  go r {var x} eq ()
  go r {var v ∙ x} eq (∙₁ f' ())
  go r {var v ∙ x} {var x₁} () (∙₂ x' rt~>rt')
  go r {var v ∙ x} {ƛ t'} () (∙₂ x' rt~>rt')
  go r {ƛ t} {var x} () (ƛ t' rt~>rt')
  go r {ƛ t} {t'' ∙ t'''} () (ƛ t' rt~>rt')


-- Renaming preserves strong normalization
--------------------------------------------------------------------------------

ren-SN→ : ∀ {Γ Δ A} (r : Γ ⊆ Δ)(t : Tm Γ A) → SN (ren r t) → SN t
ren-SN→ r t (sn snt) = sn (λ {t'} t~>t' → ren-SN→ r t' (snt (ren~>-→ r t~>t')))

ren-SN← : ∀ {Γ Δ A} (r : Γ ⊆ Δ)(t : Tm Γ A) → SN t → SN (ren r t)
ren-SN← {Γ}{Δ}{A} r t snt = sn (go t snt) where
  go : ∀ t → SN t → ∀ {t' : Tm Δ A} → ren r t ~> t' → SN t'
  go t (sn snt) rt~>t' with ren~>-str r rt~>t'
  ... | t'' , refl = ren-SN← r t'' (snt (ren~>-← r rt~>t'))

-- Renaming preserves reducibility
--------------------------------------------------------------------------------




-- ren-∈-RED← : ∀ {Γ Δ A}(r : Γ ⊆ Δ){v : A ∈ Γ} → RED (var v) → RED (var (ren-∈ r v))
-- ren-∈-RED← {A = ⋆}     r rv = sn (λ ())
-- ren-∈-RED← {A = A ⇒ B} r rv = {!!}

-- ren-RED← : ∀ {Γ Δ A}(r : Γ ⊆ Δ)(t : Tm Γ A) → RED t → RED (ren r t)
-- ren-RED← r (var v) rt = ren-∈-RED← r {v} rt
-- ren-RED← r (f ∙ x) rt = {!ren-RED← r f!}
-- ren-RED← r (ƛ t)   rt = {!!}

-- ren-RED← : ∀ {Γ Δ A}(r : Γ ⊆ Δ)(t : Tm Γ A) → RED t → RED (ren r t)
-- ren-RED← {A = ⋆}                   = ren-SN←
-- ren-RED← {Γ} {Δ} {A ⇒ B} r (var v) rt a ra = {!!}
-- ren-RED← {Γ} {Δ} {A ⇒ B} r (f ∙ x) rt a ra = {!!}
-- ren-RED← {Γ} {Δ} {A ⇒ B} r (ƛ t)   rt a ra = {!!}

-- ren-RED→ : ∀ {Γ Δ A}(r : Γ ⊆ Δ)(t : Tm Γ A) → RED (ren r t) → RED t
-- ren-RED→ {A = ⋆}     = ren-SN→
-- ren-RED→ {A = A ⇒ B} = λ r t rt a ra → ren-RED→ r (t ∙ a) (rt (ren r a) (ren-RED← r a ra))



-- Properties of reducibility candidates
--------------------------------------------------------------------------------

neu : ∀ {Γ A} → Tm Γ A → Set
neu (var _) = ⊤
neu (_ ∙ _) = ⊤
neu (ƛ _)   = ⊥

mutual

  CR₁ : ∀ {Γ} {A t} → RED {A}{Γ} t → SN t
  CR₁ {A = ⋆}     rt = rt


  CR₁ {A = A ⇒ B} {f} rf = {!!} where

  -- 1. RED f
  -- 2. RED (ren (add refl) f)
  -- 3. (RED (ren (add refl) f ∙ var vz) --> SN (ren (add refl) f ∙ var vz))
  -- 4. (SN (ren (add refl) f ∙ var vz) --> SN (ren (add refl) f))
  -- 5. SN (ren (add refl) f)
  -- 6. SN f

    -- lem1 : ∀ {Γ A B}(t : Tm (Γ ▷ A) (A ⇒ B)) → RED t → RED (t ∙ var vz)
    -- lem1 {A = A} t rt = rt (var vz) (CR₃ (var {A = A} vz) tt (λ ()))

    lem2 : ∀ {Γ A B}{f : Tm Γ (A ⇒ B)}{x} → SN (f ∙ x) → SN f
    lem2 (sn s) = sn (λ f~>f' → lem2 (s (∙₁ _ f~>f')))



  CR₂ : ∀ {Γ} {A t t'} → t ~> t' → RED {A}{Γ} t → RED t'
  CR₂ {A = ⋆}     t~>t' (sn n) = n t~>t'
  CR₂ {A = A ⇒ B} t~>t' rf     = λ a ra → CR₂ (∙₁ _ t~>t') (rf a ra)

  CR₃ : ∀ {Γ A}(t : Tm Γ A) → neu t → (∀ {t'} → t ~> t' → RED {A} t') → RED t
  CR₃ {A = ⋆}     t nt cr₂ = sn cr₂
  CR₃ {A = A ⇒ B} t nt cr₂ = λ a ra → go t nt cr₂ a ra (CR₁ ra) where
    mutual
      go :
        ∀ {Γ A B} (t : Tm Γ (A ⇒ B)) → neu t → (∀ {t'} → t ~> t' → RED {A ⇒ B} t')
        → ∀ a → RED a → SN a → RED (t ∙ a)
      go t nt cr₂ a ra sna = CR₃ (t ∙ a) tt (go' nt cr₂ a ra sna _)

      go' :
        ∀ {Γ A B}{t : Tm Γ (A ⇒ B)} → neu t → (∀ {t'} → t ~> t' → RED {A ⇒ B} t')
        → ∀ a → RED a → SN a → ∀ t' → t ∙ a ~> t' → RED t'
      go' () _ _ _ _ _ (β _ _)
      go' nt cr₂ a ra sna      _ (∙₁ t' t~>t') = cr₂ t~>t' a ra
      go' nt cr₂ a ra (sn sna) _ (∙₂ a' a~>a') = go _ nt cr₂ a' (CR₂ a~>a' ra) (sna a~>a')

