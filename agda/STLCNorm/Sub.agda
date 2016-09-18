
module Sub where

open import Data.Product renaming (map to pmap)
open import Relation.Binary.PropositionalEquality
open import Data.Sum renaming (map to smap)
open import Function
open import Data.Unit
open import Data.Empty

-- STLC
--------------------------------------------------------------------------------

data Ty : Set where
  ⋆   : Ty
  _⇒_ : Ty → Ty → Ty
infixr 2 _⇒_

data Con : Set where
  ε   : Con
  _▷_ : Con → Ty → Con
infix 3 _▷_

data _∈_ (A : Ty) : Con → Set where
  vz  : ∀ {Γ} → A ∈ Γ ▷ A
  vs_ : ∀ {Γ B} → A ∈ Γ → A ∈ Γ ▷ B
infix 2 _∈_

data Tm Γ : Ty → Set where
  var : ∀ {A} → A ∈ Γ → Tm Γ A
  _∙_ : ∀ {A B} → Tm Γ (A ⇒ B) → Tm Γ A → Tm Γ B
  ƛ   : ∀ {A B} → Tm (Γ ▷ A) B → Tm Γ (A ⇒ B)
infixl 7 _∙_

-- Renaming
--------------------------------------------------------------------------------

data _⊆_ : Con → Con → Set where
  refl : ∀ {Γ} → Γ ⊆ Γ
  add  : ∀ {A Γ Δ} → Γ ⊆ Δ → Γ     ⊆ Δ ▷ A
  keep : ∀ {A Γ Δ} → Γ ⊆ Δ → Γ ▷ A ⊆ Δ ▷ A
infix 2 _⊆_

ren-∈ : ∀ {A Γ Δ} → Γ ⊆ Δ → A ∈ Γ → A ∈ Δ
ren-∈ refl     v      = v
ren-∈ (add r)  v      = vs ren-∈ r v
ren-∈ (keep r) vz     = vz
ren-∈ (keep r) (vs v) = vs ren-∈ r v

ren : ∀ {A Γ Δ} → Γ ⊆ Δ → Tm Γ A → Tm Δ A
ren r (var v) = var (ren-∈ r v)
ren r (f ∙ x) = ren r f ∙ ren r x
ren r (ƛ t)   = ƛ (ren (keep r) t)

-- Substitution
--------------------------------------------------------------------------------

data Sub (Γ : Con) : Con → Set where
  ε    : Sub Γ ε
  _▷_  : ∀ {A Δ} → Sub Γ Δ → Tm Γ A → Sub Γ (Δ ▷ A)

ren-Sub : ∀ {Γ Δ Ξ} → Γ ⊆ Ξ → Sub Γ Δ → Sub Ξ Δ
ren-Sub r ε       = ε
ren-Sub r (δ ▷ t) = ren-Sub r δ ▷ ren r t

wk : ∀ {A Γ Δ} → Sub Γ Δ → Sub (Γ ▷ A) (Δ ▷ A)
wk δ = ren-Sub (add refl) δ ▷ var vz

sub-∈ : ∀ {A Γ Δ} → Sub Γ Δ → A ∈ Δ → Tm Γ A
sub-∈ (δ ▷ t) vz     = t
sub-∈ (δ ▷ t) (vs v) = sub-∈ δ v

sub : ∀ {A Γ Δ} → Sub Γ Δ → Tm Δ A → Tm Γ A
sub δ (var v) = sub-∈ δ v
sub δ (f ∙ x) = sub δ f ∙ sub δ x
sub δ (ƛ t)   = ƛ (sub (wk δ) t)

idˢ : ∀ {Γ} → Sub Γ Γ
idˢ {ε}     = ε
idˢ {Γ ▷ A} = wk idˢ

inst : ∀ {Γ A B} → Tm Γ A → Tm (Γ ▷ A) B → Tm Γ B
inst t' t = sub (idˢ ▷ t') t

-- Reduction
--------------------------------------------------------------------------------

data _~>_ {Γ} : ∀ {A} → Tm Γ A → Tm Γ A → Set where
  β  : ∀ {A B}(t : Tm (Γ ▷ A) B) t'                →  ƛ t ∙ t' ~> inst t' t
  ƛ  : ∀ {A B}{t : Tm (Γ ▷ A) B} t'      → t ~> t' →  ƛ t      ~> ƛ t'
  ∙₁ : ∀ {A B}{f} (f' : Tm Γ (A ⇒ B)){x} → f ~> f' →  (f ∙ x)  ~> (f' ∙ x)
  ∙₂ : ∀ {A B}{f : Tm Γ (A ⇒ B)} {x} x'  → x ~> x' →  (f ∙ x)  ~> (f ∙ x')
infix 3 _~>_

-- Strong normalization
--------------------------------------------------------------------------------

data SN {Γ A} (t : Tm Γ A) : Set where
  sn : (∀ {t'} → t ~> t' → SN t') → SN t
-- (AGDA BUG : if SN is an inductive record, CR₃ fails termination check)

runSN : ∀ {Γ A}{t : Tm Γ A} → SN t → (∀ {t'} → t ~> t' → SN t')
runSN (sn s) = s

neu : ∀ {Γ A} → Tm Γ A → Set
neu (var _) = ⊤
neu (_ ∙ _) = ⊤
neu (ƛ _)   = ⊥

-- Reducibility
--------------------------------------------------------------------------------

⟦_⟧ : (A : Ty) → ∀ {Γ} → Tm Γ A → Set
⟦ ⋆     ⟧ = SN
⟦ A ⇒ B ⟧ = λ f → SN f × (∀ {a} → ⟦ A ⟧ a → ⟦ B ⟧ (f ∙ a))

-- ⟦ A ⟧ is a reducibility candidate for all A (TODO : factor out CR to record)
--------------------------------------------------------------------------------

mutual
  CR₁ : ∀ {A Γ t} → ⟦ A ⟧ {Γ} t → SN t
  CR₁ {⋆}     = id
  CR₁ {A ⇒ B} = proj₁

  CR₂ : ∀ {A Γ t t'} → t ~> t' → ⟦ A ⟧ {Γ} t → ⟦ A ⟧ t'
  CR₂ {⋆}     t~>t' (sn nt)       = nt t~>t'
  CR₂ {A ⇒ B} t~>t' (sn st , ⟦t⟧) = st t~>t' , λ ⟦a⟧ → CR₂ (∙₁ _ t~>t') (⟦t⟧ ⟦a⟧)

  CR₃ : ∀ {A Γ}(t : Tm Γ A) → neu t → (∀ {t'} → t ~> t' → ⟦ A ⟧ t') → ⟦ A ⟧ t
  CR₃ {⋆}     t nt f = sn f
  CR₃ {A ⇒ B} t nt f = sn (proj₁ ∘ f) , λ ⟦a⟧ → CR₃ _ _ (go nt f ⟦a⟧ (CR₁ ⟦a⟧) _)
    where
      go :
        ∀ {A B Γ}{t : Tm Γ (A ⇒ B)} → neu t → (∀ {t'} → t ~> t' → ⟦ A ⇒ B ⟧ t')
        → ∀ {a} → ⟦ A ⟧ a → SN a → ∀ t' → t ∙ a ~> t' → ⟦ B ⟧ t'
      go () _ _   _        _ (β _ _)
      go nt f ⟦a⟧ sna      _ (∙₁ t' t~>t') = proj₂ (f t~>t') ⟦a⟧
      go nt f ⟦a⟧ (sn sna) _ (∙₂ a' a~>a') =
        CR₃ (_ ∙ a') _ (go nt f (CR₂ a~>a' ⟦a⟧) (sna a~>a') _)

-- Substitutions of SN terms
--------------------------------------------------------------------------------

SNᶜ : ∀ {Γ Δ} → Sub Γ Δ → Set
SNᶜ ε       = ⊤
SNᶜ (δ ▷ t) = SNᶜ δ × SN t

IsRen : ∀ {Γ Δ} → Sub Γ Δ → Set
IsRen ε           = ⊤
IsRen (δ ▷ var _) = IsRen δ
IsRen (δ ▷ _ ∙ _) = ⊥
IsRen (δ ▷ ƛ _)   = ⊥

IsRen-SNᶜ : ∀ {Γ Δ δ} → IsRen {Γ}{Δ} δ → SNᶜ δ
IsRen-SNᶜ {δ = ε}         _ = _
IsRen-SNᶜ {δ = δ ▷ var x} p = IsRen-SNᶜ p , (sn λ ())
IsRen-SNᶜ {δ = δ ▷ _ ∙ _} ()
IsRen-SNᶜ {δ = δ ▷ ƛ _}   ()

IsRen-ren : ∀ {Γ Δ Ξ}(r : Γ ⊆ Ξ){δ} → IsRen {Γ}{Δ} δ → IsRen (ren-Sub r δ)
IsRen-ren r {ε}     rδ = tt
IsRen-ren r {δ ▷ var _} rδ = IsRen-ren r {δ} rδ
IsRen-ren r {δ ▷ _ ∙ _} rδ = rδ
IsRen-ren r {δ ▷ ƛ _}   rδ = rδ

idˢ-IsRen : ∀ {Γ} → IsRen (idˢ {Γ})
idˢ-IsRen {ε}     = tt
idˢ-IsRen {Γ ▷ A} = IsRen-ren (add refl){idˢ {Γ}} (idˢ-IsRen {Γ})

idˢ-SN : ∀ {Γ} → SNᶜ (idˢ {Γ})
idˢ-SN {Γ} = IsRen-SNᶜ (idˢ-IsRen {Γ})

-- Constructors and substitution preserve strong normalization
--------------------------------------------------------------------------------

ƛ-SN→ : ∀ {Γ A B}{t : Tm (Γ ▷ A) B} → SN t → SN (ƛ t)
ƛ-SN→ (sn s) = sn λ {(ƛ _ t~>t') → ƛ-SN→ (s t~>t')}

ƛ-SN← : ∀ {Γ A B}{t : Tm (Γ ▷ A) B} → SN (ƛ t) → SN t
ƛ-SN← (sn s) = sn λ t~>t' → ƛ-SN← (s (ƛ _ t~>t'))

∙-SN← : ∀ {Γ A B}{f : Tm Γ (A ⇒ B)}{x} → SN (f ∙ x) → SN f × SN x
∙-SN← (sn s) =
  sn (λ f~>f' → proj₁ (∙-SN← (s (∙₁ _ f~>f')))) ,
  sn (λ x~>x' → proj₂ (∙-SN← (s (∙₂ _ x~>x'))))


-- -- Renaming preserves reduction
-- --------------------------------------------------------------------------------

-- ren~>-→ : ∀ {Γ Δ A}(r : Γ ⊆ Δ){t t' : Tm Γ A} → t ~> t' → ren r t ~> ren r t'
-- ren~>-→ r (β t t') rewrite ren-sub (keep r) vz t' t = β (ren (keep r) t) (ren r t')
-- ren~>-→ r (ƛ t' t~>t')  = ƛ (ren (keep r) t') (ren~>-→ (keep r) t~>t')
-- ren~>-→ r (∙₁ f' f~>f') = ∙₁ (ren r f') (ren~>-→ r f~>f')
-- ren~>-→ r (∙₂ x' x~>x') = ∙₂ (ren r x') (ren~>-→ r x~>x')

-- ren~>-str : ∀ {Γ Δ A}(r : Γ ⊆ Δ){t : Tm Γ A}{t'} → ren r t ~> t' → ∃ λ t'' → t' ≡ ren r t''
-- ren~>-str r {var x} ()
-- ren~>-str r {ƛ f ∙ x} (β _ _) =
--   sub vz x f , (sym $ ren-sub (keep r) vz x f)
-- ren~>-str r {var v ∙ x} (∙₁ f' ())
-- ren~>-str r {var v ∙ x} (∙₂ x' rt~>t') =
--   pmap (var v ∙_) (cong (var (ren-∈ r v) ∙_)) (ren~>-str r rt~>t')
-- ren~>-str r {f ∙ x ∙ y} (∙₁ f' rt~>t') =
--   pmap (_∙ y) (cong (_∙ ren r y)) (ren~>-str r rt~>t')
-- ren~>-str r {f ∙ x ∙ y} (∙₂ x' rt~>t') =
--   pmap ((f ∙ x) ∙_) (cong ((ren r f ∙ ren r x) ∙_)) (ren~>-str r rt~>t')
-- ren~>-str r {ƛ f ∙ x} (∙₁ _ (ƛ t' rt~>t')) =
--   pmap (λ t'' → ƛ t'' ∙ x) (cong (λ t' → ƛ t' ∙ ren r x)) (ren~>-str (keep r) rt~>t')
-- ren~>-str r {ƛ f ∙ x} (∙₂ x' rt~>t') =
--   pmap (ƛ f ∙_) (cong (ƛ (ren (keep r) f) ∙_)) (ren~>-str r rt~>t')
-- ren~>-str r {ƛ t}   (ƛ t' rt~>t') =
--   pmap ƛ (cong ƛ) (ren~>-str (keep r) rt~>t')

-- ren~>-← : ∀ {Γ Δ A}(r : Γ ⊆ Δ){t t' : Tm Γ A} → ren r t ~> ren r t' → t ~> t'
-- ren~>-← r = go r refl where

--   go : ∀ {Γ Δ A}(r : Γ ⊆ Δ){t t' : Tm Γ A}{t''} → t'' ≡ ren r t' → ren r t ~> t'' → t ~> t'

--   go r {var v ∙ x} {t' ∙ t''} eq (∙₂ x' rt~>rt') with ren~>-str r rt~>rt'
--   go r {var v ∙ x} {t' ∙ t''} eq (∙₂ _ rt~>rt') | x'' , refl
--     rewrite sym $ ren-inj r eq = ∙₂ x'' (go r refl rt~>rt')

--   go r {f ∙ x ∙ y} eq (∙₁ f' rt~>rt') with ren~>-str r rt~>rt'
--   go r {f ∙ x ∙ y} eq (∙₁ _ rt~>rt') | t'' , refl
--     rewrite sym $ ren-inj r eq = ∙₁ t'' (go r refl rt~>rt')

--   go r {f ∙ x ∙ y} eq (∙₂ x' rt~>rt') with ren~>-str r rt~>rt'
--   go r {f ∙ x ∙ y} eq (∙₂ _  rt~>rt') | x'' , refl
--     rewrite sym $ ren-inj r eq = ∙₂ x'' (go r refl rt~>rt')

--   go r {ƛ f ∙ x} eq (β _ _) =
--     subst (_ ~>_) (ren-inj r (trans (ren-sub (keep r) vz x f) eq)) (β f x)

--   go r {ƛ f ∙ x} eq (∙₁ _ (ƛ t' rt~>rt')) with ren~>-str (keep r) rt~>rt'
--   go r {ƛ f ∙ x} eq (∙₁ _ (ƛ _ rt~>rt')) | f' , refl
--     rewrite sym $ ren-inj r eq = ∙₁ _ (ƛ _ (go (keep r) refl rt~>rt'))

--   go r {ƛ f ∙ x} eq (∙₂ x' rt~>rt') with ren~>-str r rt~>rt'
--   go r {ƛ f ∙ x} eq (∙₂ _  rt~>rt') | x'' , refl
--     rewrite sym $ ren-inj r eq = ∙₂ x'' (go r refl rt~>rt')

--   go r {ƛ t} {ƛ t'} eq (ƛ _ rt~>rt') =
--     ƛ t' (go (keep r) (ƛ-inj eq) rt~>rt')

--   go r {var x} eq ()
--   go r {var v ∙ x} eq (∙₁ f' ())
--   go r {var v ∙ x} {var x₁} () (∙₂ x' rt~>rt')
--   go r {var v ∙ x} {ƛ t'} () (∙₂ x' rt~>rt')
--   go r {ƛ t} {var x} () (ƛ t' rt~>rt')
--   go r {ƛ t} {t'' ∙ t'''} () (ƛ t' rt~>rt')


-- -- Renaming preserves strong normalization
-- --------------------------------------------------------------------------------

-- ren-SN→ : ∀ {Γ Δ A} (r : Γ ⊆ Δ)(t : Tm Γ A) → SN (ren r t) → SN t
-- ren-SN→ r t (sn snt) = sn (λ {t'} t~>t' → ren-SN→ r t' (snt (ren~>-→ r t~>t')))

-- ren-SN← : ∀ {Γ Δ A} (r : Γ ⊆ Δ)(t : Tm Γ A) → SN t → SN (ren r t)
-- ren-SN← {Γ}{Δ}{A} r t snt = sn (go t snt) where
--   go : ∀ t → SN t → ∀ {t' : Tm Δ A} → ren r t ~> t' → SN t'
--   go t (sn snt) rt~>t' with ren~>-str r rt~>t'
--   ... | t'' , refl = ren-SN← r t'' (snt (ren~>-← r rt~>t'))



--------------------------------------------------------------------------------


⟦_⟧ˢ : ∀ {Γ Δ} → Sub Γ Δ → Set
⟦ ε     ⟧ˢ = ⊤
⟦ δ ▷ t ⟧ˢ = ⟦ δ ⟧ˢ × ⟦ _ ⟧ t

⟦var⟧ : ∀ {A Γ} → (v : A ∈ Γ) → ⟦ A ⟧ (var v)
⟦var⟧ v = CR₃ (var v) _ (λ ())

⟦sub-∈⟧ : ∀ {A Γ Δ}{δ : Sub Δ Γ} → ⟦ δ ⟧ˢ → (v : A ∈ Γ) → ⟦ A ⟧ (sub-∈ δ v)
⟦sub-∈⟧ {δ = δ ▷ t} (_   , ⟦t⟧) vz     = ⟦t⟧
⟦sub-∈⟧ {δ = δ ▷ t} (⟦δ⟧ , _)   (vs v) = ⟦sub-∈⟧ ⟦δ⟧ v

⟦∙⟧→ : ∀ {A B Γ}{f : Tm Γ (A ⇒ B)}{x} → ⟦ A ⇒ B ⟧ f → ⟦ A ⟧ x → ⟦ B ⟧ (f ∙ x)
⟦∙⟧→ ⟦f⟧ ⟦x⟧ = proj₂ ⟦f⟧ ⟦x⟧

⟦ren⟧ : ∀ {Γ Δ A}(r : Γ ⊆ Δ){t : Tm Γ A} → ⟦ A ⟧ t → ⟦ A ⟧ (ren r t)
⟦ren⟧ r {t} ⟦t⟧ = {!!}

⟦ren-Sub⟧ : ∀ {Γ Δ Ξ}{δ : Sub Γ Δ} → ⟦ δ ⟧ˢ → (r : Γ ⊆ Ξ) → ⟦ ren-Sub r δ ⟧ˢ
⟦ren-Sub⟧ {δ = ε}     ⟦δ⟧         r = tt
⟦ren-Sub⟧ {δ = δ ▷ t} (⟦δ⟧ , ⟦t⟧) r = ⟦ren-Sub⟧ ⟦δ⟧ r , ⟦ren⟧ r {t} ⟦t⟧

⟦wk⟧ : ∀ {A Γ Δ}{δ : Sub Γ Δ} → ⟦ δ ⟧ˢ → ⟦ wk {A} δ ⟧ˢ
⟦wk⟧ {A} ⟦δ⟧ = ⟦ren-Sub⟧ ⟦δ⟧ (add refl) , ⟦var⟧ {A} vz

⟦ƛ⟧ :
  ∀ {A B Γ Δ}{δ : Sub Γ Δ}{t : Tm (Δ ▷ A) B}
  → ⟦ δ ⟧ˢ → ∀ {a} → ⟦ A ⟧ a
  → ⟦ B ⟧ (sub (δ ▷ a) t)
  → ⟦ B ⟧ (ƛ (sub (wk δ) t) ∙ a)
⟦ƛ⟧ ⟦δ⟧ ⟦a⟧ ⟦t⟧ = {!!}

⟦_⟧ᵗ : ∀ {A Γ Δ}(t : Tm Γ A) → {δ : Sub Δ Γ} → ⟦ δ ⟧ˢ → ⟦ A ⟧ (sub δ t)
⟦ var v ⟧ᵗ ⟦δ⟧ = ⟦sub-∈⟧ ⟦δ⟧ v
⟦ f ∙ x ⟧ᵗ ⟦δ⟧ = ⟦∙⟧→ (⟦ f ⟧ᵗ ⟦δ⟧) (⟦ x ⟧ᵗ ⟦δ⟧)
⟦ ƛ t   ⟧ᵗ ⟦δ⟧ =
  ƛ-SN→ (CR₁ (⟦ t ⟧ᵗ (⟦wk⟧ ⟦δ⟧))) ,
  λ ⟦a⟧ → ⟦ƛ⟧ ⟦δ⟧ ⟦a⟧ (⟦ t ⟧ᵗ (⟦δ⟧ , ⟦a⟧))


