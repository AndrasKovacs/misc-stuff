
module Sub4 where

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

-- Sub
--------------------------------------------------------------------------------

drop : ∀ {Γ A} → A ∈ Γ → Con
drop {Γ ▷ _} vz     = Γ
drop         (vs v) = drop v

drop-⊆ : ∀ {Γ A} (v : A ∈ Γ) → drop v ⊆ Γ
drop-⊆ vz     = add refl
drop-⊆ (vs v) = add (drop-⊆ v)

⊆-drop : ∀ {Γ Δ A}(v : A ∈ Γ)(r : Γ ⊆ Δ) → drop v ⊆ drop (ren-∈ r v)
⊆-drop v      refl     = refl
⊆-drop v      (add r)  = ⊆-drop v r
⊆-drop vz     (keep r) = r
⊆-drop (vs v) (keep r) = ⊆-drop v r

subᶜ : ∀ {Γ A} → A ∈ Γ → Con
subᶜ {Γ ▷ _} vz    = Γ
subᶜ {Γ ▷ A}(vs v) = subᶜ v ▷ A

⊆-subᶜ : ∀ {Γ Δ A}(v : A ∈ Γ)(r : Γ ⊆ Δ) → subᶜ v ⊆ subᶜ (ren-∈ r v)
⊆-subᶜ v      refl     = refl
⊆-subᶜ v      (add r)  = add (⊆-subᶜ v r)
⊆-subᶜ vz     (keep r) = r
⊆-subᶜ (vs v) (keep r) = keep (⊆-subᶜ v r)

∈-eq : ∀ {A B Γ}(v : A ∈ Γ)(v' : B ∈ Γ) → A ≡ B ⊎ (B ∈ subᶜ v)
∈-eq vz     vz      = inj₁ refl
∈-eq vz     (vs v') = inj₂ v'
∈-eq (vs v) vz      = inj₂ vz
∈-eq (vs v) (vs v') = smap id vs_ (∈-eq v v')

drop-sub-⊆ : ∀ {Γ A}(v : A ∈ Γ) → drop v ⊆ subᶜ v
drop-sub-⊆ vz     = refl
drop-sub-⊆ (vs v) = add (drop-sub-⊆ v)

sub : ∀ {Γ A B}(v : A ∈ Γ) → Tm (drop v) A → Tm Γ B → Tm (subᶜ v) B
sub v t' (f ∙ x) = sub v t' f ∙ sub v t' x
sub v t' (ƛ t)   = ƛ (sub (vs v) t' t)
sub v t' (var v') with ∈-eq v v'
... | inj₁ refl = ren (drop-sub-⊆ v) t'
... | inj₂ v''  = var v''

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

mutual
  ∙-SN→ : ∀ {Γ A B}{f : Tm Γ (A ⇒ B)}{x} → SN f → SN x → SN (f ∙ x)
  ∙-SN→ {Γ}{A}{B}{f}{x}(sn sf) (sn sx) = sn go where
    go : {t' : Tm Γ B} → f ∙ x ~> t' → SN t'
    go (β t t')      = sub-SN vz t' t (sn sx) (ƛ-SN← (sn sf))
    go (∙₁ f' f~>f') = ∙-SN→ (sf f~>f') (sn sx)
    go (∙₂ x' x~>x') = ∙-SN→ (sn sf) (sx x~>x')
  
  ren-SN : ∀ {Γ Δ A}(r : Γ ⊆ Δ){t : Tm Γ A} → SN t → SN (ren r t)
  ren-SN r {var v} snt = sn λ ()
  ren-SN r {f ∙ x} snt = let (sf , sx) = ∙-SN← snt in ∙-SN→ (ren-SN r sf) (ren-SN r sx)
  ren-SN r {ƛ t}   snt = ƛ-SN→ (ren-SN (keep r) {t} (ƛ-SN← snt))
  
  sub-SN : ∀ {Γ A B}(v : A ∈ Γ) t' t → SN t' → SN {_}{B} t → SN (sub v t' t)
  sub-SN v t' (var v') st' st with ∈-eq v v'
  ... | inj₁ refl = ren-SN (drop-sub-⊆ v) st'
  ... | inj₂ v''  = sn λ ()
  sub-SN v t' (f ∙ x)  st' st = 
    let (sf , sx) = ∙-SN← st in ∙-SN→ (sub-SN v t' f st' sf) (sub-SN v t' x st' sx)
  sub-SN v t' (ƛ t)    st' st = ƛ-SN→ (sub-SN (vs v) t' t st' (ƛ-SN← st))

--------------------------------------------------------------------------------

-- ⟦_⟧ˢ : ∀ {Γ Δ} → Sub Γ Δ → Set
-- ⟦ ε     ⟧ˢ = ⊤
-- ⟦ δ ▷ t ⟧ˢ = ⟦ δ ⟧ˢ × ⟦ _ ⟧ t

-- ⟦var⟧ : ∀ {A Γ} → (v : A ∈ Γ) → ⟦ A ⟧ (var v)
-- ⟦var⟧ v = CR₃ (var v) _ (λ ())

-- ⟦sub-∈⟧ : ∀ {A Γ Δ}{δ : Sub Δ Γ} → ⟦ δ ⟧ˢ → (v : A ∈ Γ) → ⟦ A ⟧ (sub-∈ δ v)
-- ⟦sub-∈⟧ {δ = δ ▷ t} (_   , ⟦t⟧) vz     = ⟦t⟧
-- ⟦sub-∈⟧ {δ = δ ▷ t} (⟦δ⟧ , _)   (vs v) = ⟦sub-∈⟧ ⟦δ⟧ v

-- ⟦∙⟧→ : ∀ {A B Γ}{f : Tm Γ (A ⇒ B)}{x} → ⟦ A ⇒ B ⟧ f → ⟦ A ⟧ x → ⟦ B ⟧ (f ∙ x)
-- ⟦∙⟧→ ⟦f⟧ ⟦x⟧ = {!!}

-- ⟦∙⟧← : ∀ {A B Γ}{f : Tm Γ (A ⇒ B)}{x} → ⟦ B ⟧ (f ∙ x) → ⟦ A ⇒ B ⟧ f × (⟦ A ⟧ x)
-- ⟦∙⟧← ⟦f∙x⟧ = {!!}

-- ⟦ren⟧ : ∀ {Γ Δ A}(r : Γ ⊆ Δ){t : Tm Γ A} → ⟦ A ⟧ t → ⟦ A ⟧ (ren r t)
-- ⟦ren⟧ r {var v} ⟦t⟧ = ⟦var⟧ (ren-∈ r v)
-- ⟦ren⟧ r {f ∙ x} ⟦t⟧ = let (⟦f⟧ , ⟦x⟧) = ⟦∙⟧← {f = f}{x}⟦t⟧ in ⟦∙⟧→ (⟦ren⟧ r {f} ⟦f⟧) (⟦ren⟧ r {x} ⟦x⟧)
-- ⟦ren⟧ r {ƛ t}   ⟦t⟧ = {!!} , (λ {a} ⟦a⟧ → {!⟦ren⟧!}) -- !!!

-- ⟦ren-Sub⟧ : ∀ {Γ Δ Ξ}{δ : Sub Γ Δ} → ⟦ δ ⟧ˢ → (r : Γ ⊆ Ξ) → ⟦ ren-Sub δ r ⟧ˢ
-- ⟦ren-Sub⟧ {δ = ε}     ⟦δ⟧         r = tt
-- ⟦ren-Sub⟧ {δ = δ ▷ t} (⟦δ⟧ , ⟦t⟧) r = ⟦ren-Sub⟧ ⟦δ⟧ r , ⟦ren⟧ r {t} ⟦t⟧

-- ⟦wk⟧ : ∀ {A Γ Δ}{δ : Sub Γ Δ} → ⟦ δ ⟧ˢ → ⟦ wk {A} δ ⟧ˢ
-- ⟦wk⟧ {A} ⟦δ⟧ = ⟦ren-Sub⟧ ⟦δ⟧ (add refl) , ⟦var⟧ {A} vz

-- ⟦ƛ⟧ :
--   ∀ {A B Γ Δ}{δ : Sub Γ Δ}{t : Tm (Δ ▷ A) B}
--   → ⟦ δ ⟧ˢ → ∀ {a} → ⟦ A ⟧ a
--   → ⟦ B ⟧ (sub (δ ▷ a) t)
--   → ⟦ B ⟧ (ƛ (sub (wk δ) t) ∙ a)
-- ⟦ƛ⟧ ⟦δ⟧ ⟦a⟧ ⟦t⟧ = {!!}

-- ⟦_⟧ᵗ : ∀ {A Γ Δ}(t : Tm Γ A) → {δ : Sub Δ Γ} → ⟦ δ ⟧ˢ → ⟦ A ⟧ (sub δ t)
-- ⟦ var v ⟧ᵗ ⟦δ⟧ = ⟦sub-∈⟧ ⟦δ⟧ v
-- ⟦ f ∙ x ⟧ᵗ ⟦δ⟧ = ⟦∙⟧→ (⟦ f ⟧ᵗ ⟦δ⟧) (⟦ x ⟧ᵗ ⟦δ⟧)
-- ⟦ ƛ t   ⟧ᵗ ⟦δ⟧ =
--   ƛ-SN→ (CR₁ (⟦ t ⟧ᵗ (⟦wk⟧ ⟦δ⟧))) ,
--   λ ⟦a⟧ → ⟦ƛ⟧ ⟦δ⟧ ⟦a⟧ (⟦ t ⟧ᵗ (⟦δ⟧ , ⟦a⟧))


