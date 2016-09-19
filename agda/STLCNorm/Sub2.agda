
module Sub2 where

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

-- Strong normalization
--------------------------------------------------------------------------------

snk : ∀ {Γ A} → Tm Γ A → (∀ {Γ A B} → Tm Γ A → Tm (Γ ▷ A) B → Set) → Set
snk (var v)      k = ⊤
snk (var _ ∙ x)  k = snk x k
snk (f ∙ x ∙ y)  k = snk (f ∙ x) k × snk y k
snk (ƛ f ∙ x)    k = k x f 
snk (ƛ t)        k = snk t k

data SN {Γ A} (t : Tm Γ A) : Set where
  sn : snk t (λ x f → SN (inst x f)) → SN t

runSN : ∀ {Γ A}{t : Tm Γ A} → SN t → snk t (λ x f → SN (inst x f))
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

-- mutual
--   CR₁ : ∀ {A Γ t} → ⟦ A ⟧ {Γ} t → SN t
--   CR₁ {⋆}     = id
--   CR₁ {A ⇒ B} = proj₁

--   CR₂ : ∀ {A Γ t t'} → t ~> t' → ⟦ A ⟧ {Γ} t → ⟦ A ⟧ t'
--   CR₂ {⋆}     t~>t' (sn nt)       = nt t~>t'
--   CR₂ {A ⇒ B} t~>t' (sn st , ⟦t⟧) = st t~>t' , λ ⟦a⟧ → CR₂ (∙₁ _ t~>t') (⟦t⟧ ⟦a⟧)

--   CR₃ : ∀ {A Γ}(t : Tm Γ A) → neu t → (∀ {t'} → t ~> t' → ⟦ A ⟧ t') → ⟦ A ⟧ t
--   CR₃ {⋆}     t nt f = sn f
--   CR₃ {A ⇒ B} t nt f = sn (proj₁ ∘ f) , λ ⟦a⟧ → CR₃ _ _ (go nt f ⟦a⟧ (CR₁ ⟦a⟧) _)
--     where
--       go :
--         ∀ {A B Γ}{t : Tm Γ (A ⇒ B)} → neu t → (∀ {t'} → t ~> t' → ⟦ A ⇒ B ⟧ t')
--         → ∀ {a} → ⟦ A ⟧ a → SN a → ∀ t' → t ∙ a ~> t' → ⟦ B ⟧ t'
--       go () _ _   _        _ (β _ _)
--       go nt f ⟦a⟧ sna      _ (∙₁ t' t~>t') = proj₂ (f t~>t') ⟦a⟧
--       go nt f ⟦a⟧ (sn sna) _ (∙₂ a' a~>a') =
--         CR₃ (_ ∙ a') _ (go nt f (CR₂ a~>a' ⟦a⟧) (sna a~>a') _)


-- Constructors and substitution preserve strong normalization
--------------------------------------------------------------------------------

∙-SN← : ∀ {Γ A B}{f : Tm Γ (A ⇒ B)}{x} → SN (f ∙ x) → SN f × SN x
∙-SN← {f = var x} (sn s)         = sn tt , sn s
∙-SN← {f = f ∙ x} (sn (sf , sx)) = sn sf , sn sx
∙-SN← {f = ƛ f}   (sn (sn s))    = {!!} , {!!}


-- ∙-SN← : ∀ {Γ A B}{f : Tm Γ (A ⇒ B)}{x} → SN (f ∙ x) → SN f × SN x
-- ∙-SN← (sn s) =
--   sn (λ f~>f' → proj₁ (∙-SN← (s (∙₁ _ f~>f')))) ,
--   sn (λ x~>x' → proj₂ (∙-SN← (s (∙₂ _ x~>x'))))

∙-SN→ : ∀ {Γ A B}{f : Tm Γ (A ⇒ B)}{x} → SN f → SN x → SN (f ∙ x)
∙-SN→ {f = var v}  (sn sf) (sn sx) = sn sx
∙-SN→ {f = f ∙ x}  (sn sf) (sn sx) = sn (sf , sx)
∙-SN→ {f = ƛ f}    (sn sf) (sn sx) = sn {!!}



-- sub-∈-SN : ∀ {Γ Δ A}{δ : Sub Γ Δ} → SNᶜ δ → (v : A ∈ Δ) → SN (sub-∈ δ v)
-- sub-∈-SN {δ = δ ▷ x} snδ vz     = proj₂ snδ
-- sub-∈-SN {δ = δ ▷ x} snδ (vs v) = sub-∈-SN (proj₁ snδ) v

-- mutual
--   sub-SN : ∀ {Γ Δ A}{δ : Sub Γ Δ} → SNᶜ δ → ∀{t : Tm Δ A} → SN t → SN (sub δ t)
--   sub-SN snδ {var v} snt = sub-∈-SN snδ v
--   sub-SN snδ {f ∙ x} snt =
--     let (sf , sx) = ∙-SN← snt in ∙-SN→ (sub-SN snδ sf) (sub-SN snδ sx)
--   sub-SN snδ {ƛ t}   snt = {!!}
  
--   ∙-SN→ : ∀ {Γ A B}{f : Tm Γ (A ⇒ B)}{x} → SN f → SN x → SN (f ∙ x)
--   ∙-SN→ (sn sf) (sn sx) = sn             
--     λ {(∙₁ f' f~>f') → ∙-SN→ (sf f~>f') (sn sx);
--        (∙₂ x' x~>x') → ∙-SN→ (sn sf) (sx x~>x');
--        (β t t')      → sub-SN (idˢ-SN , sn sx) (ƛ-SN← (sn sf))}
  
-- ren-SN : ∀ {Γ Δ A}(r : Γ ⊆ Δ){t : Tm Γ A} → SN t → SN (ren r t)
-- ren-SN r {var v} snt = sn λ ()
-- ren-SN r {f ∙ x} snt = let (sf , sx) = ∙-SN← snt in ∙-SN→ (ren-SN r sf) (ren-SN r sx)
-- ren-SN r {ƛ t}   snt = ƛ-SN→ (ren-SN (keep r) {t} (ƛ-SN← snt))

-- ren-Sub-SN : ∀ {Γ Δ Ξ}(r : Γ ⊆ Ξ){δ : Sub Γ Δ} → SNᶜ δ → SNᶜ (ren-Sub r δ)
-- ren-Sub-SN r {ε}     snδ         = snδ
-- ren-Sub-SN r {δ ▷ x} (snδ , snx) = ren-Sub-SN r snδ , ren-SN r snx

-- --------------------------------------------------------------------------------

-- -- ⟦_⟧ˢ : ∀ {Γ Δ} → Sub Γ Δ → Set
-- -- ⟦ ε     ⟧ˢ = ⊤
-- -- ⟦ δ ▷ t ⟧ˢ = ⟦ δ ⟧ˢ × ⟦ _ ⟧ t

-- -- ⟦var⟧ : ∀ {A Γ} → (v : A ∈ Γ) → ⟦ A ⟧ (var v)
-- -- ⟦var⟧ v = CR₃ (var v) _ (λ ())

-- -- ⟦sub-∈⟧ : ∀ {A Γ Δ}{δ : Sub Δ Γ} → ⟦ δ ⟧ˢ → (v : A ∈ Γ) → ⟦ A ⟧ (sub-∈ δ v)
-- -- ⟦sub-∈⟧ {δ = δ ▷ t} (_   , ⟦t⟧) vz     = ⟦t⟧
-- -- ⟦sub-∈⟧ {δ = δ ▷ t} (⟦δ⟧ , _)   (vs v) = ⟦sub-∈⟧ ⟦δ⟧ v

-- -- ⟦∙⟧→ : ∀ {A B Γ}{f : Tm Γ (A ⇒ B)}{x} → ⟦ A ⇒ B ⟧ f → ⟦ A ⟧ x → ⟦ B ⟧ (f ∙ x)
-- -- ⟦∙⟧→ ⟦f⟧ ⟦x⟧ = {!!}

-- -- ⟦∙⟧← : ∀ {A B Γ}{f : Tm Γ (A ⇒ B)}{x} → ⟦ B ⟧ (f ∙ x) → ⟦ A ⇒ B ⟧ f × (⟦ A ⟧ x)
-- -- ⟦∙⟧← ⟦f∙x⟧ = {!!}

-- -- ⟦ren⟧ : ∀ {Γ Δ A}(r : Γ ⊆ Δ){t : Tm Γ A} → ⟦ A ⟧ t → ⟦ A ⟧ (ren r t)
-- -- ⟦ren⟧ r {var v} ⟦t⟧ = ⟦var⟧ (ren-∈ r v)
-- -- ⟦ren⟧ r {f ∙ x} ⟦t⟧ = let (⟦f⟧ , ⟦x⟧) = ⟦∙⟧← {f = f}{x}⟦t⟧ in ⟦∙⟧→ (⟦ren⟧ r {f} ⟦f⟧) (⟦ren⟧ r {x} ⟦x⟧)
-- -- ⟦ren⟧ r {ƛ t}   ⟦t⟧ = {!!} , (λ {a} ⟦a⟧ → {!⟦ren⟧!}) -- !!!

-- -- ⟦ren-Sub⟧ : ∀ {Γ Δ Ξ}{δ : Sub Γ Δ} → ⟦ δ ⟧ˢ → (r : Γ ⊆ Ξ) → ⟦ ren-Sub δ r ⟧ˢ
-- -- ⟦ren-Sub⟧ {δ = ε}     ⟦δ⟧         r = tt
-- -- ⟦ren-Sub⟧ {δ = δ ▷ t} (⟦δ⟧ , ⟦t⟧) r = ⟦ren-Sub⟧ ⟦δ⟧ r , ⟦ren⟧ r {t} ⟦t⟧

-- -- ⟦wk⟧ : ∀ {A Γ Δ}{δ : Sub Γ Δ} → ⟦ δ ⟧ˢ → ⟦ wk {A} δ ⟧ˢ
-- -- ⟦wk⟧ {A} ⟦δ⟧ = ⟦ren-Sub⟧ ⟦δ⟧ (add refl) , ⟦var⟧ {A} vz

-- -- ⟦ƛ⟧ :
-- --   ∀ {A B Γ Δ}{δ : Sub Γ Δ}{t : Tm (Δ ▷ A) B}
-- --   → ⟦ δ ⟧ˢ → ∀ {a} → ⟦ A ⟧ a
-- --   → ⟦ B ⟧ (sub (δ ▷ a) t)
-- --   → ⟦ B ⟧ (ƛ (sub (wk δ) t) ∙ a)
-- -- ⟦ƛ⟧ ⟦δ⟧ ⟦a⟧ ⟦t⟧ = {!!}

-- -- ⟦_⟧ᵗ : ∀ {A Γ Δ}(t : Tm Γ A) → {δ : Sub Δ Γ} → ⟦ δ ⟧ˢ → ⟦ A ⟧ (sub δ t)
-- -- ⟦ var v ⟧ᵗ ⟦δ⟧ = ⟦sub-∈⟧ ⟦δ⟧ v
-- -- ⟦ f ∙ x ⟧ᵗ ⟦δ⟧ = ⟦∙⟧→ (⟦ f ⟧ᵗ ⟦δ⟧) (⟦ x ⟧ᵗ ⟦δ⟧)
-- -- ⟦ ƛ t   ⟧ᵗ ⟦δ⟧ =
-- --   ƛ-SN→ (CR₁ (⟦ t ⟧ᵗ (⟦wk⟧ ⟦δ⟧))) ,
-- --   λ ⟦a⟧ → ⟦ƛ⟧ ⟦δ⟧ ⟦a⟧ (⟦ t ⟧ᵗ (⟦δ⟧ , ⟦a⟧))


