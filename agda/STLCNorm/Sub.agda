
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

ren-Sub : ∀ {Γ Δ Ξ} → Sub Γ Δ → Γ ⊆ Ξ → Sub Ξ Δ
ren-Sub ε       r = ε
ren-Sub (δ ▷ t) r = ren-Sub δ r ▷ ren r t

wk : ∀ {A Γ Δ} → Sub Γ Δ → Sub (Γ ▷ A) (Δ ▷ A)
wk δ = ren-Sub δ (add refl) ▷ var vz

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

ƛ-SN : ∀ {Γ A B}{t : Tm (Γ ▷ A) B} → SN t → SN (ƛ t)
ƛ-SN (sn s) = sn λ {(ƛ _ t~>t') → ƛ-SN (s t~>t')}

--------------------------------------------------------------------------------

neu : ∀ {Γ A} → Tm Γ A → Set
neu (var _) = ⊤
neu (_ ∙ _) = ⊤
neu (ƛ _)   = ⊥

--------------------------------------------------------------------------------

⟦_⟧ : (A : Ty) → ∀ {Γ} → Tm Γ A → Set
⟦ ⋆     ⟧ = SN
⟦ A ⇒ B ⟧ = λ f → SN f × (∀ {a} → ⟦ A ⟧ a → ⟦ B ⟧ (f ∙ a))

--------------------------------------------------------------------------------

mutual
  CR₁ : ∀ {A Γ t} → ⟦ A ⟧ {Γ} t → SN t
  CR₁ {⋆}     = id
  CR₁ {A ⇒ B} = proj₁

  CR₂ : ∀ {A Γ t t'} → t ~> t' → ⟦ A ⟧ {Γ} t → ⟦ A ⟧ t'
  CR₂ {⋆}     t~>t' (sn n)       = n t~>t'
  CR₂ {A ⇒ B} t~>t' (sn st , rt) = st t~>t' , λ ⟦a⟧ → CR₂ (∙₁ _ t~>t') (rt ⟦a⟧)

  CR₃ : ∀ {A Γ}(t : Tm Γ A) → neu t → (∀ {t'} → t ~> t' → ⟦ A ⟧ t') → ⟦ A ⟧ t
  CR₃ {⋆}     t nt f = sn f
  CR₃ {A ⇒ B} t nt f = sn (proj₁ ∘ f) , λ ⟦a⟧ → CR₃ _ _ (go nt f ⟦a⟧ (CR₁ ⟦a⟧) _)
    where
      go :
        ∀ {A B Γ}{t : Tm Γ (A ⇒ B)} → neu t → (∀ {t'} → t ~> t' → ⟦ A ⇒ B ⟧ t')
        → ∀ {a} → ⟦ A ⟧ a → SN a → ∀ t' → t ∙ a ~> t' → ⟦ B ⟧ t'
      go () _   _  _        _ (β _ _)
      go nt f ⟦a⟧ sna      _ (∙₁ t' t~>t') = proj₂ (f t~>t') ⟦a⟧
      go nt f ⟦a⟧ (sn sna) _ (∙₂ a' a~>a') =
        CR₃ (_ ∙ a') _ (go nt f (CR₂ a~>a' ⟦a⟧) (sna a~>a') _)


--------------------------------------------------------------------------------

⟦_⟧ˢ : ∀ {Γ Δ} → Sub Γ Δ → Set
⟦ ε     ⟧ˢ = ⊤
⟦ δ ▷ t ⟧ˢ = ⟦ δ ⟧ˢ × ⟦ _ ⟧ t

⟦var⟧ : ∀ {A Γ} → (v : A ∈ Γ) → ⟦ A ⟧ (var v)
⟦var⟧ v = CR₃ (var v) _ (λ ())

⟦sub-∈⟧ : ∀ {A Γ Δ}{δ : Sub Δ Γ} → ⟦ δ ⟧ˢ → (v : A ∈ Γ) → ⟦ A ⟧ (sub-∈ δ v)
⟦sub-∈⟧ = {!!}

⟦ren-Sub⟧ : ∀ {Γ Δ Ξ}{δ : Sub Γ Δ} → ⟦ δ ⟧ˢ → (r : Γ ⊆ Ξ) → ⟦ ren-Sub δ r ⟧ˢ
⟦ren-Sub⟧ ⟦δ⟧ r = {!!}

⟦wk⟧ : ∀ {A Γ Δ}{δ : Sub Γ Δ} → ⟦ δ ⟧ˢ → ⟦ wk {A} δ ⟧ˢ
⟦wk⟧ {A} ⟦δ⟧ = ⟦ren-Sub⟧ ⟦δ⟧ (add refl) , ⟦var⟧ {A} vz

⟦∙⟧ : ∀ {A B Γ Δ}{δ : Sub Γ Δ}{f x}
      → ⟦ δ ⟧ˢ → ⟦ A ⇒ B ⟧ (sub δ f) → ⟦ A ⟧ (sub δ x) → ⟦ B ⟧ (sub δ f ∙ sub δ x)
⟦∙⟧ ⟦δ⟧ ⟦f⟧ ⟦x⟧ = {!!}

⟦▷⟧ : ∀ {A Γ Δ}{δ : Sub Γ Δ}{t : Tm Γ A} → ⟦ δ ⟧ˢ → ⟦ A ⟧ t → ⟦ δ ▷ t ⟧ˢ
⟦▷⟧ = {!!}

⟦ƛ⟧ :
  ∀ {A B Γ Δ}{δ : Sub Γ Δ}{t : Tm (Δ ▷ A) B}
  → ⟦ δ ⟧ˢ → ∀ {a} → ⟦ A ⟧ a
  → ⟦ B ⟧ (sub (δ ▷ a) t)
  → ⟦ B ⟧ (ƛ (sub (wk δ) t) ∙ a)
⟦ƛ⟧ ⟦δ⟧ ⟦a⟧ ⟦t⟧ = {!!}

⟦_⟧ᵗ : ∀ {A Γ Δ}(t : Tm Γ A) → {δ : Sub Δ Γ} → ⟦ δ ⟧ˢ → ⟦ A ⟧ (sub δ t)
⟦ var v ⟧ᵗ ⟦δ⟧ = ⟦sub-∈⟧ ⟦δ⟧ v
⟦ f ∙ x ⟧ᵗ ⟦δ⟧ = ⟦∙⟧ ⟦δ⟧ (⟦ f ⟧ᵗ ⟦δ⟧) (⟦ x ⟧ᵗ ⟦δ⟧)
⟦ ƛ t   ⟧ᵗ ⟦δ⟧ =
  ƛ-SN (CR₁ (⟦ t ⟧ᵗ (⟦wk⟧ ⟦δ⟧))) ,
  λ ⟦a⟧ → ⟦ƛ⟧ ⟦δ⟧ ⟦a⟧ (⟦ t ⟧ᵗ (⟦▷⟧ ⟦δ⟧ ⟦a⟧))








