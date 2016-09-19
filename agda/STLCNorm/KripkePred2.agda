
module KripkePred2 where

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

-- Categorical renaming
--------------------------------------------------------------------------------

_∘ʳ_ : ∀ {Γ Δ Ξ} → Δ ⊆ Ξ → Γ ⊆ Δ → Γ ⊆ Ξ
refl   ∘ʳ r'      = r'
add r  ∘ʳ r'      = add (r ∘ʳ r')
keep r ∘ʳ refl    = keep r
keep r ∘ʳ add r'  = add (r ∘ʳ r')
keep r ∘ʳ keep r' = keep (r ∘ʳ r')
infixr 9 _∘ʳ_

∘ʳ-refl : ∀ {Γ Δ} (r : Γ ⊆ Δ) → r ∘ʳ refl ≡ r
∘ʳ-refl refl     = refl
∘ʳ-refl (add r)  = cong add (∘ʳ-refl r)
∘ʳ-refl (keep r) = refl

ren-∈-∘ʳ :
  ∀ {Γ Δ Ξ A} (r : Δ ⊆ Ξ) (r' : Γ ⊆ Δ) (v : A ∈ Γ)
  → ren-∈ r (ren-∈ r' v) ≡ ren-∈ (r ∘ʳ r') v
ren-∈-∘ʳ refl     r'        v      = refl
ren-∈-∘ʳ (add r)  r'        v      = cong vs_ (ren-∈-∘ʳ r r' v)
ren-∈-∘ʳ (keep r) refl      v      = refl
ren-∈-∘ʳ (keep r) (add r')  v      = cong vs_ (ren-∈-∘ʳ r r' v)
ren-∈-∘ʳ (keep r) (keep r') vz     = refl
ren-∈-∘ʳ (keep r) (keep r') (vs v) = ren-∈-∘ʳ (add r) r' v

ren-∘ʳ : ∀ {Γ Δ Ξ A}(r : Δ ⊆ Ξ)(r' : Γ ⊆ Δ)(t : Tm Γ A) → ren r (ren r' t) ≡ ren (r ∘ʳ r') t
ren-∘ʳ r r' (var v) = cong var (ren-∈-∘ʳ r r' v)
ren-∘ʳ r r' (f ∙ x) = cong₂ _∙_ (ren-∘ʳ r r' f) (ren-∘ʳ r r' x)
ren-∘ʳ r r' (ƛ t)   = cong ƛ (ren-∘ʳ (keep r) (keep r') t)

Id-⊆ : ∀ {Γ} → Γ ⊆ Γ → Set
Id-⊆ refl     = ⊤
Id-⊆ (add o)  = ⊥
Id-⊆ (keep o) = Id-⊆ o

ren-∈-Id : ∀ {Γ A}(r : Γ ⊆ Γ){{p : Id-⊆ r}}(v : A ∈ Γ) → ren-∈ r v ≡ v
ren-∈-Id refl     v      = refl
ren-∈-Id (add r) {{()}} v
ren-∈-Id (keep r) vz     = refl
ren-∈-Id (keep r) (vs v) = cong vs_ (ren-∈-Id r v)

ren-Id : ∀ {Γ A}(r : Γ ⊆ Γ){{p : Id-⊆ r}}(t : Tm Γ A) → ren r t ≡ t
ren-Id r (var v) = cong var (ren-∈-Id r v)
ren-Id r (f ∙ x) = cong₂ _∙_ (ren-Id r f) (ren-Id r x)
ren-Id r (ƛ t)   = cong ƛ (ren-Id (keep r) t)

ren-refl : ∀ {Γ A}(t : Tm Γ A) → ren refl t ≡ t
ren-refl = ren-Id refl

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

ƛ-SN→ : ∀ {Γ A B}{t : Tm (Γ ▷ A) B} → SN t → SN (ƛ t)
ƛ-SN→ (sn s) = sn λ {(ƛ _ t~>t') → ƛ-SN→ (s t~>t')}

-- Reducibility
--------------------------------------------------------------------------------

-- Kripke reducibility predicate
⟦_⟧ : (A : Ty) → ∀ {Γ} → Tm Γ A → Set
⟦ ⋆     ⟧ {Γ} t = ∀ {Δ}(r : Γ ⊆ Δ) → SN (ren r t)
⟦ A ⇒ B ⟧ {Γ} f = ∀ {Δ}(r : Γ ⊆ Δ){a : Tm Δ A} → ⟦ A ⟧ a → ⟦ B ⟧ (ren r f ∙ a)

∙-SN : ∀ {Γ A B}{f : Tm Γ (A ⇒ B)}{x} → SN (f ∙ x) → SN f × SN x
∙-SN (sn s) =
  sn (λ f~>f' → proj₁ (∙-SN (s (∙₁ _ f~>f')))) ,
  sn (λ x~>x' → proj₂ (∙-SN (s (∙₂ _ x~>x'))))

ren~> : ∀ {Γ Δ A}(r : Γ ⊆ Δ){t t' : Tm Γ A} → t ~> t' → ren r t ~> ren r t'
ren~> r (β t t')      = {!!} -- TODO: ren-sub
ren~> r (ƛ t' t~>t')  = ƛ (ren (keep r) t') (ren~> (keep r) t~>t')
ren~> r (∙₁ f' f~>f') = ∙₁ (ren r f') (ren~> r f~>f')
ren~> r (∙₂ x' x~>x') = ∙₂ (ren r x') (ren~> r x~>x')

ren-SN : ∀ {Γ Δ A} (r : Γ ⊆ Δ)(t : Tm Γ A) → SN (ren r t) → SN t
ren-SN r t (sn snt) = sn (λ {t'} t~>t' → ren-SN r t' (snt (ren~> r t~>t')))

ren-neu : ∀ {Γ Δ A}(r : Γ ⊆ Δ){t : Tm Γ A} → neu t → neu (ren r t)
ren-neu r {var _} nt = tt
ren-neu r {_ ∙ _} nt = tt
ren-neu r {ƛ _}   nt = nt

mutual
  CR₁' : ∀ {A Γ t} → ⟦ A ⟧ {Γ} t → SN t  
  CR₁' {t = t}⟦t⟧ = subst SN (ren-refl t) (CR₁ refl {t} ⟦t⟧)

  CR₁ : ∀ {A Γ Δ}(r : Γ ⊆ Δ){t} → ⟦ A ⟧ {Γ} t → SN (ren r t)
  CR₁ {⋆}     r     ⟦t⟧ = ⟦t⟧ r
  CR₁ {A ⇒ B} r {t} ⟦t⟧ =
    let
      l1 : ⟦ B ⟧ (ren (add r) t ∙ var vz)    
      l1 = ⟦t⟧ (add {A} r) (CR₃ (var (vz {A})) _ (λ _ ()))
      
      l2 : SN (ren (add r) t ∙ var vz)
      l2 = CR₁' l1

      l3 : SN (ren (add {A} r) t)
      l3 = proj₁ (∙-SN l2)

      l4 : SN (ren (add {A} refl) (ren r t))
      l4 = subst SN (sym (ren-∘ʳ (add refl) r t)) l3

    in ren-SN (add refl) (ren r t) l4
    
  CR₂ : ∀ {A Δ Γ t t'}(r : Γ ⊆ Δ) → ren r t ~> t' → ⟦ A ⟧ {Γ} t → ⟦ A ⟧ t'
  CR₂ {⋆}     r rt~>t' ⟦t⟧ r' = {!!}
  CR₂ {A ⇒ B} = {!!}
  -- CR₂ {⋆}     r rt~>t' (sn s) = sn (λ {t'} step → {!!}) -- t~>t'
  -- CR₂ {A ⇒ B} r rt~>t' ⟦t⟧    = {!!} -- λ r ⟦a⟧ → CR₂ (∙₁ _ (ren~> r t~>t')) (⟦t⟧ r ⟦a⟧)

  -- CR₂ : ∀ {A Γ t t'} → t ~> t' → ⟦ A ⟧ {Γ} t → ⟦ A ⟧ t'
  -- CR₂ {⋆}     t~>t' (sn s) = s t~>t'
  -- CR₂ {A ⇒ B} t~>t' ⟦t⟧    = λ r ⟦a⟧ → CR₂ (∙₁ _ (ren~> r t~>t')) (⟦t⟧ r ⟦a⟧)

  CR₃ : ∀ {A Γ}(t : Tm Γ A) → neu t → (∀ {Δ}(r : Γ ⊆ Δ){t'} → ren r t ~> t' → ⟦ A ⟧ t') → ⟦ A ⟧ t
  CR₃ = {!!}
  -- CR₃ {⋆}     t nt f = sn (f refl ∘ subst (_~> _) (sym (ren-refl t)))
  -- CR₃ {A ⇒ B}{Γ} t nt f {Δ} r {a} ⟦a⟧ = 
  --   CR₃ {B} (ren r t ∙ a) _ (λ r' → go t nt r ⟦a⟧ (CR₁ ⟦a⟧) f r' refl)
  --   where
  --     go :
  --       ∀ {Γ Δ A B}
  --       → (t : Tm Γ (A ⇒ B))
  --       → neu t
  --       → (r : Γ ⊆ Δ)
  --       → {a : Tm Δ A}
  --       → ⟦ A ⟧ a
  --       → SN a               
  --       → (∀ {Δ}(r : Γ ⊆ Δ){t'} → ren r t ~> t' → ⟦ A ⇒ B ⟧ t')
  --       → ∀ {Δ'} (r' : Δ ⊆ Δ') {t' : Tm Δ' B}{lhs}
  --       → lhs ≡ ren r' (ren r t ∙ a)
  --       → lhs ~> t' → ⟦ B ⟧ t'
  --     go (var _) _ _ _ _ _ _ () (β _ _)
  --     go (_ ∙ _) _ _ _ _ _ _ () (β _ _)
  --     go (ƛ _)  () _ _ _ _ _ _  (β _ _)
  --     go _       _ _ _ _ _ _ () (ƛ _ _)      
  --     go t nt r {a} ⟦a⟧ sna f r' refl (∙₁ f' step) rewrite ren-∘ʳ r' r t
  --       = subst (λ x → ⟦ _ ⟧ (x ∙ ren r' a)) (ren-refl f') (f (r' ∘ʳ r) step refl {ren r' a} {!⟦a⟧!})
  --     go t nt r ⟦a⟧ sna f r' refl (∙₂ x' step) = {!!}
       

-- --------------------------------------------------------------------------------

-- ⟦_⟧ˢ : ∀ {Γ Δ} → Sub Γ Δ → Set
-- ⟦ ε     ⟧ˢ = ⊤
-- ⟦ δ ▷ t ⟧ˢ = ⟦ δ ⟧ˢ × ⟦ _ ⟧ t

-- ⟦ƛ⟧ :
--   ∀ {A B Γ Δ}{δ : Sub Γ Δ}{t : Tm (Δ ▷ A) B}
--   → ⟦ δ ⟧ˢ → ∀ {a} → ⟦ A ⟧ a
--   → ⟦ B ⟧ (sub (δ ▷ a) t)
--   → ⟦ B ⟧ (ƛ (sub (wk δ) t) ∙ a)
-- ⟦ƛ⟧ ⟦δ⟧ ⟦a⟧ ⟦t⟧ = {!!}

-- ⟦sub-∈⟧ : ∀ {A Γ Δ}{δ : Sub Δ Γ} → ⟦ δ ⟧ˢ → (v : A ∈ Γ) → ⟦ A ⟧ (sub-∈ δ v)
-- ⟦sub-∈⟧ {δ = δ ▷ t} (_   , ⟦t⟧) vz     = ⟦t⟧
-- ⟦sub-∈⟧ {δ = δ ▷ t} (⟦δ⟧ , _)   (vs v) = ⟦sub-∈⟧ ⟦δ⟧ v

-- ⟦_⟧ᵗ : ∀ {A Γ Δ}(t : Tm Γ A) → {δ : Sub Δ Γ} → ⟦ δ ⟧ˢ → ⟦ A ⟧ (sub δ t)
-- ⟦ var v ⟧ᵗ ⟦δ⟧ = ⟦sub-∈⟧ ⟦δ⟧ v
-- ⟦ f ∙ x ⟧ᵗ ⟦δ⟧ = (⟦ f ⟧ᵗ ⟦δ⟧) (⟦ x ⟧ᵗ ⟦δ⟧)
-- ⟦ ƛ t   ⟧ᵗ ⟦δ⟧ = λ ⟦a⟧ → ⟦ƛ⟧ ⟦δ⟧ ⟦a⟧ (⟦ t ⟧ᵗ (⟦δ⟧ , ⟦a⟧))


