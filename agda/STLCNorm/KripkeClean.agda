
module KripkeClean where

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


--------------------------------------------------------------------------------

toSub : ∀ {Γ Δ} → Γ ⊆ Δ → Sub Δ Γ
toSub refl     = idˢ
toSub (add r)  = ren-Sub (add refl) (toSub r)
toSub (keep r) = wk (toSub r)

_∘ˢ_ : ∀ {Γ Δ Ξ} → Sub Δ Ξ → Sub Γ Δ → Sub Γ Ξ
ε       ∘ˢ δ' = ε
(δ ▷ t) ∘ˢ δ' = δ ∘ˢ δ' ▷ sub δ' t

--------------------------------------------------------------------------------

ren-sub-refl :
  ∀ {Γ Δ}(δ : Sub Δ Γ) → ren-Sub refl δ ≡ δ
ren-sub-refl ε = refl
ren-sub-refl (δ ▷ t) rewrite ren-sub-refl δ | ren-refl t = refl

ren-sub-∘ʳ :
  ∀ {Γ Δ Ξ Σ}(r : Ξ ⊆ Σ)(r' : Δ ⊆ Ξ)(δ : Sub Δ Γ)
  → ren-Sub r (ren-Sub r' δ) ≡ ren-Sub (r ∘ʳ r') δ
ren-sub-∘ʳ r r' ε       = refl
ren-sub-∘ʳ r r' (δ ▷ t) rewrite ren-sub-∘ʳ r r' δ | ren-∘ʳ r r' t = refl

ren-sub-∈ : ∀ {Γ Δ Ξ A}(r : Δ ⊆ Ξ)(s : Sub Δ Γ)(v : A ∈ Γ) → ren r (sub-∈ s v) ≡ sub-∈ (ren-Sub r s) v
ren-sub-∈ r (s ▷ x) vz     = refl
ren-sub-∈ r (s ▷ x) (vs v) = ren-sub-∈ r s v

ren-sub : ∀ {Γ Δ Ξ A}(r : Δ ⊆ Ξ)(s : Sub Δ Γ)(t : Tm Γ A) → ren r (sub s t) ≡ sub (ren-Sub r s) t
ren-sub r s (var v) = ren-sub-∈ r s v
ren-sub r s (f ∙ x) = cong₂ _∙_ (ren-sub r s f) (ren-sub r s x)
ren-sub r s (ƛ {A} t) rewrite
    ren-sub (keep r) (wk s) t
  | ren-sub-∘ʳ (keep {A} r) (add refl) s
  | ren-sub-∘ʳ (add {A} refl) r s
  | ∘ʳ-refl r = refl

ren-sub-ext :
  ∀ {Γ Δ Ξ A}(r : Δ ⊆ Ξ)(r' : Δ ⊆ Γ)(s : Sub Δ Γ)(t : Tm Γ A) → sub (ren-Sub r s) t ≡ {!!}
ren-sub-ext = {!!}  
  

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

neu : ∀ {Γ A} → Tm Γ A → Set
neu (var _) = ⊤
neu (_ ∙ _) = ⊤
neu (ƛ _)   = ⊥

ren-neu : ∀ {Γ Δ A}(r : Γ ⊆ Δ)(t : Tm Γ A) → neu t → neu (ren r t)
ren-neu r (var _) nt = tt
ren-neu r (_ ∙ _) nt = tt
ren-neu r (ƛ _)   nt = nt

∙-SN : ∀ {Γ A B}{f : Tm Γ (A ⇒ B)}{x} → SN (f ∙ x) → SN f × SN x
∙-SN (sn s) =
  sn (λ f~>f' → proj₁ (∙-SN (s (∙₁ _ f~>f')))) ,
  sn (λ x~>x' → proj₂ (∙-SN (s (∙₂ _ x~>x'))))

ren~> : ∀ {Γ Δ A}(r : Γ ⊆ Δ){t t' : Tm Γ A} → t ~> t' → ren r t ~> ren r t'
ren~> r (β t t')      rewrite ren-sub r (idˢ ▷ t') t = {!sub (ren-Sub r idˢ ▷ ren r t') t!}
ren~> r (ƛ t' t~>t')  = ƛ (ren (keep r) t') (ren~> (keep r) t~>t')
ren~> r (∙₁ f' f~>f') = ∙₁ (ren r f') (ren~> r f~>f')
ren~> r (∙₂ x' x~>x') = ∙₂ (ren r x') (ren~> r x~>x')

ren-SN : ∀ {Γ Δ A} (r : Γ ⊆ Δ)(t : Tm Γ A) → SN (ren r t) → SN t
ren-SN r t (sn snt) = sn (λ {t'} t~>t' → ren-SN r t' (snt (ren~> r t~>t')))

-- Reducibility
--------------------------------------------------------------------------------

-- Kripke reducibility predicate
⟦_⟧ : (A : Ty) → ∀ {Γ} → Tm Γ A → Set
⟦ ⋆     ⟧ {Γ} t = SN t
⟦ A ⇒ B ⟧ {Γ} f = ∀ {Δ}(r : Γ ⊆ Δ){a : Tm Δ A} → ⟦ A ⟧ a → ⟦ B ⟧ (ren r f ∙ a)

mutual
  CR₁ : ∀ {A Γ t} → ⟦ A ⟧ {Γ} t → SN t
  CR₁ {⋆}     {t = t} ⟦t⟧ = ⟦t⟧
  CR₁ {A ⇒ B} {t = t} ⟦t⟧ =
    ren-SN _ t $ proj₁ $ ∙-SN $ CR₁ (⟦t⟧ (add {A} refl) (CR₃ (var (vz{A})) _ (λ _ ())))

  CR₂ : ∀ {A Γ t t'} → t ~> t' → ⟦ A ⟧ {Γ} t → ⟦ A ⟧ t'
  CR₂ {⋆}     t~>t' (sn s) = s t~>t'
  CR₂ {A ⇒ B} t~>t' ⟦t⟧    = λ r {a} ⟦a⟧ → CR₂ (∙₁ _ (ren~> r t~>t')) (⟦t⟧ r ⟦a⟧)

  ⟦ren⟧ : ∀ {A Γ Δ}(r : Γ ⊆ Δ) (t : Tm Γ A) → ⟦ A ⟧ t → ⟦ A ⟧ (ren r t)
  ⟦ren⟧ r (var x) ⟦t⟧ = CR₃ _ _ (λ _ ())
  ⟦ren⟧ r (f ∙ x) ⟦t⟧ = CR₃ (ren r f ∙ ren r x) _ {!!}
  ⟦ren⟧ r (ƛ {A} t)   ⟦t⟧ r' {a} ⟦a⟧ rewrite
    ren-∘ʳ (keep {A} r') (keep {A} r) t =
    let foo = ⟦ren⟧ (keep (r' ∘ʳ r)) t {!!}
    in CR₃ (ƛ (ren (keep (r' ∘ʳ r)) t) ∙ a) _ {!!}
  -- ⟦ren⟧ {⋆}     r a sna = {!!}
  -- ⟦ren⟧ {A ⇒ B} r t ⟦t⟧ r' {a} ⟦a⟧ rewrite ren-∘ʳ r' r t =
  --   CR₃ (ren (r' ∘ʳ r) t ∙ a) _ {!!}

  -- maybe strong normalization could include renaming? (ugh)
  CR₃ : ∀ {A Γ} (t : Tm Γ A) → neu t → (∀ {Δ}(r : Γ ⊆ Δ){t'} → ren r t ~> t' → ⟦ A ⟧ t') → ⟦ A ⟧ t
  CR₃ {⋆}     t nt f = sn (λ {t'} t~>t' → f refl (subst (_~> t') (sym $ ren-refl t) t~>t'))
  CR₃ {A ⇒ B} t nt f {Δ} r {a} ⟦a⟧ = CR₃ {B} (ren r t ∙ a) _
    (λ {Δ'} r' {t'} step →
    go t nt f (r' ∘ʳ r) refl {ren r' a} (⟦ren⟧ r' _ ⟦a⟧) (CR₁ (⟦ren⟧ r' _ ⟦a⟧)) {t'}
    (subst (λ x → x ∙ _ ~> _) (ren-∘ʳ r' r t) step))
    where
      go :
        ∀{Γ Δ}(t : Tm Γ (A ⇒ B))
        → neu t
        → (∀ {Δ}(r : Γ ⊆ Δ){t'} → ren r t ~> t' → ⟦ A ⇒ B ⟧ t')
        → (r : Γ ⊆ Δ)
        → {rt : Tm Δ (A ⇒ B)}
        → rt ≡ ren r t
        → {a : Tm Δ A}
        → ⟦ A ⟧ a
        → SN a
        → {t' : Tm Δ B} → rt ∙ a ~> t' → ⟦ B ⟧ t'
        
      go (var _) _ _ _ () _ _ (β _ _)
      go (_ ∙ _) _ _ _ () _ _ (β _ _)
      go (ƛ _)   () _ _ _ _ _ (β _ _)
      
      go t nt f r refl ⟦a⟧ sna (∙₁ t' rt~>t') =
        subst (λ x → ⟦ _ ⟧ (x ∙ _)) (ren-refl t') (f r rt~>t' refl ⟦a⟧)
      go t nt f r refl ⟦a⟧ (sn sna) (∙₂ a' a~>a')  =
        CR₃ {B} (ren r t ∙ a') _
        (λ {Δ'} r' {t'} step →
          go t nt f (r' ∘ʳ r) refl {ren r' a'}
          (⟦ren⟧ r' a' (CR₂ a~>a' ⟦a⟧)) {!sna a~>a'!} {t'} -- ⟦ren⟧ again + renaming SN
          (subst (λ x → x ∙ _ ~> _) (ren-∘ʳ r' r t) step))        

--------------------------------------------------------------------------------

⟦_⟧ˢ : ∀ {Γ Δ} → Sub Γ Δ → Set
⟦ ε     ⟧ˢ = ⊤
⟦ δ ▷ t ⟧ˢ = ⟦ δ ⟧ˢ × ⟦ _ ⟧ t

⟦ƛ⟧ :
  ∀ {A B Γ Δ}{δ : Sub Γ Δ}{t : Tm (Δ ▷ A) B}
  → ⟦ δ ⟧ˢ → ∀ {a} → ⟦ A ⟧ a
  → ⟦ B ⟧ (sub (δ ▷ a) t)
  → ⟦ B ⟧ (ƛ (sub (wk δ) t) ∙ a)
⟦ƛ⟧ ⟦δ⟧ ⟦a⟧ ⟦t⟧ = {!!}

⟦sub-∈⟧ : ∀ {A Γ Δ}{δ : Sub Δ Γ} → ⟦ δ ⟧ˢ → (v : A ∈ Γ) → ⟦ A ⟧ (sub-∈ δ v)
⟦sub-∈⟧ {δ = δ ▷ t} (_   , ⟦t⟧) vz     = ⟦t⟧
⟦sub-∈⟧ {δ = δ ▷ t} (⟦δ⟧ , _)   (vs v) = ⟦sub-∈⟧ ⟦δ⟧ v

-- ⟦ren⟧ : ∀ {Γ Δ A}(r : Γ ⊆ Δ){t : Tm Γ A} → ⟦ A ⟧ t → ⟦ A ⟧ (ren r t)
-- ⟦ren⟧ r {t} ⟦t⟧ = {!!}

⟦ren-Sub⟧ : ∀ {Γ Δ Ξ}{δ : Sub Γ Δ} → ⟦ δ ⟧ˢ → (r : Γ ⊆ Ξ) → ⟦ ren-Sub r δ ⟧ˢ
⟦ren-Sub⟧ {δ = ε}     ⟦δ⟧         r = tt
⟦ren-Sub⟧ {δ = δ ▷ t} (⟦δ⟧ , ⟦t⟧) r = ⟦ren-Sub⟧ ⟦δ⟧ r , ⟦ren⟧ r t ⟦t⟧

⟦_⟧ᵗ : ∀ {A Γ Δ}(t : Tm Γ A) → {δ : Sub Δ Γ} → ⟦ δ ⟧ˢ → ⟦ A ⟧ (sub δ t)
⟦ var v ⟧ᵗ ⟦δ⟧ = ⟦sub-∈⟧ ⟦δ⟧ v
⟦ f ∙ x ⟧ᵗ ⟦δ⟧ = subst (λ x → ⟦ _ ⟧ (x ∙ _)) (ren-refl _) (⟦ f ⟧ᵗ ⟦δ⟧ refl (⟦ x ⟧ᵗ ⟦δ⟧))
⟦ ƛ t   ⟧ᵗ ⟦δ⟧ = λ r ⟦a⟧ → {!!} -- ren-sub etc needed

