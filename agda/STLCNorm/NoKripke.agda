
module NoKripke where

open import Data.Product renaming (map to pmap)
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Data.Sum renaming (map to smap) hiding ([_,_])
open import Function using (_$_; id; _∘_)
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

renˢ : ∀ {Γ Δ Ξ} → Γ ⊆ Ξ → Sub Γ Δ → Sub Ξ Δ
renˢ r ε       = ε
renˢ r (δ ▷ t) = renˢ r δ ▷ ren r t

wk : ∀ {A Γ Δ} → Sub Γ Δ → Sub (Γ ▷ A) (Δ ▷ A)
wk δ = renˢ (add refl) δ ▷ var vz

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
  β  : ∀ {A B}{t : Tm (Γ ▷ A) B} t'                →  ƛ t ∙ t' ~> inst t' t
  ƛ  : ∀ {A B}{t : Tm (Γ ▷ A) B} t'      → t ~> t' →  ƛ t      ~> ƛ t'
  ∙₁ : ∀ {A B}{f} (f' : Tm Γ (A ⇒ B)){x} → f ~> f' →  (f ∙ x)  ~> (f' ∙ x)
  ∙₂ : ∀ {A B}{f : Tm Γ (A ⇒ B)} {x} x'  → x ~> x' →  (f ∙ x)  ~> (f ∙ x')
infix 3 _~>_

-- Strong normalization
--------------------------------------------------------------------------------

data SN {Γ A} (t : Tm Γ A) : Set where
  sn : (∀ {t'} → t ~> t' → SN t') → SN t
-- (AGDA BUG : if SN is an inductive record, CR₃ fails termination check)

ƛ-SN→ : ∀ {Γ A B}{t : Tm (Γ ▷ A) B} → SN t → SN (ƛ t)
ƛ-SN→ (sn s) = sn λ {(ƛ _ t~>t') → ƛ-SN→ (s t~>t')}

ƛ-SN← : ∀ {Γ A B}{t : Tm (Γ ▷ A) B} → SN (ƛ t) → SN t
ƛ-SN← (sn s) = sn λ t~>t' → ƛ-SN← (s (ƛ _ t~>t'))

∙-SN← : ∀ {Γ A B}{f : Tm Γ (A ⇒ B)}{x} → SN (f ∙ x) → SN f × SN x
∙-SN← (sn s) =
  sn (λ f~>f' → proj₁ (∙-SN← (s (∙₁ _ f~>f')))) ,
  sn (λ x~>x' → proj₂ (∙-SN← (s (∙₂ _ x~>x'))))

neu : ∀ {Γ A} → Tm Γ A → Set
neu (var _) = ⊤
neu (_ ∙ _) = ⊤
neu (ƛ _)   = ⊥

--------------------------------------------------------------------------------

⟦_⟧ : (A : Ty) → ∀ {Γ} → Tm Γ A → Set
⟦ ⋆     ⟧ = SN
⟦ A ⇒ B ⟧ = λ f → SN f × (∀ a → ⟦ A ⟧ a → ⟦ B ⟧ (f ∙ a))

mutual
  CR₁ : ∀ {Γ} {A t} → ⟦ A ⟧ {Γ} t → SN t
  CR₁ {A = ⋆}     = id
  CR₁ {A = A ⇒ B} = proj₁

  CR₂ : ∀ {Γ} {A t t'} → t ~> t' → ⟦ A ⟧ {Γ} t → ⟦ A ⟧ t'
  CR₂ {A = ⋆}     t~>t' (sn n)       = n t~>t'
  CR₂ {A = A ⇒ B} t~>t' (sn st , rt) = st t~>t' , λ a ra → CR₂ (∙₁ _ t~>t') (rt a ra)

  CR₃ : ∀ {Γ A}(t : Tm Γ A) → neu t → (∀ {t'} → t ~> t' → ⟦ A ⟧ t') → ⟦ A ⟧ t
  CR₃ {A = ⋆}     t nt f = sn f
  CR₃ {A = A ⇒ B} t nt f = sn (proj₁ ∘ f) , λ a ra → CR₃ (t ∙ a) _ (go nt f a ra (CR₁ ra) _)
    where
      go :
        ∀ {Γ A B}{t : Tm Γ (A ⇒ B)} → neu t → (∀ {t'} → t ~> t' → ⟦ A ⇒ B ⟧ t')
        → ∀ a → ⟦ A ⟧ a → SN a → ∀ t' → t ∙ a ~> t' → ⟦ B ⟧ t'
      go () _   _ _  _      _ (β _)
      go nt f a ra sna      _ (∙₁ t' t~>t') = proj₂ (f t~>t') a ra
      go nt f a ra (sn sna) _ (∙₂ a' a~>a') =
        CR₃ (_ ∙ a') _ (go nt f a' (CR₂ a~>a' ra) (sna a~>a') _)

--------------------------------------------------------------------------------

⟦_⟧ˢ : ∀ {Γ Δ} → Sub Γ Δ → Set
⟦ ε     ⟧ˢ = ⊤
⟦ δ ▷ t ⟧ˢ = ⟦ δ ⟧ˢ × ⟦ _ ⟧ t

-- Single substitution is provable
⟦ƛ⟧ :
  ∀ {Γ A B}
  → (b : Tm (Γ ▷ A) B) → ⟦ B ⟧ b → SN b
  → (∀ a → ⟦ A ⟧ a → ⟦ B ⟧ (inst a b))
  → ∀ a → ⟦ A ⟧ a → ⟦ B ⟧ (ƛ b ∙ a)
⟦ƛ⟧ b ⟦b⟧ snb f a ⟦a⟧ = go b ⟦b⟧ snb f a ⟦a⟧ (CR₁ ⟦a⟧)
  where
    go :
      ∀ {Γ A B}
      → (b : Tm (Γ ▷ A) B) → ⟦ B ⟧ b → SN b
      → (∀ a → ⟦ A ⟧ a → ⟦ B ⟧ (inst a b))
      → ∀ a → ⟦ A ⟧ a → SN a → ⟦ B ⟧ (ƛ b ∙ a)
    go {Γ}{A}{B} b ⟦b⟧ (sn snb) f a ⟦a⟧ (sn sna) = CR₃ (ƛ b ∙ a) _
      (λ {(β _)               → f a ⟦a⟧;
          (∙₁ _ (ƛ b' b~>b')) →
            -- provable
            go b' (CR₂ b~>b' ⟦b⟧) (snb b~>b') (λ a ⟦a⟧ → {!f a ⟦a⟧!}) a ⟦a⟧ (sn sna);
          (∙₂ a' a~>a')       → go b ⟦b⟧ (sn snb) f a' (CR₂ a~>a' ⟦a⟧) (sna a~>a')})


-- MUTLI sub: I don't see exactly how yet
-- NOTE : we could push the δ substitution inside the "f" arg, thereby strenghtening
-- the premise (we can get this from ⟦_⟧ᵗ)
go :
  ∀ {Γ Δ A B}
  → {δ : Sub Δ Γ} → ⟦ δ ⟧ˢ
  → (t : Tm (Γ ▷ A) B) → ⟦ B ⟧ (sub (wk δ) t) → SN (sub (wk δ) t)
  → (∀ {a} → ⟦ A ⟧ a → ⟦ B ⟧ (sub (δ ▷ a) t))
  → (∀ {a} → ⟦ A ⟧ a → SN a → ⟦ B ⟧ (ƛ (sub (wk δ) t) ∙ a))
go {δ = δ} ⟦δ⟧ t ⟦t⟧ (sn snt) f {a} ⟦a⟧ (sn sna) = CR₃ (ƛ (sub (wk δ) t) ∙ a) _
  (λ {
    (∙₁ _ (ƛ t' t~>t')) → {!go ⟦δ⟧ !}; -- probably much harder than single sub, but provable
    (∙₂ a' a~>a' )      → go ⟦δ⟧ t ⟦t⟧ (sn snt) f {a'} (CR₂ a~>a' ⟦a⟧) (sna a~>a');
    (β  a )             → {! f ⟦a⟧!}}) -- TODO (doable and not very hard)


-- NO IDEA ABOUT THIS
⟦ren⟧ : ∀ {Γ Δ A}(r : Γ ⊆ Δ){t : Tm Γ A} → ⟦ A ⟧ t → ⟦ A ⟧ (ren r t)
⟦ren⟧ = {!!}

⟦var⟧ : ∀ {Γ A} → (v : A ∈ Γ) → ⟦ A ⟧ (var v)
⟦var⟧ v = CR₃ (var v) _ (λ ())

⟦sub-∈⟧ : ∀ {A Γ Δ}{δ : Sub Δ Γ} → ⟦ δ ⟧ˢ → (v : A ∈ Γ) → ⟦ A ⟧ (sub-∈ δ v)
⟦sub-∈⟧ {δ = δ ▷ t} (_   , ⟦t⟧) vz     = ⟦t⟧
⟦sub-∈⟧ {δ = δ ▷ t} (⟦δ⟧ , _)   (vs v) = ⟦sub-∈⟧ ⟦δ⟧ v

⟦renˢ⟧ : ∀ {Γ Δ Ξ}{δ : Sub Γ Δ} → ⟦ δ ⟧ˢ → (r : Γ ⊆ Ξ) → ⟦ renˢ r δ ⟧ˢ
⟦renˢ⟧ {δ = ε}     ⟦δ⟧         r = tt
⟦renˢ⟧ {δ = δ ▷ t} (⟦δ⟧ , ⟦t⟧) r = ⟦renˢ⟧ ⟦δ⟧ r , ⟦ren⟧ r {t} ⟦t⟧

⟦wk⟧ : ∀ {A Γ Δ}{δ : Sub Γ Δ} → ⟦ δ ⟧ˢ → ⟦ wk {A} δ ⟧ˢ
⟦wk⟧ {A} ⟦δ⟧ = ⟦renˢ⟧ ⟦δ⟧ (add refl) , ⟦var⟧ (vz {A})


⟦_⟧ᵗ : ∀ {A Γ Δ}(t : Tm Γ A) → {δ : Sub Δ Γ} → ⟦ δ ⟧ˢ → ⟦ A ⟧ (sub δ t)
⟦ var v  ⟧ᵗ ⟦δ⟧ = ⟦sub-∈⟧ ⟦δ⟧ v
⟦ f ∙ x  ⟧ᵗ ⟦δ⟧ = proj₂ (⟦ f ⟧ᵗ ⟦δ⟧) _ (⟦ x ⟧ᵗ ⟦δ⟧)
⟦ ƛ t    ⟧ᵗ ⟦δ⟧ =
   ƛ-SN→ (CR₁ (⟦ t ⟧ᵗ (⟦wk⟧ ⟦δ⟧))) , {!⟦ t ⟧ᵗ!}

--  (λ a ⟦a⟧ → ⟦ƛ⟧ t ⟦δ⟧ ⟦a⟧ (⟦ t ⟧ᵗ (⟦δ⟧ , ⟦a⟧)))


