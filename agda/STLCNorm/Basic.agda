module Basic where

open import Data.Product renaming (map to pmap)
open import Relation.Binary.PropositionalEquality
open import Data.Sum renaming (map to smap)
import Function as F
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

-- Constructor injectivity
--------------------------------------------------------------------------------

vs-inj : ∀ {Γ A B}{v v' : A ∈ Γ} → vs_ {B = B} v ≡ vs v' → v ≡ v'
vs-inj refl = refl

var-inj : ∀ {Γ A} {v v' : A ∈ Γ} → var v ≡ var v' → v ≡ v'
var-inj refl = refl

∙-inj :
  ∀ {Γ A A' B}{f : Tm Γ (A ⇒ B)}{f' : Tm Γ (A' ⇒ B)}{x : Tm Γ A}{x' : Tm Γ A'}
  → f ∙ x ≡ f' ∙ x'
  → ∃ λ (p : A ≡ A') → subst (λ x → Tm Γ (x ⇒ B)) p f ≡ f' × subst (Tm Γ) p x ≡ x'
∙-inj refl = refl , refl , refl

ƛ-inj : ∀ {Γ A B}{t t' : Tm (Γ ▷ A) B} → ƛ t ≡ ƛ t' → t ≡ t'
ƛ-inj refl = refl

-- Renaming & Substitution
--------------------------------------------------------------------------------

data _⊆_ : Con → Con → Set where
  refl : ∀ {Γ} → Γ ⊆ Γ
  add  : ∀ {A Γ Δ} → Γ ⊆ Δ → Γ     ⊆ Δ ▷ A
  keep : ∀ {A Γ Δ} → Γ ⊆ Δ → Γ ▷ A ⊆ Δ ▷ A
infix 2 _⊆_

_∘_ : ∀ {Γ Δ Ξ} → Δ ⊆ Ξ → Γ ⊆ Δ → Γ ⊆ Ξ
refl   ∘ r'      = r'
add r  ∘ r'      = add (r ∘ r')
keep r ∘ refl    = keep r
keep r ∘ add r'  = add (r ∘ r')
keep r ∘ keep r' = keep (r ∘ r')
infixr 9 _∘_

ren-∈ : ∀ {A Γ Δ} → Γ ⊆ Δ → A ∈ Γ → A ∈ Δ
ren-∈ refl     v      = v
ren-∈ (add r)  v      = vs ren-∈ r v
ren-∈ (keep r) vz     = vz
ren-∈ (keep r) (vs v) = vs ren-∈ r v

ren : ∀ {A Γ Δ} → Γ ⊆ Δ → Tm Γ A → Tm Δ A
ren r (var v) = var (ren-∈ r v)
ren r (f ∙ x) = ren r f ∙ ren r x
ren r (ƛ t)   = ƛ (ren (keep r) t)

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
∈-eq (vs v) (vs v') = smap F.id vs_ (∈-eq v v')

drop-sub-⊆ : ∀ {Γ A}(v : A ∈ Γ) → drop v ⊆ subᶜ v
drop-sub-⊆ vz     = refl
drop-sub-⊆ (vs v) = add (drop-sub-⊆ v)

sub : ∀ {Γ A B}(v : A ∈ Γ) → Tm (drop v) A → Tm Γ B → Tm (subᶜ v) B
sub v t' (f ∙ x) = sub v t' f ∙ sub v t' x
sub v t' (ƛ t)   = ƛ (sub (vs v) t' t)
sub v t' (var v') with ∈-eq v v'
... | inj₁ refl = ren (drop-sub-⊆ v) t'
... | inj₂ v''  = var v''

-- Categorical renaming
--------------------------------------------------------------------------------

∘-refl : ∀ {Γ Δ} (r : Γ ⊆ Δ) → r ∘ refl ≡ r
∘-refl refl     = refl
∘-refl (add r)  = cong add (∘-refl r)
∘-refl (keep r) = refl

ren-∈-∘ :
  ∀ {Γ Δ Ξ A} (r : Δ ⊆ Ξ) (r' : Γ ⊆ Δ) (v : A ∈ Γ)
  → ren-∈ r (ren-∈ r' v) ≡ ren-∈ (r ∘ r') v
ren-∈-∘ refl     r'        v      = refl
ren-∈-∘ (add r)  r'        v      = cong vs_ (ren-∈-∘ r r' v)
ren-∈-∘ (keep r) refl      v      = refl
ren-∈-∘ (keep r) (add r')  v      = cong vs_ (ren-∈-∘ r r' v)
ren-∈-∘ (keep r) (keep r') vz     = refl
ren-∈-∘ (keep r) (keep r') (vs v) = ren-∈-∘ (add r) r' v

ren-∘ : ∀ {Γ Δ Ξ A}(r : Δ ⊆ Ξ)(r' : Γ ⊆ Δ)(t : Tm Γ A) → ren r (ren r' t) ≡ ren (r ∘ r') t
ren-∘ r r' (var v) = cong var (ren-∈-∘ r r' v)
ren-∘ r r' (f ∙ x) = cong₂ _∙_ (ren-∘ r r' f) (ren-∘ r r' x)
ren-∘ r r' (ƛ t)   = cong ƛ (ren-∘ (keep r) (keep r') t)

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

-- Renaming is injective
--------------------------------------------------------------------------------

ren-∈-inj : ∀ {Γ Δ A}(r : Γ ⊆ Δ){v v' : A ∈ Γ} → ren-∈ r v ≡ ren-∈ r v' → v ≡ v'
ren-∈-inj refl     eq = eq
ren-∈-inj (add r)  eq = ren-∈-inj r (vs-inj eq)
ren-∈-inj (keep r) {vz} {vz} eq = refl
ren-∈-inj (keep r) {vs v} {vs v'} eq = cong vs_ (ren-∈-inj r (vs-inj eq))
ren-∈-inj (keep r) {vz} {vs v'} ()
ren-∈-inj (keep r) {vs v} {vz} ()

ren-inj : ∀ {Γ Δ A}(r : Γ ⊆ Δ){t t' : Tm Γ A} → ren r t ≡ ren r t' → t ≡ t'
ren-inj r {var _} {var _}   eq = cong var (ren-∈-inj r (var-inj eq))
ren-inj r {f ∙ x} {f' ∙ x'} eq with ∙-inj eq
... | refl , eq₁ , eq₂ = cong₂ _∙_ (ren-inj r eq₁) (ren-inj r eq₂)
ren-inj r {ƛ t}   {ƛ t'}    eq = cong ƛ (ren-inj (keep r) (ƛ-inj eq))
ren-inj r {var _} {_ ∙ _} ()
ren-inj r {var _} {ƛ _}   ()
ren-inj r {_ ∙ _} {var _} ()
ren-inj r {_ ∙ _} {ƛ _}   ()
ren-inj r {ƛ _}   {var _} ()
ren-inj r {ƛ _}   {_ ∙ _} ()


-- Renaming and substitution commute
--------------------------------------------------------------------------------

ren-sub-∈ :
  ∀ {Γ Δ A B}(r : Γ ⊆ Δ) (v : A ∈ Γ) (v' : B ∈ Γ)
  → ∈-eq (ren-∈ r v) (ren-∈ r v') ≡ smap F.id (ren-∈ (⊆-subᶜ v r)) (∈-eq v v')
ren-sub-∈ refl v v' with ∈-eq v v'
... | inj₁ _ = refl
... | inj₂ _ = refl
ren-sub-∈ (add r)  v v' with ren-sub-∈ r v v' | ∈-eq v v' | inspect (∈-eq v) v'
... | rec | inj₁ _ | [ eq ] rewrite rec | eq = refl
... | rec | inj₂ _ | [ eq ] rewrite rec | eq = refl
ren-sub-∈ (keep r) (vs v) (vs v') with ren-sub-∈ r v v' | ∈-eq v v' | inspect (∈-eq v) v'
... | rec | inj₁ x | [ eq ] rewrite rec | eq = refl
... | rec | inj₂ y | [ eq ] rewrite rec | eq = refl
ren-sub-∈ (keep r) vz vz      = refl
ren-sub-∈ (keep r) vz (vs v') = refl
ren-sub-∈ (keep r) (vs v) vz  = refl

ren-drop-sub' :
  ∀ {Γ Δ A}(r : Γ ⊆ Δ)(v : A ∈ Γ)
  → (⊆-subᶜ v r ∘ drop-sub-⊆ v) ≡ (drop-sub-⊆ (ren-∈ r v) ∘ ⊆-drop v r)
ren-drop-sub' refl     v      = sym (∘-refl (drop-sub-⊆ v))
ren-drop-sub' (add r)  v      = cong add (ren-drop-sub' r v)
ren-drop-sub' (keep r) vz     = ∘-refl r
ren-drop-sub' (keep r) (vs v) = cong add (ren-drop-sub' r v)

ren-drop-sub :
  ∀ {Γ Δ A}(r : Γ ⊆ Δ)(v : A ∈ Γ)(t : Tm (drop v) A)
  → ren (⊆-subᶜ v r) (ren (drop-sub-⊆ v) t) ≡ ren (drop-sub-⊆ (ren-∈ r v)) (ren (⊆-drop v r) t)
ren-drop-sub r v t rewrite
  ren-∘ (⊆-subᶜ v r) (drop-sub-⊆ v) t | ren-∘ (drop-sub-⊆ (ren-∈ r v)) (⊆-drop v r) t
  = cong (λ x → ren x t) (ren-drop-sub' r v)

ren-sub :
  ∀ {Γ Δ A B} (r : Γ ⊆ Δ) (v : A ∈ Γ) t' (t : Tm Γ B)
  → ren (⊆-subᶜ v r) (sub v t' t) ≡ sub (ren-∈ r v) (ren (⊆-drop v r) t') (ren r t)
ren-sub r v t' (f ∙ x)  = cong₂ _∙_ (ren-sub r v t' f) (ren-sub r v t' x)
ren-sub r v t' (ƛ t)    = cong ƛ (ren-sub (keep r) (vs v) t' t)
ren-sub r v t' (var v') with ∈-eq (ren-∈ r v) (ren-∈ r v') | ∈-eq v v' | ren-sub-∈ r v v'
... | inj₁ refl | inj₁ refl | _    = ren-drop-sub r v t'
... | inj₂ _    | inj₂ v''  | refl = refl
... | inj₁ refl | inj₂ _    | ()
... | inj₂ _    | inj₁ refl | ()
