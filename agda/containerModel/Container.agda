{-# OPTIONS --type-in-type #-}

open import Relation.Binary.PropositionalEquality
  renaming (trans to infixr 4 _◾_; subst to tr; cong to ap; sym to infix 6 _⁻¹)
open import Data.Unit
open import Data.Empty
open import Data.Product renaming (proj₁ to ₁; proj₂ to ₂)
open import Data.Sum
open import Function using (_∋_)
open import Level
import Axiom.Extensionality.Propositional as Axiom

-- File based on: https://gist.github.com/bobatkey/0d1f04057939905d35699f1b1c323736

--------------------------------------------------------------------------------

coe : ∀ {i}{A B : Set i} → A ≡ B → A → B
coe refl x = x

J⁻¹ :
  ∀ {α β}{A : Set α} {x : A}(P : ∀ y → x ≡ y → Set β)
  → {y : A} → (w : x ≡ y) → P y w → P x refl
J⁻¹ P refl p = p

UIP : ∀ {i}{A : Set i}{x y : A}(p q : x ≡ y) → p ≡ q
UIP refl refl = refl

⊎-elim : ∀ {i j k}{A : Set i}{B : Set j}(P : A ⊎ B → Set k)
         → (∀ a → P (inj₁ a))
         → (∀ b → P (inj₂ b))
         → ∀ ab → P ab
⊎-elim P l r (inj₁ x) = l x
⊎-elim P l r (inj₂ y) = r y

⊎-map : {A A' B B' : Set} → (A → A') → (B → B') → A ⊎ B → A' ⊎ B'
⊎-map f g (inj₁ x) = inj₁ (f x )
⊎-map f g (inj₂ y) = inj₂ (g y)

⊎-disjoint : ∀ {i j}{A : Set i}{B : Set j}{x : A}{y : B} → inj₁ x ≢ inj₂ y
⊎-disjoint ()

postulate
  ext  : ∀ {i j} → Axiom.Extensionality i j
  exti : ∀ {i j} → Axiom.ExtensionalityImplicit i j


-- CwF
--------------------------------------------------------------------------------

record Con : Set₁ where
  constructor con
  field
    P : Set                 -- P : "proof"
    R : P → Set             -- R : "refutation"
open Con

record Sub (Γ Δ : Con) : Set where
  constructor sub
  field
    P : P Γ → P Δ
    R : ∀ {γ} → R Δ (P γ) → R Γ γ      -- reverse direction
open Sub

-- CwF of containers: Σ(S : Set) × ((S → Set)ᵒᵖ)
-- we can't reverse dependent morphisms!
-- the fibered part is only simply typed (democratic) CwF
--   Tm Γ A  --->  Tm A Γ

record Ty (Γ : Con) : Set₁ where
  constructor ty
  field
    P : Con.P Γ → Set
    R : ∀ {γ : Con.P Γ}(α : P γ) → Set                       -- simply typed
    -- R : ∀ {γ : Con.P Γ}(γ* : Con.R Γ γ)(α : P γ) → Set    -- full CwF fibration
open Ty

record Tm (Γ : Con) (A : Ty Γ) : Set₁ where
  constructor tm
  field
    P : (γ : P Γ) → P A γ
    R : ∀ {γ} → R A {γ} (P γ) → R Γ γ
open Tm


abstract
  Sub≡ : ∀ {Γ Δ}{σ₀ σ₁ : Sub Γ Δ}
           (q₀₁ : ∀ γ → P σ₀ γ ≡ P σ₁ γ)
         → (∀ γ α → R σ₀ {γ} α ≡ R σ₁ (tr (R Δ) (q₀₁ γ) α))
         → σ₀ ≡ σ₁
  Sub≡ {Γ} {Δ} {sub q₀ r₀} {sub q₁ r₁} q₀₁ r₀₁ with ext q₀₁
  ... | refl = ap (sub q₀) (exti (λ {γ} → ext λ α →
                  r₀₁ _ α ◾ ap r₁ (tr (λ p → tr (R Δ) p α ≡ α) (UIP _ _) refl)))

  Ty≡ : ∀ {Γ}{A₀ A₁ : Ty Γ}(q₀₁ : ∀ γ → P A₀ γ ≡ P A₁ γ)
        → (∀ γ α → R A₀ {γ} α ≡ R A₁ (coe (q₀₁ γ) α)) → A₀ ≡ A₁
  Ty≡ {Γ} {ty q₀ r₀} {ty q₁ r₁} q₀₁ r₀₁ with ext q₀₁
  ... | refl = ap (ty q₀) (exti λ {γ} → ext λ α →
                 r₀₁ γ α ◾ ap r₁ (tr (λ p → coe p α ≡ α) (UIP _ _) refl))

  Tm≡ : ∀ {Γ A}{t₀ t₁ : Tm Γ A}
           (q₀₁ : ∀ γ → P t₀ γ ≡ P t₁ γ)
         → (∀ γ α → R t₀ {γ} α ≡ R t₁ (tr (R A) (q₀₁ γ) α))
         → t₀ ≡ t₁
  Tm≡ {Γ}{A}{tm q₀ r₀} {tm q₁ r₁} q₀₁ r₀₁ with ext q₀₁
  ... | refl = ap (tm q₀) (exti λ {γ} → ext λ α →
                 r₀₁ γ α ◾ ap r₁ (tr (λ p → tr (R A) p α ≡ α) (UIP _ _) refl))

∙ : Con
∙ = con ⊤ (λ _ → ⊥)

ε : ∀ {Γ} → Sub Γ ∙
ε = sub _ ⊥-elim

εη : ∀ {Γ}{σ : Sub Γ ∙} → σ ≡ ε
εη {Γ} {σ} = Sub≡ (λ _ → refl) (λ γ ∙* → ⊥-elim ∙*)

id : ∀ {Γ} → Sub Γ Γ
id {Γ} = sub (λ γ → γ) (λ γ* → γ*)

infixr 5 _∘_
_∘_ : ∀ {Γ Δ Σ} → Sub Δ Σ → Sub Γ Δ → Sub Γ Σ
sub q₀ r₀ ∘ sub q₁ r₁ = sub (λ γ → q₀ (q₁ γ)) (λ σ* → r₁ (r₀ σ*))

idl : ∀ {Γ Δ}{σ : Sub Γ Δ} → id ∘ σ ≡ σ
idl = refl

idr : ∀ {Γ Δ}{σ : Sub Γ Δ} → σ ∘ id ≡ σ
idr = refl

ass : ∀ {Γ Δ Σ Ξ}{σ : Sub Σ Ξ}{δ : Sub Δ Σ}{ν : Sub Γ Δ} → (σ ∘ δ) ∘ ν ≡ σ ∘ δ ∘ ν
ass = refl

infix 6 _[_]T
_[_]T : ∀ {Γ Δ} → Ty Δ → Sub Γ Δ → Ty Γ
_[_]T {Γ} {Δ} A σ = ty (λ γ → P A (P σ γ)) (R A)

[id]T : ∀ {Γ}{A : Ty Γ} → A [ id ]T ≡ A
[id]T = refl

[∘]T : ∀ {Γ Δ Σ}{A : Ty Σ}{σ : Sub Δ Σ}{δ : Sub Γ Δ} → A [ σ ]T [ δ ]T ≡ A [ σ ∘ δ ]T
[∘]T = refl

infix 6 _[_]t
_[_]t : ∀ {Γ Δ A}(t : Tm Δ A)(σ : Sub Γ Δ) → Tm Γ (A [ σ ]T)
_[_]t t σ = tm (λ γ → P t (P σ γ)) (λ α* → R σ (R t α*))

infixl 3 _▶_
_▶_ : (Γ : Con) → Ty Γ → Con
Γ ▶ A = con (Σ (P Γ) (P A)) (λ {(γ* , α*) → R Γ γ* ⊎ R A α*})

π₁ : ∀ {Γ Δ A} → Sub Γ (Δ ▶ A) → Sub Γ Δ
π₁ σ = sub (λ γ → ₁ (P σ γ)) (λ δ* → R σ (inj₁ δ*))

π₂ : ∀ {Γ Δ A}(σ : Sub Γ (Δ ▶ A)) → Tm Γ (A [ π₁ σ ]T)
π₂ σ = tm (λ γ → ₂ (P σ γ)) (λ α* → R σ (inj₂ α*))

infixl 3 _,ₛ_
_,ₛ_ : ∀ {Γ Δ A}(σ : Sub Γ Δ) → Tm Γ (A [ σ ]T) → Sub Γ (Δ ▶ A)
_,ₛ_ σ t = sub (λ γ → (P σ γ) , (P t γ)) (⊎-elim _ (R σ) (R t))

π₁β : ∀ {Γ Δ A}{σ : Sub Γ Δ}{t : Tm Γ (A [ σ ]T)} → π₁ {A = A}(σ ,ₛ t) ≡ σ
π₁β {Γ} {Δ} {A} {σ} {t} = refl

π₂β : ∀ {Γ Δ A}{σ : Sub Γ Δ}{t : Tm Γ (A [ σ ]T)} → π₂ {A = A}(σ ,ₛ t) ≡ t
π₂β {Γ} {Δ} {A} {σ} {t} = refl

,ₛη : ∀ {Γ Δ A}{σ : Sub Γ (Δ ▶ A)} → (π₁ σ ,ₛ π₂ σ) ≡ σ
,ₛη {Γ} {Δ} {A} {σ} =
  Sub≡ (λ _ → refl)
       (λ γ → ⊎-elim (λ α* → ⊎-elim (λ _ → R Γ γ) (λ α* → R σ (inj₁ α*))
                                    (λ α* → R σ (inj₂ α*)) α* ≡ R σ α*)
                 (λ _ → refl)
                 (λ _ → refl))

π₁∘ : ∀ {Γ Δ Σ A}{σ : Sub Δ (Σ ▶ A)}{δ : Sub Γ Δ} → π₁ σ ∘ δ ≡ π₁ (σ ∘ δ)
π₁∘ = refl

π₂∘ : ∀ {Γ Δ Σ A}{σ : Sub Δ (Σ ▶ A)}{δ : Sub Γ Δ} → π₂ σ [ δ ]t ≡ π₂ (σ ∘ δ)
π₂∘ = refl

--------------------------------------------------------------------------------

-- Tm (Γ ▶ A) B ≃ Tm Γ (Π A B)

-- Tm (Γ ▶ A) B   -- usual forward function
--                -- + reverse function: R B → R Γ + R A

-- t : Tm Γ (Π A B)      -- P component contains also a backward function
-- app t : Tm (Γ ▶ A) B  -- P component only contains a forward

Π : ∀ {Γ}(A : Ty Γ) → Ty (Γ ▶ A) → Ty Γ
P (Π {Γ} A B) γ =
  ∃ λ (f : (α : P A γ) → P B (γ , α)) →
      (∀ {α} → R B (f α) → ⊤ ⊎ R A α)  -- R B → Maybe (R A)

R (Π {Γ} A B) {γ} (f , pf) =
  ∃₂ λ (α : P A γ)(fα* : R B (f α)) → pf fα* ≡ inj₁ tt

Π[] : ∀ {Γ Δ}{σ : Sub Γ Δ}{A B} → Π {Δ} A B [ σ ]T ≡ Π (A [ σ ]T) (B [ σ ∘ π₁ id ,ₛ π₂ id ]T)
Π[] = refl

app : ∀ {Γ A B} → Tm Γ (Π A B) → Tm (Γ ▶ A) B
P (app t) (γ , α)   = ₁ (P t γ) α
R (app {Γ} {A} {B} t) {γ , α} β =
  ⊎-elim (λ ab → ₂ (P t γ) β ≡ ab → R (Γ ▶ A) (γ , α))
         (λ _ p → inj₁ (R t (α , β , p)))
         (λ α* p → inj₂ α*)
         (₂ (P t γ) β) refl

lam : ∀ {Γ A B} → Tm (Γ ▶ A) B → Tm Γ (Π A B)
P (lam t) γ = (λ x → P t (γ , x)) , λ β* → ⊎-map _ (λ α* → α*) (R t β*)
R (lam {Γ} {A} {B} t) {γ} (α , β , p) =
  ⊎-elim (λ ab → ⊎-map (λ _ → tt) (λ α* → α*) ab ≡ inj₁ tt → R Γ γ)
         (λ γ* _ → γ*) (λ b p → ⊥-elim (⊎-disjoint (p ⁻¹)))
         (R t β) p

Πβ : ∀ {Γ A B t} → app (lam {Γ}{A}{B} t) ≡ t
Πβ {Γ} {A} {B} {t} =
  Tm≡ (λ _ → refl) (λ {(γ , α) α* →
     ⊎-elim (λ rtα* → ⊎-elim
              (λ ab → ⊎-map (λ _ → tt) (λ α*₁ → α*₁) rtα* ≡ ab → R Γ γ ⊎ R A α) (λ _ p →
                 inj₁ (⊎-elim (λ ab → ⊎-map (λ _ → tt) (λ α*₁ → α*₁) ab ≡ inj₁ tt → R Γ
                 γ) (λ γ* _ → γ*) (λ b p₁ → ⊥-elim (⊎-disjoint (p₁ ⁻¹))) rtα* p)) (λ α*₁
                 p → inj₂ α*₁) (⊎-map (λ _ → tt) (λ α*₁ → α*₁) rtα*) refl ≡ rtα*)
             (λ _ → refl) (λ _ → refl)
             (R t α*)})

-- also possible, see Bob Atkey formalization
Πη : ∀ {Γ A B t} → lam {Γ}{A}{B} (app t) ≡ t
Πη = {!!}

--------------------------------------------------------------------------------

Bot : ∀ {Γ} → Ty Γ
Bot {Γ} = ty (λ _ → ⊥) (λ _ → ⊤)

BotElim : ∀ {Γ}(A : Ty Γ) → Tm Γ Bot → Tm Γ A
BotElim {Γ} A t = tm (λ γ → ⊥-elim (P t γ)) λ {γ} _ → ⊥-elim (P t γ)

--------------------------------------------------------------------------------

U : ∀ {Γ} → Ty Γ
U {Γ} = ty (λ _ → Σ Set λ A → A → Set) (λ _ → ⊥)

El : ∀ {Γ} → Tm Γ U → Ty Γ
El {Γ} A = ty (λ γ → ₁ (P A γ)) (λ {γ} α → ₂ (P A γ) α)

El[] : ∀ {Γ Δ}{σ : Sub Γ Δ}{a} → (El {Δ} a) [ σ ]T ≡ El (a [ σ ]t)
El[] = refl

c : ∀ {Γ} → Ty Γ → Tm Γ U
c {Γ} A = tm (λ γ → (P A γ) , R A) ⊥-elim

cEl : ∀ {Γ a} → c (El {Γ} a) ≡ a
cEl {Γ} {a} = Tm≡ (λ _ → refl) (λ _ ())

Elc : ∀ {Γ A} → El {Γ} (c A) ≡ A
Elc {Γ} {A} = refl

--------------------------------------------------------------------------------

Eq : ∀ {Γ A} → Tm Γ A → Tm Γ A → Ty Γ
Eq {Γ}{A} t u = ty (λ γ → P t γ ≡ P u γ) (λ _ → ⊥)

Refl : ∀ {Γ A}(t : Tm Γ A) → Tm Γ (Eq t t)
Refl t = tm (λ _ → refl) ⊥-elim

UIP' : ∀ {Γ A}{t u : Tm Γ A}{e e' : Tm Γ (Eq t u)} → Tm Γ (Eq e e')
UIP' {Γ} {A} {t} {u} {e} {e'} = tm (λ _ → UIP _ _) ⊥-elim

Tr : ∀ {Γ A}(B : Ty (Γ ▶ A)){t u : Tm Γ A}(e : Tm Γ (Eq t u))
     → Tm Γ (B [ id ,ₛ t ]T) → Tm Γ (B [ id ,ₛ u ]T)
Tr {Γ} {A} B e pt  =
  tm (λ γ → tr (λ x → P B (γ , x)) (P e γ) (P pt γ))
     (λ {γ} P* →
       R pt {γ} (J⁻¹ (λ _ e → R B (tr (λ x → P B (γ , x)) e (P pt γ))) (P e γ)
                     P*))

-- Σ
--------------------------------------------------------------------------------

Sg : ∀ {Γ}(A : Ty Γ) → Ty (Γ ▶ A) → Ty Γ
Sg A B = ty (λ γ → Σ (P A γ) λ α → P B (γ , α))
            (λ {(α , β) → R A α ⊎ R B β})

Proj1 : ∀ {Γ A B} → Tm Γ (Sg A B) → Tm Γ A
Proj1 t = tm (λ γ → ₁ (P t γ)) (λ α* → R t (inj₁ α*))

Proj2 : ∀ {Γ A B}(t : Tm Γ (Sg A B)) → Tm Γ (B [ id ,ₛ Proj1 t ]T)
Proj2 t = tm (λ γ → ₂ (P t γ)) (λ β* → R t (inj₂ β*))

Pair : ∀ {Γ A B}(t : Tm Γ A) → Tm Γ (B [ id ,ₛ t ]T) → Tm Γ (Sg A B)
Pair t u = tm (λ γ → P t γ , P u γ) (⊎-elim _ (R t) (R u))

--------------------------------------------------------------------------------
module NoFunExt where

  FunExtTy : Set
  FunExtTy = ∀ {Γ A B}(f g : Tm Γ (Π A B))
           → Tm (Γ ▶ A) (Eq (app {Γ}{A}{B} f) (app {Γ}{A}{B} g))
           → Tm Γ (Eq f g)

  open import Data.Bool

  A : Ty ∙
  A = ty (λ _ → ⊤) (λ _ → Bool)

  B : Ty (∙ ▶ A)
  B = ty (λ _ → ⊤) (λ _ → ⊤)

  f : Tm ∙ (Π A B)
  f = tm (λ γ → (λ _ → tt) , (λ _ → inj₂ true)) (λ ())

  g : Tm ∙ (Π A B)
  g = tm (λ γ → (λ _ → tt) , (λ _ → inj₂ false)) (λ ())

  e : Tm (∙ ▶ A) (Eq (app f) (app g))
  e = Refl (app f)

  ¬FunExt : FunExtTy → ⊥
  ¬FunExt funext with ap (λ f → ₂ f tt) (P (funext f g (Refl (app f))) tt)
  ... | ()

-- t : Tm (∙ ▶ ⊥ ▶ ⊥) ⊥
-- we don't get an interesting refutation!
