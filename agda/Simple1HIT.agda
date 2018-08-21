
{-# OPTIONS --without-K #-}

open import Relation.Binary.PropositionalEquality renaming (subst to transp; cong to ap)
open import Data.Product renaming (proj₁ to ₁; proj₂ to ₂)
open import Data.Unit

infixr 4 _◾_; _◾_ = trans
infix  6 _⁻¹; _⁻¹ = sym

apd : ∀{i j}{A : Set i}{B : A → Set j}(f : (x : A) → B x){a₀ a₁ : A}(a₂ : a₀ ≡ a₁)
    → transp B a₂ (f a₀) ≡ f a₁
apd f refl = refl

-- Syntax of declarations
--------------------------------------------------------------------------------

infixr 4 _⇒_
data U : Set₁ where
  sort : U
  _⇒_  : (A : Set) → (A → U) → U

infixr 4 _⇒'_
data Ty : Set₁ where
  El   : U → Ty
  _⇒_  : U → Ty → Ty
  _⇒'_ : (α : Set) → (α → Ty) → Ty

infixl 3 _▶_
data Con : Set₁ where
  ∙   : Con
  _▶_ : Con → Ty → Con

data Var : Con → Ty → Set₁ where
  vz : ∀ {Γ A} → Var (Γ ▶ A) A
  vs : ∀ {Γ A B} → Var Γ A → Var (Γ ▶ B) A

data Tm (Γ : Con) : Ty → Set₁ where
  var  : ∀ {A} → Var Γ A → Tm Γ A
  app  : ∀ {a B} → Tm Γ (a ⇒ B) → Tm Γ (El a) → Tm Γ B
  appU : ∀ {α b} → Tm Γ (El (α ⇒ b)) → ∀ x → Tm Γ (El (b x))
  app' : ∀ {α B} → Tm Γ (α ⇒' B) → (x : α) → Tm Γ (B x)

data EqTy (Γ : Con) : Set₁ where
  eq   : ∀ {a} → Tm Γ (El a) → Tm Γ (El a) → EqTy Γ
  _⇒'_ : (α : Set) → (α → EqTy Γ) → EqTy Γ
  _⇒_  : (a : U) → EqTy (Γ ▶ El a) → EqTy Γ

data EqCon (Γ : Con) : Set₁ where
  ∙   : EqCon Γ
  _▶_ : EqCon Γ → EqTy Γ → EqCon Γ

Decl : Set₁
Decl = Σ Con λ Γ → EqCon Γ


-- Algebras
--------------------------------------------------------------------------------

module Alg {sortᴬ : Set} where

  Uᴬ : U → Set
  Uᴬ sort    = sortᴬ
  Uᴬ (α ⇒ b) = ∀ x → Uᴬ (b x)

  Tyᴬ : Ty → Set
  Tyᴬ (El a  ) = Uᴬ a
  Tyᴬ (a ⇒  B) = Uᴬ a → Tyᴬ B
  Tyᴬ (α ⇒' B) = ∀ x → Tyᴬ (B x)

  Conᴬ : Con → Set
  Conᴬ ∙       = ⊤
  Conᴬ (Γ ▶ A) = Conᴬ Γ × Tyᴬ A

  Tmᴬ : ∀ {Γ A} → Tm Γ A → Conᴬ Γ → Tyᴬ A
  Tmᴬ (var vz)     Γᴬ = ₂ Γᴬ
  Tmᴬ (var (vs v)) Γᴬ = Tmᴬ (var v) (₁ Γᴬ)
  Tmᴬ (app  t u)   Γᴬ = Tmᴬ t Γᴬ (Tmᴬ u Γᴬ)
  Tmᴬ (appU t x)   Γᴬ = Tmᴬ t Γᴬ x
  Tmᴬ (app' t x)   Γᴬ = Tmᴬ t Γᴬ x

  EqTyᴬ : ∀ {Γ} → EqTy Γ → Conᴬ Γ → Set
  EqTyᴬ (eq t u) Γᴬ = Tmᴬ t Γᴬ ≡ Tmᴬ u Γᴬ
  EqTyᴬ (α ⇒' B) Γᴬ = ∀ x → EqTyᴬ (B x) Γᴬ
  EqTyᴬ (a ⇒  B) Γᴬ = ∀ x → EqTyᴬ B (Γᴬ , x)

  EqConᴬ : ∀ {Γ} → EqCon Γ → Conᴬ Γ → Set
  EqConᴬ ∙       Γᴬ = ⊤
  EqConᴬ (Δ ▶ A) Γᴬ = EqConᴬ Δ Γᴬ × EqTyᴬ A Γᴬ


-- Displayed Algebras
--------------------------------------------------------------------------------

module Displayed {sortᴬ : Set} {sortᴰ : sortᴬ → Set} where

  open Alg {sortᴬ}

  Uᴰ : ∀ (a : U) → Uᴬ a → Set
  Uᴰ sort    aᴬ = sortᴰ aᴬ
  Uᴰ (α ⇒ b) aᴬ = ∀ x → Uᴰ (b x) (aᴬ x)

  Tyᴰ : ∀ (A : Ty) → Tyᴬ A → Set
  Tyᴰ (El a  ) Aᴬ = Uᴰ a Aᴬ
  Tyᴰ (a ⇒  B) Aᴬ = ∀ aᴬ (aᴰ : Uᴰ a aᴬ) → Tyᴰ B (Aᴬ aᴬ)
  Tyᴰ (α ⇒' B) Aᴬ = ∀ x → Tyᴰ (B x) (Aᴬ x)

  Conᴰ : ∀ (Γ : Con) → Conᴬ Γ → Set
  Conᴰ ∙       Γᴬ        = ⊤
  Conᴰ (Γ ▶ A) (Γᴬ , Aᴬ) = Conᴰ Γ Γᴬ × Tyᴰ A Aᴬ

  Tmᴰ : ∀ {Γ A}(t : Tm Γ A){Γᴬ}(Γᴰ : Conᴰ Γ Γᴬ) → Tyᴰ A (Tmᴬ t Γᴬ)
  Tmᴰ (var vz)     Γᴰ = ₂ Γᴰ
  Tmᴰ (var (vs v)) Γᴰ = Tmᴰ (var v) (₁ Γᴰ)
  Tmᴰ (app t u)    Γᴰ = Tmᴰ t Γᴰ (Tmᴬ u _) (Tmᴰ u Γᴰ)
  Tmᴰ (appU t x)   Γᴰ = Tmᴰ t Γᴰ x
  Tmᴰ (app' t x)   Γᴰ = Tmᴰ t Γᴰ x

  EqTyᴰ : ∀ {Γ}(A : EqTy Γ){Γᴬ}(Γᴰ : Conᴰ Γ Γᴬ) → EqTyᴬ A Γᴬ → Set
  EqTyᴰ (eq t u) Γᴰ Aᴬ = transp (Uᴰ _) Aᴬ (Tmᴰ t Γᴰ) ≡ Tmᴰ u Γᴰ
  EqTyᴰ (α ⇒' A) Γᴰ Aᴬ = ∀ x → EqTyᴰ (A x) Γᴰ (Aᴬ x)
  EqTyᴰ (a ⇒  A) Γᴰ Aᴬ = ∀ x (xᴰ : Uᴰ a x) → EqTyᴰ A (Γᴰ , xᴰ) (Aᴬ x)

  EqConᴰ : ∀ {Γ}(Δ : EqCon Γ){Γᴬ}(Γᴰ : Conᴰ Γ Γᴬ) → EqConᴬ Δ Γᴬ → Set
  EqConᴰ ∙       Γᴰ Δᴬ        = ⊤
  EqConᴰ (Δ ▶ A) Γᴰ (Δᴬ , Aᴬ) = EqConᴰ Δ Γᴰ Δᴬ × EqTyᴰ A Γᴰ Aᴬ


-- Displayed algebra sections
--------------------------------------------------------------------------------

module Section {sortᴬ : Set}{sortᴰ : sortᴬ → Set}{sortˢ : ∀ x → sortᴰ x} where
  open Alg {sortᴬ}
  open Displayed {sortᴬ} {sortᴰ}

  Uˢ : ∀ (a : U) aᴬ → Uᴰ a aᴬ
  Uˢ sort    aᴬ = sortˢ aᴬ
  Uˢ (A ⇒ b) fᴬ = λ aᴬ → Uˢ (b aᴬ) (fᴬ aᴬ)

  Tyˢ : ∀ (A : Ty) aᴬ → Tyᴰ A aᴬ → Set
  Tyˢ (El a)   aᴬ aᴰ = Uˢ a aᴬ ≡ aᴰ
  Tyˢ (a ⇒  B) fᴬ fᴰ = ∀ aᴬ → Tyˢ B (fᴬ aᴬ) (fᴰ aᴬ (Uˢ a aᴬ))
  Tyˢ (α ⇒' B) aᴬ aᴰ = ∀ x → Tyˢ (B x) (aᴬ x) (aᴰ x)

  Conˢ : ∀ (Γ : Con) Γᴬ → Conᴰ Γ Γᴬ → Set
  Conˢ ∙       Γᴬ        Γᴰ        = ⊤
  Conˢ (Γ ▶ A) (Γᴬ , Aᴬ) (Γᴰ , Aᴰ) = Conˢ Γ Γᴬ Γᴰ × Tyˢ A Aᴬ Aᴰ

  Tmˢ : ∀ {Γ A}(t : Tm Γ A){Γᴬ Γᴰ}(Γˢ : Conˢ Γ Γᴬ Γᴰ) → Tyˢ A (Tmᴬ t Γᴬ) (Tmᴰ t Γᴰ)
  Tmˢ (var vz)     Γˢ = ₂ Γˢ
  Tmˢ (var (vs v)) Γˢ = Tmˢ (var v) (₁ Γˢ)
  Tmˢ (app t u)    Γˢ rewrite Tmˢ u Γˢ ⁻¹ = Tmˢ t Γˢ (Tmᴬ u _)
  Tmˢ (appU t x)   Γˢ = ap (λ f → f x) (Tmˢ t Γˢ)
  Tmˢ (app' t x)   Γˢ = Tmˢ t Γˢ x

  EqTyˢ : ∀ {Γ}(A : EqTy Γ){Γᴬ Γᴰ}(Γˢ : Conˢ Γ Γᴬ Γᴰ) → ∀ aᴬ → EqTyᴰ A Γᴰ aᴬ → Set
  EqTyˢ (eq {a} t u) Γˢ aᴬ aᴰ = (ap (transp (Uᴰ a) aᴬ) (Tmˢ t Γˢ ⁻¹) ◾ apd (Uˢ a) aᴬ ◾ Tmˢ u Γˢ) ≡ aᴰ
  EqTyˢ (α ⇒' B) Γˢ aᴬ aᴰ = ∀ x → EqTyˢ (B x) Γˢ (aᴬ x) (aᴰ x)
  EqTyˢ (a ⇒  B) Γˢ fᴬ fᴰ = ∀ aᴬ → EqTyˢ B (Γˢ , refl) (fᴬ aᴬ) (fᴰ aᴬ (Uˢ a aᴬ))

  EqConˢ : ∀ {Γ}(Δ : EqCon Γ){Γᴬ Γᴰ}(Γˢ : Conˢ Γ Γᴬ Γᴰ) Δᴬ → EqConᴰ Δ Γᴰ Δᴬ → Set
  EqConˢ ∙       Γˢ Δᴬ        Δᴰ        = ⊤
  EqConˢ (Δ ▶ A) Γˢ (Δᴬ , Aᴬ) (Δᴰ , Aᴰ) = EqConˢ Δ Γˢ Δᴬ Δᴰ × EqTyˢ A Γˢ Aᴬ Aᴰ


Alg : Decl → Set₁
Alg (Γ , Δ) = ∃₂ λ sᴬ Γᴬ → Alg.EqConᴬ {sᴬ} Δ Γᴬ

Displayed : (Γ : Decl) → Alg Γ → Set₁
Displayed (Γ , Δ) (sᴬ , Γᴬ , Δᴬ) = ∃₂ λ sᴰ Γᴰ → Displayed.EqConᴰ {sᴬ}{sᴰ} Δ Γᴰ Δᴬ

Section : (Γ : Decl) → (A : Alg Γ) → Displayed Γ A → Set
Section (Γ , Δ)(sᴬ , Γᴬ , Δᴬ)(sᴰ , Γᴰ , Δᴰ) = ∃₂ λ sˢ Γˢ → Section.EqConˢ {sᴬ}{sᴰ}{sˢ} Δ Γˢ Δᴬ Δᴰ

module _ (Γ : Decl) where
  postulate
    con : Alg Γ
    ind : (D : Displayed Γ con) → Section Γ con D


-- Examples
--------------------------------------------------------------------------------

NatExample : ⊤
NatExample =
  -- I use let block for destructuring assignment
  let
    Nat' : Decl
    Nat' =
        (∙ ▶ El sort ▶ sort ⇒ El sort)  -- zero : Nat, suc : Nat → Nat
      , ∙                               -- no path constructors

    -- Nat : Set; zero : Nat; suc : Nat → Nat
    Nat , ((_ , zero) , suc) , _ = con Nat'

    addMethods : Displayed Nat' (con Nat')
    addMethods = ((λ _ → Nat → Nat) , ((_ , λ b → b) , λ _ rec b → suc (rec b)) , tt)

    -- add : Nat → Nat → Nat
    add , ((_ , zeroβ) , sucβ) , _ = ind Nat' addMethods

    add0 : ∀ n → add n zero ≡ n
    add0 = ind Nat' (
        (λ n → add n zero ≡ n)
      , ((_ , ap (λ f → f zero) zeroβ)
      , (λ n e → ap (λ f → f zero) (sucβ n) ◾ ap suc e)) , _) .₁
  in _

S¹ : Decl
S¹ =
    (∙ ▶ El sort)                -- base : S¹
  , (∙ ▶ eq (var vz) (var vz))   -- loop : base = base

I : Decl
I =
    (∙ ▶ El sort ▶ El sort)          -- left : I, right : I
  , (∙ ▶ eq (var (vs vz)) (var vz))  -- seg : left = right

W : (S : Set)(P : S → Set) → Decl
W S P =
    (∙ ▶ S ⇒' λ s → (P s ⇒ λ _ → sort) ⇒ El sort) -- sup : (s : S) → (P s → W S P) → W S P
   , ∙

PropTrunc : (A : Set) → Decl
PropTrunc A =
    (∙ ▶ (A ⇒' λ _ → El sort))                    -- emb : A → PropTrunc A
  , (∙ ▶ sort ⇒ sort ⇒ eq (var (vs vz)) (var vz)) -- trunc : (x y : PropTrunc A) → x = y

Suspension : (A : Set) → Decl
Suspension A =
    (∙ ▶ El sort ▶ El sort )
  , (∙ ▶ A ⇒' λ _ → eq (var (vs vz)) (var vz))

Pushout : {A B C : Set} → (C → A) → (C → B) → Decl
Pushout {A}{B}{C} f g =
    (∙ ▶ (A ⇒' λ _ → El sort)       -- inl : A → Pushout f g
       ▶ (B ⇒' λ _ → El sort))      -- inr : B → Pushout f g
  , (∙ ▶ C ⇒' λ c → eq (app' (var (vs vz)) (f c))
                       (app' (var vz) (g c)))  -- glue : ∀ c → inl (f c) = inr (g c)
