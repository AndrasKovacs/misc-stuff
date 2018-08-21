{-# OPTIONS --without-K #-}

{- Syntax for 1-HITs with functors and natural transformations (an F-algebra-like style).
   Based on Agda file by Corlin Fardar:
   https://groups.google.com/forum/#!topic/homotopytypetheory/9PGc3RvNJeA -}

open import Relation.Binary.PropositionalEquality renaming (subst to transp; cong to ap)
open import Data.Product renaming (proj₁ to ₁; proj₂ to ₂)
open import Data.Sum
open import Data.Unit
open import Data.Empty

infixr 4 _◾_; _◾_ = trans
infix  6 _⁻¹; _⁻¹ = sym

apd : ∀{i j}{A : Set i}{B : A → Set j}(f : (x : A) → B x){a₀ a₁ : A}(a₂ : a₀ ≡ a₁)
    → transp B a₂ (f a₀) ≡ f a₁
apd f refl = refl

-- Syntax
--------------------------------------------------------------------------------

data F : Set₁ where
  Id    : F
  Const : Set → F
  Sum   : F → F → F
  Prod  : F → F → F
  Exp   : Set → F → F
  Empty : F

data Tm (f g : F) : F → Set₁ where
  id      : Tm f g g
  const   : ∀ {A} → A → Tm f g (Const A)
  con     : Tm f g f → Tm f g Id
  pair    : ∀ {h i} → Tm f g h → Tm f g i → Tm f g (Prod h i)
  π₁      : ∀ {h i} → Tm f g (Prod h i) → Tm f g h
  π₂      : ∀ {h i} → Tm f g (Prod h i) → Tm f g i
  lam     : ∀ {h A} → (A → Tm f g h) → Tm f g (Exp A h) -- need this lam for pushout
                                                        -- (and for embedding external functions into Tm in general)
  app     : ∀ {h A} → Tm f g (Exp A h) → Tm f g (Const A) → Tm f g h
  inj₁    : ∀ {h i} → Tm f g h → Tm f g (Sum h i)
  inj₂    : ∀ {h i} → Tm f g i → Tm f g (Sum h i)
  case    : ∀ {h i j} → Tm f g (Sum h i) → Tm f (Prod g h) j → Tm f (Prod g i) j → Tm f g j
  exfalso : ∀ {h} → Tm f g Empty → Tm f g h

-- 1HIT declarations
Decl : Set₁
Decl = ∃₂ λ f g → Tm f g Id × Tm f g Id

-- Algebras
--------------------------------------------------------------------------------

Fᴬ : F → Set → Set
Fᴬ Id         X = X
Fᴬ (Const A)  X = A
Fᴬ (Sum f g)  X = Fᴬ f X ⊎ Fᴬ g X
Fᴬ (Prod f g) X = Fᴬ f X × Fᴬ g X
Fᴬ (Exp A f)  X = A → Fᴬ f X
Fᴬ Empty      X = ⊥

Tmᴬ : ∀ {f g h} → Tm f g h → ∀ {X}(c : Fᴬ f X → X) → Fᴬ g X → Fᴬ h X
Tmᴬ id           c gx = gx
Tmᴬ (const x)    c gx = x
Tmᴬ (con t)      c gx = c (Tmᴬ t c gx)
Tmᴬ (pair t u)   c gx = (Tmᴬ t c gx) , (Tmᴬ u c gx)
Tmᴬ (π₁ t)       c gx = ₁ (Tmᴬ t c gx)
Tmᴬ (π₂ t)       c gx = ₂ (Tmᴬ t c gx)
Tmᴬ (lam t)      c gx = λ x → Tmᴬ (t x) c gx
Tmᴬ (app t u)    c gx = Tmᴬ t c gx (Tmᴬ u c gx)
Tmᴬ (inj₁ t)     c gx = inj₁ (Tmᴬ t c gx)
Tmᴬ (inj₂ u)     c gx = inj₂ (Tmᴬ u c gx)
Tmᴬ (case t u v) c gx with Tmᴬ t c gx
... | inj₁ x = Tmᴬ u c (gx , x)
... | inj₂ x = Tmᴬ v c (gx , x)
Tmᴬ (exfalso t)  c gx = ⊥-elim (Tmᴬ t c gx)

Alg : Decl → Set₁
Alg (f , g , t , u) =
  ∃₂ λ (X      : Set)
       (points : Fᴬ f X → X)
     → (∀ gx → Tmᴬ t points gx ≡ Tmᴬ u points gx)


-- Displayed algebras
--------------------------------------------------------------------------------

Fᴰ : ∀ f → {X : Set}(Xᴰ : X → Set) → Fᴬ f X → Set
Fᴰ Id         Xᴰ fx        = Xᴰ fx
Fᴰ (Const A)  Xᴰ fx        = ⊤
Fᴰ (Sum f g)  Xᴰ (inj₁ fx) = Fᴰ f Xᴰ fx
Fᴰ (Sum f g)  Xᴰ (inj₂ gx) = Fᴰ g Xᴰ gx
Fᴰ (Prod f g) Xᴰ fx        = Fᴰ f Xᴰ (₁ fx) × Fᴰ g Xᴰ (₂ fx)
Fᴰ (Exp A f)  Xᴰ fx        = ∀ x → Fᴰ f Xᴰ (fx x)
Fᴰ Empty      Xᴰ fx        = ⊥-elim fx

Tmᴰ : ∀ {f g h}(t : Tm f g h)
        {X}(Xᴰ : X → Set)
        {c : Fᴬ f X → X}(cᴰ : ∀ {fx} → Fᴰ f Xᴰ fx → Xᴰ (c fx))
        {gx : Fᴬ g X}(gxᴰ : Fᴰ g Xᴰ gx)
      → Fᴰ h Xᴰ (Tmᴬ t c gx)
Tmᴰ id           Xᴰ cᴰ gxᴰ = gxᴰ
Tmᴰ (const x)    Xᴰ cᴰ gxᴰ = tt
Tmᴰ (con t)      Xᴰ cᴰ gxᴰ = cᴰ (Tmᴰ t Xᴰ cᴰ gxᴰ)
Tmᴰ (pair t u)   Xᴰ cᴰ gxᴰ = Tmᴰ t Xᴰ cᴰ gxᴰ , Tmᴰ u Xᴰ cᴰ gxᴰ
Tmᴰ (π₁ t)       Xᴰ cᴰ gxᴰ = ₁ (Tmᴰ t Xᴰ cᴰ gxᴰ)
Tmᴰ (π₂ t)       Xᴰ cᴰ gxᴰ = ₂ (Tmᴰ t Xᴰ cᴰ gxᴰ)
Tmᴰ (lam t)      Xᴰ cᴰ gxᴰ = λ x → Tmᴰ (t x) Xᴰ cᴰ gxᴰ
Tmᴰ (app t u)    Xᴰ cᴰ gxᴰ = Tmᴰ t Xᴰ cᴰ gxᴰ (Tmᴬ u _ _)
Tmᴰ (inj₁ t)     Xᴰ cᴰ gxᴰ = Tmᴰ t Xᴰ cᴰ gxᴰ
Tmᴰ (inj₂ t)     Xᴰ cᴰ gxᴰ = Tmᴰ t Xᴰ cᴰ gxᴰ
Tmᴰ (case t u v) Xᴰ {c} cᴰ {gx} gxᴰ with Tmᴬ t c gx | Tmᴰ t Xᴰ cᴰ gxᴰ
... | inj₁ x | xᴰ = Tmᴰ u Xᴰ cᴰ (gxᴰ , xᴰ)
... | inj₂ x | xᴰ = Tmᴰ v Xᴰ cᴰ (gxᴰ , xᴰ)
Tmᴰ (exfalso t) Xᴰ {c} cᴰ {gx} gxᴰ = ⊥-elim (Tmᴬ t c gx)

Displayed : (Γ : Decl) → Alg Γ → Set₁
Displayed (f , g , t , u) (X , points , paths) =
  ∃₂ λ (Xᴰ      : X → Set)
       (pointsᴰ : ∀ {fx} → Fᴰ f Xᴰ fx → Xᴰ (points fx))
     → ((gx : Fᴬ g X)(gxᴰ : Fᴰ g Xᴰ gx) → transp Xᴰ (paths gx) (Tmᴰ t Xᴰ pointsᴰ gxᴰ) ≡ Tmᴰ u Xᴰ pointsᴰ gxᴰ)

-- Displayed algebra sections
--------------------------------------------------------------------------------

Fˢ : ∀ (f : F){X Xᴰ}(Xˢ : ∀ x → Xᴰ x)(fx : Fᴬ f X) → Fᴰ f Xᴰ fx
Fˢ Id         Xˢ fx       = Xˢ fx
Fˢ (Const A)  Xˢ fx       = tt
Fˢ (Sum f g)  Xˢ (inj₁ x) = Fˢ f Xˢ x
Fˢ (Sum f g)  Xˢ (inj₂ x) = Fˢ g Xˢ x
Fˢ (Prod f g) Xˢ fx       = Fˢ f Xˢ (₁ fx) , Fˢ g Xˢ (₂ fx)
Fˢ (Exp A f)  Xˢ fx       = λ x → Fˢ f Xˢ (fx x)
Fˢ Empty      Xˢ fx       = ⊥-elim fx

postulate funext : ∀ {i j} → Extensionality i j

Tmˢ : ∀ {f g h}(t : Tm f g h)
        {X : Set}       {Xᴰ : X → Set}                        (Xˢ : ∀ x → Xᴰ x)
        {c : Fᴬ f X → X}{cᴰ : ∀ {fx} → Fᴰ f Xᴰ fx → Xᴰ (c fx)}(cˢ : ∀ fx → Xˢ (c fx) ≡ cᴰ (Fˢ f Xˢ fx))
      → ∀ gx → Fˢ h Xˢ (Tmᴬ t c gx) ≡ Tmᴰ t Xᴰ cᴰ (Fˢ g Xˢ gx)
Tmˢ id           Xˢ cˢ gx = refl
Tmˢ (const x)    Xˢ cˢ gx = refl
Tmˢ (con t) Xˢ {c} {cᴰ} cˢ gx = cˢ (Tmᴬ t c gx) ◾ ap cᴰ (Tmˢ t Xˢ cˢ gx)
Tmˢ (pair t u) Xˢ cˢ gx rewrite Tmˢ t Xˢ cˢ gx | Tmˢ u Xˢ cˢ gx = refl
Tmˢ (π₁ t)       Xˢ cˢ gx = ap ₁ (Tmˢ t Xˢ cˢ gx)
Tmˢ (π₂ t)       Xˢ cˢ gx = ap ₂ (Tmˢ t Xˢ cˢ gx)
Tmˢ (lam t)      Xˢ cˢ gx = funext λ x → Tmˢ (t x) Xˢ cˢ gx
Tmˢ (app t u)    Xˢ cˢ gx = ap (λ f → f (Tmᴬ u _ _)) (Tmˢ t Xˢ cˢ gx)
Tmˢ (inj₁ t)     Xˢ cˢ gx = Tmˢ t Xˢ cˢ gx
Tmˢ (inj₂ t)     Xˢ cˢ gx = Tmˢ t Xˢ cˢ gx
Tmˢ (case t u v) Xˢ {c} {cᴰ} cˢ gx rewrite Tmˢ t Xˢ {_}{cᴰ} cˢ gx ⁻¹ with Tmᴬ t c gx
... | inj₁ x = Tmˢ u Xˢ cˢ (gx , x)
... | inj₂ x = Tmˢ v Xˢ cˢ (gx , x)
Tmˢ (exfalso t) Xˢ {c} cˢ gx = ⊥-elim (Tmᴬ t c gx)

Section : (Γ : Decl)(A : Alg Γ) → Displayed Γ A → Set
Section (f , g , t , u)(X , points , paths)(Xᴰ , pointsᴰ , pathsᴰ) =
  ∃₂ λ (Xˢ      : ∀ x → Xᴰ x)
       (pointsˢ : ∀ fx → Xˢ (points fx) ≡ pointsᴰ (Fˢ f Xˢ fx))
     → ((gx : Fᴬ g X) →  (ap (transp Xᴰ (paths gx)) (Tmˢ t Xˢ pointsˢ gx ⁻¹)
                        ◾ apd (Fˢ Id Xˢ) (paths gx)
                        ◾ Tmˢ u Xˢ pointsˢ gx)
                      ≡ pathsᴰ gx (Fˢ g Xˢ gx))

--------------------------------------------------------------------------------

module _ (Γ : Decl) where
  postulate
    Con : Alg Γ                  -- type, point, path constructors
    Ind : (D : Displayed Γ Con)  -- induction motive & induction methods
          → Section Γ Con D      -- eliminator & propositional β-rules

-- (you can always turn propositional β into definitional by REWRITE, but not the other way)


-- Decl examples
--------------------------------------------------------------------------------

One : F
One = Const ⊤

Nat : Decl
Nat = Sum One Id , Empty , exfalso id , exfalso id

List : Set → Decl
List A = Sum One (Prod (Const A) Id) , Empty , exfalso id , exfalso id

S¹ : Decl
S¹ = One , One , con id , con id

Interval : Decl
Interval = Sum One One , One , con (inj₁ id) , con (inj₂ id)

PropTrunc : Set → Decl
PropTrunc A = Const A , Prod Id Id , π₁ id , π₂ id

Pushout : {A B C : Set} → (C → A) → (C → B) → Decl
Pushout {A}{B}{C} f g =
    Sum (Const A) (Const B)
  , Const C
  , con (inj₁ (app (lam λ c → const (f c)) id))
  , con (inj₂ (app (lam λ c → const (g c)) id))
