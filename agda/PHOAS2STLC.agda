
{- Convert PHOAS to STLC terms via parametricity #-}

open import Algebra
open import Data.Bool
open import Data.Empty
open import Data.List
open import Data.List.Properties
open import Data.Product
open import Function
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Relation.Nullary.Decidable

module LM {A : Set} = Monoid (++-monoid A)

infixr 4 _⇒_
data Type : Set where
  o   : Type
  _⇒_ : Type → Type → Type

Env = List Type

-- we use decidable equality to convert postulated equations
-- (originating from parametricity) to canonical equations,
-- so we don't block computation
Type≡? : (A B : Type) → Dec (A ≡ B)
Type≡? o o = yes refl
Type≡? o (_ ⇒ _) = no λ ()
Type≡? (_ ⇒ _) o = no λ ()
Type≡? (A ⇒ B) (A' ⇒ B') with Type≡? A A'
... | no  p    = no λ {refl → p refl}
... | yes refl with Type≡? B B'
... | no  p    = no λ {refl → p refl}
... | yes refl = yes refl

Env≡? : (Γ Δ : Env) → Dec (Γ ≡ Δ)
Env≡? [] [] = yes refl
Env≡? [] (_ ∷ _) = no (λ ())
Env≡? (_ ∷ _) [] = no (λ ())
Env≡? (A ∷ Γ) (A' ∷ Γ') with Type≡? A A'
... | no p     = no λ {refl → p refl}
... | yes refl with Env≡? Γ Γ'
... | no p     = no λ {refl → p refl}
... | yes refl = yes refl

data Var : Env → Type → Set where
  Z : ∀ {Γ A} → Var (A ∷ Γ) A
  S : ∀ {Γ A B} → Var Γ B → Var (A ∷ Γ) B

data Exp : Env → Type → Set where
  var : ∀ {Γ A} → Var Γ A → Exp Γ A
  lam : ∀ {Γ A B} → Exp (A ∷ Γ) B → Exp Γ (A ⇒ B)
  app : ∀ {Γ A B} → Exp Γ (A ⇒ B) → Exp Γ A → Exp Γ B

data PH (X : Type → Set) : Type → Set where
  var : ∀ {A} → X A → PH X A
  lam : ∀ {A B} → (X A → PH X B) → PH X (A ⇒ B)
  app : ∀ {A B} → PH X (A ⇒ B) → PH X A → PH X B

-- logical predicate on PH
PHᴾ : ∀ {X}(Xᴾ : ∀ {A} → X A → Set) → ∀ {A} → PH X A → Set
PHᴾ Xᴾ (var a)   = Xᴾ a
PHᴾ Xᴾ (lam t)   = ∀ a → Xᴾ a → PHᴾ Xᴾ (t a)
PHᴾ Xᴾ (app t u) = PHᴾ Xᴾ t × PHᴾ Xᴾ u

postulate
  free-thm :
    ∀ {A}(t : ∀ {X} → PH X A) → ∀ X (Xᴾ : ∀ {A} → X A → Set) → PHᴾ {X} Xᴾ t

PH' : Type → Set
PH' = PH (λ _ → Env)

VarOK? : ∀ Γ A Δ → Dec (∃ λ Ξ → (Ξ ++ A ∷ Δ) ≡ Γ)
VarOK? []       A Δ = no (λ {([] , ()) ; (_ ∷ _ , ())})
VarOK? (A' ∷ Γ) A Δ with Env≡? (A' ∷ Γ) (A ∷ Δ)
VarOK? (A' ∷ Γ) .A' .Γ | yes refl = yes ([] , refl)
VarOK? (A' ∷ Γ) A Δ | no ¬p with VarOK? Γ A Δ
VarOK? (A' ∷ Γ) A Δ | no ¬p | yes (Σ , refl) =
  yes (A' ∷ Σ , refl)
VarOK? (A' ∷ Γ) A Δ | no ¬p | no ¬q
  = no λ { ([] , refl) → ¬p refl ; (x ∷ Σ , s) → ¬q (Σ , proj₂ (∷-injective s))}

OK : ∀ {A} → Env → PH' A → Set
OK {A} Γ t = ∀ Δ → PHᴾ (λ {B} Σ → True (VarOK? (Δ ++ Γ) B Σ)) t

toVar : ∀ {Γ Σ A} → (∃ λ Ξ → (Ξ ++ A ∷ Σ) ≡ Γ) → Var Γ A
toVar ([]    , refl) = Z
toVar (x ∷ Ξ , refl) = S (toVar (Ξ , refl))

toExp' : ∀ {Γ A} (t : PH' A) → OK {A} Γ t → Exp Γ A
toExp' (var x) p = var (toVar (toWitness (p [])))
toExp' {Γ} (lam {A} {B} t) p =
  lam (toExp' (t Γ)
      λ Δ → subst (λ z → PHᴾ (λ {B₁} Σ₁ → True (VarOK? z B₁ Σ₁)) (t Γ))
                   (LM.assoc Δ (A ∷ []) Γ)
                   (p (Δ ++ A ∷ []) Γ (fromWitness (Δ , sym (LM.assoc Δ (A ∷ []) Γ)))))
toExp' (app t u) p =
  app (toExp' t (proj₁ ∘ p)) (toExp' u (proj₂ ∘ p))

toExp : ∀ {A} → (∀ {X} → PH X A) → Exp [] A
toExp {A} t = toExp' t λ Δ → free-thm t _ _

-- examples
------------------------------------------------------------

t0 : ∀ {X} → PH X ((o ⇒ o) ⇒ o ⇒ o)
t0 = lam var

t1 : ∀ {X} → PH X ((o ⇒ o) ⇒ o ⇒ o)
t1 = lam λ f → lam λ x → app (var f) (app (var f) (var x))

test1 : toExp t0 ≡ lam (var Z)
test1 = refl

test2 : toExp t1 ≡ lam (lam (app (var (S Z)) (app (var (S Z)) (var Z))))
test2 = refl
