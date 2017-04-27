
open import Algebra
open import Data.Bool
open import Data.Empty
open import Data.List
open import Data.Nat hiding (erase)
open import Data.Product
open import Data.Unit
open import Function
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.PropositionalEquality.TrustMe

module LM {A : Set} = Monoid (Data.List.monoid A)

-- A universe for types which can be put into STRef.
--------------------------------------------------------------------------------

data U : Set where
  ℕ' Bool' : U
  _⇒_ : U → U → U

infixr 4 _⇒_

⟦_⟧ : U → Set
⟦ ℕ'    ⟧ = ℕ
⟦ Bool' ⟧ = Bool
⟦ A ⇒ B ⟧ = ⟦ A ⟧ → ⟦ B ⟧

--------------------------------------------------------------------------------

data Heap : List U → Set where
  []  : Heap []
  _∷_ : ∀ {A As} → ⟦ A ⟧ → Heap As → Heap (A ∷ As)

_[_]≡_ : {A : Set} → List A → ℕ → A → Set
[]       [ _     ]≡ b = ⊥
(a ∷ as) [ zero  ]≡ b = a ≡ b
(a ∷ as) [ suc n ]≡ b = as [ n ]≡ b

readHp : ∀ {A As n} → Heap As → As [ n ]≡ A → ⟦ A ⟧
readHp {As = []}     {n}     hp      ()
readHp {As = A ∷ As} {zero} (a ∷ hp) p = subst ⟦_⟧ (erase p) a
readHp {As = A ∷ As} {suc n}(_ ∷ hp) p = readHp hp p

writeHp : ∀ {A As n} → Heap As → As [ n ]≡ A → ⟦ A ⟧ → Heap As
writeHp {As = []} {n}         hp       () a
writeHp {As = A ∷ As} {zero}  (_  ∷ hp) p a = subst ⟦_⟧ (sym (erase p)) a ∷ hp
writeHp {As = A ∷ As} {suc n} (a' ∷ hp) p a = a' ∷ writeHp hp p a

pushHp : ∀ {As} → Heap As → ∀ {A} → ⟦ A ⟧ → Heap (As ++ A ∷ [])
pushHp []        a = a  ∷ []
pushHp (a' ∷ hp) a = a' ∷ pushHp hp a

[length] : ∀ {A}(as bs : List A) b → (as ++ b ∷ bs) [ length as ]≡ b
[length] []       bs b = refl
[length] (a ∷ as) bs b = [length] as bs b

--------------------------------------------------------------------------------

data ST (S : U → Set)(A : Set) : Set where
  ret   : A → ST S A
  new   : ∀ B → ⟦ B ⟧ → (S B → ST S A) → ST S A
  read  : ∀ B → S B → (⟦ B ⟧ → ST S A) → ST S A
  write : ∀ B → S B → ⟦ B ⟧ → ST S A → ST S A

-- Logical predicate for ST. We omit ᴾ witnesses for elements of U
-- and elements of ⟦ A ⟧, since these are all in ⊤.
STᴾ : ∀{S}(Sᴾ : ∀ {A} → S A → Set){A}(Aᴾ : A → Set) → ST S A → Set
STᴾ Sᴾ Aᴾ (ret _)          = ⊤
STᴾ Sᴾ Aᴾ (new _ _ k)      = ∀ sb → Sᴾ sb → STᴾ Sᴾ Aᴾ (k sb)
STᴾ Sᴾ Aᴾ (read _ sb k)    = Sᴾ sb × (∀ b → STᴾ Sᴾ Aᴾ (k b))
STᴾ Sᴾ Aᴾ (write _ sb _ k) = Sᴾ sb × STᴾ Sᴾ Aᴾ k

--------------------------------------------------------------------------------

ST' : Set → Set
ST' = ST (λ _ → ℕ)

Safe : List U → ∀ {A} → ST' A → Set
Safe As (ret _)         = ⊤
Safe As (new B _ k)     = Safe (As ++ B ∷ []) (k (length As))
Safe As (read B n k)    = As [ n ]≡ B × (∀ b → Safe As (k b))
Safe As (write B n _ k) = As [ n ]≡ B × Safe As k

runST' : ∀ {A As}(m : ST' A) → Safe As m → Heap As → A
runST' (ret a)         p       hp = a
runST' (new _ b k)     p       hp = runST' (k _) p (pushHp hp b)
runST' (read _ n k)    (p , q) hp = runST' (k _) (q (readHp hp p)) hp
runST' (write _ n b k) (p , q) hp = runST' k q (writeHp hp p b)

--------------------------------------------------------------------------------

Safe' : List U → ∀ {A} → ST' A → Set
Safe' As = STᴾ (λ {A} n → As [ n ]≡ A) (λ _ → ⊤)

Safe'+ : List U → ∀ {A} → ST' A → Set
Safe'+ As m = ∀ Bs → Safe' (As ++ Bs) m

Safe'+[] : ∀ {As A m} → Safe'+ As {A} m → Safe' As m
Safe'+[] {As}{A}{m} safe' = subst (λ x → Safe' x {A} m)(proj₂ LM.identity As) (safe' [])

Safe'+⇒Safe : ∀ {As A}(m : ST' A) → Safe'+ As m → Safe As m
Safe'+⇒Safe {As}(ret _) safe'+ = tt

Safe'+⇒Safe {As}(new B b k) safe'+ =
  Safe'+⇒Safe
     (k (length As))
     (λ Bs → subst
       (λ x → Safe' x (k (length As)))
       ((sym (LM.assoc As (B ∷ []) Bs)))
       (safe'+ (B ∷ Bs) _ ([length] As Bs B)))

Safe'+⇒Safe {As}(read B n k) safe'+ =
  proj₁ (Safe'+[] {As}{m = read B n k} safe'+) ,
  (λ b → Safe'+⇒Safe (k b) (λ Bs → proj₂ (safe'+ Bs) b))

Safe'+⇒Safe {As}(write B n b k) safe'+ =
  proj₁ (Safe'+[] {As}{m = write B n b k} safe'+) ,
  Safe'+⇒Safe k (λ Bs → proj₂ (safe'+ Bs))

--------------------------------------------------------------------------------

postulate
  free-theorem : ∀ {A}(m : ∀ S → ST S A) → ∀ Aᴾ S (Sᴾ : ∀ {A} → S A → Set) → STᴾ Sᴾ Aᴾ (m S)

run : ∀ {A} → (∀ S → ST S A) → ST' A
run m = m (λ _ → ℕ)

alwaysSafe : ∀ {A As}(m : ∀ S → ST S A) → Safe As (run m)
alwaysSafe m = Safe'+⇒Safe (run m) (λ Bs → free-theorem m (λ _ → ⊤) _ _)

runST : ∀ {A} → (∀ S → ST S A) → A
runST m = runST' (run m) (alwaysSafe m) []

--------------------------------------------------------------------------------

ex1 : ∀ S → ST S ℕ
ex1 S =
  new ℕ' 0 λ x →
  read _ x λ b →
  write _ x (b + 10) $
  read _ x λ b →
  ret b

computes : runST ex1 ≡ 10
computes = refl

