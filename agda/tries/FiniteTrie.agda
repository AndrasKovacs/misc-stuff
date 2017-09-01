
open import Lib hiding (_×_; ⊤)
import Lib as L
open import Category.Monad
open import Data.Maybe
open module MaybeM {α} = RawMonad {α} Data.Maybe.monad public

mutual
  -- Types
  data * : Set where
    ⊤ : *
    μ : F → *

    -- Functors
  data F : Set where
    I       : F
    K       : * → F
    _+_ _×_ : F → F → F

infixr 5 _+_
infixr 6 _×_

mutual
  ⟦_⟧ : * → Set
  ⟦ ⊤   ⟧ = L.⊤
  ⟦ μ f ⟧ = ⟦μ⟧ f

  ⟦_⟧ᶠ : F → Set → Set
  ⟦ I     ⟧ᶠ A = A
  ⟦ K a   ⟧ᶠ _ = ⟦ a ⟧
  ⟦ f + g ⟧ᶠ A = ⟦ f ⟧ᶠ A ⊎ ⟦ g ⟧ᶠ A
  ⟦ f × g ⟧ᶠ A = ⟦ f ⟧ᶠ A L.× ⟦ g ⟧ᶠ A

  data ⟦μ⟧ (f : F) : Set where
    ⟨_⟩ : ⟦ f ⟧ᶠ (⟦μ⟧ f) → ⟦μ⟧ f

data AtLeastOne (A B : Set) : Set where
  left  : A → AtLeastOne A B
  right : B → AtLeastOne A B
  both  : A → B → AtLeastOne A B

mutual
  -- non-empty functor
  *ᵀ : * → Set → Set
  *ᵀ ⊤     A = A
  *ᵀ (μ f) A = μᵀ f A

  data μᵀ (f : F)(A : Set) : Set where
    ⟨_⟩ : Fᵀ f (μ f) A → μᵀ f A

  -- non-empty higher functor
  Fᵀ : F → * → Set → Set
  Fᵀ I       a A = *ᵀ a A
  Fᵀ (K a)   _ A = *ᵀ a A
  Fᵀ (f + g) a A = AtLeastOne (Fᵀ f a A) (Fᵀ g a A)
  Fᵀ (f × g) a A = Fᵀ f a (Fᵀ g a A)

outᵀ : ∀ {f A} → μᵀ f A → Fᵀ f (μ f) A
outᵀ ⟨ t ⟩ = t

module TrieOps where
  mutual
    lookup : ∀ a {B} → *ᵀ a B → ⟦ a ⟧ → Maybe B
    lookup ⊤     t     i     = just t
    lookup (μ f) ⟨ t ⟩ ⟨ i ⟩ = lookupF f f t i

    lookupF : ∀ f g {B} → Fᵀ f (μ g) B → ⟦ f ⟧ᶠ (⟦μ⟧ g) → Maybe B
    lookupF I       h ⟨ t ⟩      ⟨ i ⟩     = lookupF h h t i
    lookupF (K a)   h t          i         = lookup a t i
    lookupF (f + g) h (left l)   (inl i)   = lookupF f h l i
    lookupF (f + g) h (left l)   (inr i)   = nothing
    lookupF (f + g) h (right r)  (inl i)   = nothing
    lookupF (f + g) h (right r)  (inr i)   = lookupF g h r i
    lookupF (f + g) h (both l r) (inl i)   = lookupF f h l i
    lookupF (f + g) h (both l r) (inr i)   = lookupF g h r i
    lookupF (f × g) h t          (il , ir) = lookupF f h t il >>= (λ t' → lookupF g h t' ir)

  mutual
    modify : ∀ a {B} → Maybe (*ᵀ a B) → ⟦ a ⟧ → (Maybe B → Maybe B) → Maybe (*ᵀ a B)
    modify ⊤     t i     m = m t
    modify (μ f) t ⟨ i ⟩ m = ⟨_⟩ <$> modifyF f f (outᵀ <$> t) i m

    modifyF : ∀ f g {B} → Maybe (Fᵀ f (μ g) B) → ⟦ f ⟧ᶠ (⟦μ⟧ g) → (Maybe B → Maybe B) → Maybe (Fᵀ f (μ g) B)
    modifyF I       h t                 ⟨ i ⟩     m = ⟨_⟩ <$> modifyF h h (outᵀ <$> t) i m
    modifyF (K a)   h t                 i         m = modify a t i m
    modifyF (f + g) h (just (left l))   (inl i)   m = left <$> modifyF f h (just l) i m
    modifyF (f + g) h (just (left l))   (inr i)   m = both l <$> modifyF g h nothing i m
    modifyF (f + g) h (just (right r))  (inl i)   m = both <$> modifyF f h nothing i m ⊛ just r
    modifyF (f + g) h (just (right r))  (inr i)   m = right <$> modifyF g h (just r) i m
    modifyF (f + g) h (just (both l r)) (inl i)   m = both <$> modifyF f h (just l) i m ⊛ just r
    modifyF (f + g) h (just (both l r)) (inr i)   m = both l <$> modifyF g h (just r) i m
    modifyF (f + g) h nothing           (inl i)   m = left <$> modifyF f h nothing i m
    modifyF (f + g) h nothing           (inr i)   m = right <$> modifyF g h nothing i m
    modifyF (f × g) h t                 (il , ir) m = modifyF f h t il (λ t → modifyF g h t ir m)

--------------------------------------------------------------------------------

Trie : * → Set → Set
Trie a B = Maybe (*ᵀ a B)

pattern empty = nothing

lookup : ∀ {a B} → ⟦ a ⟧ → Trie a B → Maybe B
lookup i t = t >>= λ t → TrieOps.lookup _ t i

insert : ∀ {a B} → ⟦ a ⟧ → B → Trie a B → Trie a B
insert i b t = TrieOps.modify _ t i (λ _ → just b)

singleton : ∀ {a B} → ⟦ a ⟧ → B → Trie a B
singleton i b = insert i b empty

delete : ∀ {a B} → ⟦ a ⟧ → Trie a B → Trie a B
delete i t = TrieOps.modify _ t i (λ _ → nothing)

--------------------------------------------------------------------------------

Bool : *
Bool = μ (K ⊤ + K ⊤)

true : ⟦ Bool ⟧
true = ⟨ inl tt ⟩

false : ⟦ Bool ⟧
false = ⟨ inr tt ⟩

List : * → *
List A = μ (K ⊤ + K A × I)

nil : ∀ {a} → ⟦ List a ⟧
nil = ⟨ inl tt ⟩

_∷_ : ∀ {a} → ⟦ a ⟧ → ⟦ List a ⟧ → ⟦ List a ⟧
a ∷ as = ⟨ inr (a , as) ⟩
infixr 5 _∷_

Nat : *
Nat = μ (K ⊤ + I)

zero : ⟦ Nat ⟧
zero = ⟨ inl tt ⟩

suc : ⟦ Nat ⟧ → ⟦ Nat ⟧
suc n = ⟨ inr n ⟩

k1 : ⟦ List Bool ⟧
k1 = true ∷ nil

t1 = insert (true ∷ true ∷ nil) (suc zero) (insert nil zero (singleton k1 (suc (suc zero))))
l1 = lookup k1 t1

