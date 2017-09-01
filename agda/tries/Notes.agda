
open import Lib hiding (_×_; ⊤)
open import Data.List hiding (unfold)
open import Data.Bool
open import Category.Monad
import Lib as L

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

open import Data.Maybe
module _ {α} where open RawMonad {α} Data.Maybe.monad public

data AtLeastOne (A B : Set) : Set where
  left  : A → AtLeastOne A B
  right : B → AtLeastOne A B
  both  : A → B → AtLeastOne A B  

mutual
  *ᵀ : * → Set → Bool → Set
  *ᵀ a     A true  = L.⊤  
  *ᵀ ⊤     A false = A
  *ᵀ (μ f) A false = μᵀ f A

  data μᵀ (f : F)(A : Set) : Set where
    ⟨_⟩ : Fᵀ f (μ f) A → μᵀ f A

  Fᵀ : F → * → Set → Set
  Fᵀ I       a A = *ᵀ a A false
  Fᵀ (K a)   _ A = *ᵀ a A false
  Fᵀ (f + g) a A = AtLeastOne (Fᵀ f a A) (Fᵀ g a A)
  Fᵀ (f × g) a A = Fᵀ f a (Fᵀ g a A)

mutual
  lookup : ∀ a b {B} → *ᵀ a B b → ⟦ a ⟧ → Maybe B
  lookup a     true  t     i     = nothing
  lookup ⊤     false t     i     = just t
  lookup (μ f) false ⟨ t ⟩ ⟨ i ⟩ = lookupF f f t i 

  lookupF : ∀ f g {B} → Fᵀ f (μ g) B → ⟦ f ⟧ᶠ (⟦μ⟧ g) → Maybe B
  lookupF I       h ⟨ t ⟩      ⟨ i ⟩     = lookupF h h t i
  lookupF (K a)   h t          i         = lookup a false t i
  lookupF (f + g) h (left l)   (inl i)   = lookupF f h l i
  lookupF (f + g) h (left l)   (inr i)   = nothing
  lookupF (f + g) h (right r)  (inl i)   = nothing
  lookupF (f + g) h (right r)  (inr i)   = lookupF g h r i
  lookupF (f + g) h (both l r) (inl i)   = lookupF f h l i
  lookupF (f + g) h (both l r) (inr i)   = lookupF g h r i
  lookupF (f × g) h t          (il , ir) = lookupF f h t il >>= (λ t' → lookupF g h t' ir)

mutual
  single : ∀ a {B} → ⟦ a ⟧ → B → *ᵀ a B false
  single ⊤     i     v = v
  single (μ f) ⟨ i ⟩ v = ⟨ singleF f f i v ⟩

  singleF : ∀ f g {B} → ⟦ f ⟧ᶠ (⟦μ⟧ g) → B → Fᵀ f (μ g) B
  singleF I       h ⟨ i ⟩     v = ⟨ singleF h h i v ⟩ 
  singleF (K a)   h i         v = single a i v
  singleF (f + g) h (inl i)   v = left (singleF f h i v)
  singleF (f + g) h (inr i)   v = right (singleF g h i v)
  singleF (f × g) h (il , ir) v = singleF f h il (singleF g h ir v)

mutual
  insert' : ∀ a b {B} → *ᵀ a B b → ⟦ a ⟧ → B → (B → B) → *ᵀ a B false
  insert' a     true  t     i     v m = single a i v  
  insert' ⊤     false t     i     v m = m t
  insert' (μ f) false ⟨ t ⟩ ⟨ i ⟩ v m = ⟨ insertF' f f t i v m ⟩

  insertF' : ∀ f g {B} → Fᵀ f (μ g) B → ⟦ f ⟧ᶠ (⟦μ⟧ g) → B → (B → B) → Fᵀ f (μ g) B
  insertF' I       h ⟨ t ⟩       ⟨ i ⟩     v m = ⟨ insertF' h h t i v m ⟩
  insertF' (K a)   h t           i         v m = insert' a false t i v m
  insertF' (f + g) h (left l)    (inl i)   v m = left (insertF' f h l i v m)
  insertF' (f + g) h (left l)    (inr i)   v m = both l (singleF g h i v)
  insertF' (f + g) h (right r)   (inl i)   v m = both (singleF f h i v) r
  insertF' (f + g) h (right r)   (inr i)   v m = right (insertF' g h r i v m)
  insertF' (f + g) h (both l r)  (inl i)   v m = both (insertF' f h l i v m) r
  insertF' (f + g) h (both l r)  (inr i)   v m = both l (insertF' g h r i v m)
  insertF' (f × g) h t           (il , ir) v m = insertF' f h t il (singleF g h ir v) (λ t → insertF' g h t ir v m)

insert : ∀ a b {B} → *ᵀ a B b → ⟦ a ⟧ → B → *ᵀ a B false
insert a b t i v = insert' a b t i v (λ _ → v)

mutual
  delete' : ∀ a b {B} → *ᵀ a B b → ⟦ a ⟧ → ∃ (*ᵀ a B)
  delete' a     true  t i = true , tt  
  delete' ⊤     false t i = true , tt
  delete' (μ f) false t i = {!!}
  -- insert' a     true  t     i     v m = single a i v  
  -- insert' ⊤     false t     i     v m = m t
  -- insert' (μ f) false ⟨ t ⟩ ⟨ i ⟩ v m = ⟨ insertF' f f t i v m ⟩

  deleteF' : ∀ f g {B} → Fᵀ f (μ g) B → ⟦ f ⟧ᶠ (⟦μ⟧ g) → B → (B → B) → Fᵀ f (μ g) B
  deleteF' = {!!}
  -- insertF' I       h ⟨ t ⟩       ⟨ i ⟩     v m = ⟨ insertF' h h t i v m ⟩
  -- insertF' (K a)   h t           i         v m = insert' a false t i v m
  -- insertF' (f + g) h (left l)    (inl i)   v m = left (insertF' f h l i v m)
  -- insertF' (f + g) h (left l)    (inr i)   v m = both l (singleF g h i v)
  -- insertF' (f + g) h (right r)   (inl i)   v m = both (singleF f h i v) r
  -- insertF' (f + g) h (right r)   (inr i)   v m = right (insertF' g h r i v m)
  -- insertF' (f + g) h (both l r)  (inl i)   v m = both (insertF' f h l i v m) r
  -- insertF' (f + g) h (both l r)  (inr i)   v m = both l (insertF' g h r i v m)
  -- insertF' (f × g) h t           (il , ir) v m = insertF' f h t il (singleF g h ir v) (λ t → insertF' g h t ir v m)

--------------------------------------------------------------------------------

