
open import Lib hiding (_×_; ⊤)
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
  ⟦ μ f ⟧ = Fix f

  ⟦_⟧ᶠ : F → Set → Set
  ⟦ I     ⟧ᶠ A = A
  ⟦ K a   ⟧ᶠ _ = ⟦ a ⟧
  ⟦ f + g ⟧ᶠ A = ⟦ f ⟧ᶠ A ⊎ ⟦ g ⟧ᶠ A
  ⟦ f × g ⟧ᶠ A = ⟦ f ⟧ᶠ A L.× ⟦ g ⟧ᶠ A

  data Fix (f : F) : Set where
    fold : ⟦ f ⟧ᶠ (Fix f) → Fix f

mutual
  *ᵀ : * → (Set → Set)
  *ᵀ ⊤     A = A
  *ᵀ (μ f) A = μᵀ f A

  Fᵀ : F → * → (Set → Set)
  Fᵀ I       a   = *ᵀ a
  Fᵀ (K a)   _   = *ᵀ a
  Fᵀ (f + g) a A = Fᵀ f a A L.× Fᵀ g a A
  Fᵀ (f × g) a A = Fᵀ f a (Fᵀ g a A)

  record μᵀ (f : F)(A : Set) : Set where
    coinductive
    field unfold : Fᵀ f (μ f) A

open μᵀ

mutual
  lookup : ∀ a {B} → *ᵀ a B → (⟦ a ⟧ → B)
  lookup ⊤     t i        = t
  lookup (μ f) t (fold i) = lookupF f f (t .unfold) i 

  lookupF : ∀ f g {B} → Fᵀ f (μ g) B → ⟦ f ⟧ᶠ (Fix g) → B
  lookupF I       h t (fold i)  = lookupF h h (t .unfold) i 
  lookupF (K a)   h t i         = lookup a t i
  lookupF (f + g) h t (inl i)   = lookupF f h (t .proj₁) i
  lookupF (f + g) h t (inr i)   = lookupF g h (t .proj₂) i  
  lookupF (f × g) h t (i₁ , i₂) = lookupF g h (lookupF f h t i₁) i₂

mutual
  tabulate : ∀ a {B} → (⟦ a ⟧ → B) → *ᵀ a B
  tabulate ⊤     g = g tt
  tabulate (μ f) g .unfold = tabulateF f f (g ∘ fold)

  {-# TERMINATING #-} -- Agda plz
  tabulateF : ∀ f g {B} → (⟦ f ⟧ᶠ (Fix g) → B) → Fᵀ f (μ g) B
  tabulateF I       h j .unfold = tabulateF h h (j ∘ fold)
  tabulateF (K a)   h j = tabulate a j
  tabulateF (f + g) h j = tabulateF f h (j ∘ inl) , tabulateF g h (j ∘ inr)
  tabulateF (f × g) h j = tabulateF f h λ i₁ → tabulateF g h λ i₂ → j (i₁ , i₂)

-- Examples
--------------------------------------------------------------------------------

nat : *
nat = μ (K ⊤ + I)

pattern z   = fold (inl tt)
pattern s n = fold (inr n)

five : ⟦ nat ⟧
five = s (s (s (s (s z))))

add : ⟦ nat ⟧ → ⟦ nat ⟧ → ⟦ nat ⟧
add z     b = b
add (s a) b = s (add a b)

tree : *
tree = μ (K ⊤ + (I × I))

pattern leaf     = fold (inl tt)
pattern node l r = fold (inr (l , r))

size : ⟦ tree ⟧ → ⟦ nat ⟧
size leaf       = s z
size (node l r) = add (size l) (size r)

sizeᵀ : *ᵀ tree ⟦ nat ⟧
sizeᵀ = tabulate tree size

t1 : ⟦ tree ⟧
t1 = node (node leaf leaf) leaf

s1 : ⟦ nat ⟧
s1 = lookup tree sizeᵀ t1

test = sizeᵀ .unfold .proj₂ .unfold .proj₂ .unfold

--------------------------------------------------------------------------------

-- todo: investigate fixed points of (* → *) → (* → *)
-- see if nice induction for nested types falls out

