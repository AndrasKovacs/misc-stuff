
open import Lib hiding (⊤)
import Lib as L using (⊤)

mutual
  -- Types
  data U : Set where
    ⊤ : U
    μ : F → U

  -- Functors
  data F : Set where
    I       : F
    K       : U → F
    _+_ _*_ : F → F → F

infixr 5 _+_
infixr 6 _*_

mutual
  ⟦_⟧ : U → Set
  ⟦ ⊤   ⟧ = L.⊤
  ⟦ μ f ⟧ = Fix f

  ⟦_⟧ᶠ : F → Set → Set
  ⟦ I     ⟧ᶠ A = A
  ⟦ K a   ⟧ᶠ _ = ⟦ a ⟧
  ⟦ f + g ⟧ᶠ A = ⟦ f ⟧ᶠ A ⊎ ⟦ g ⟧ᶠ A
  ⟦ f * g ⟧ᶠ A = ⟦ f ⟧ᶠ A × ⟦ g ⟧ᶠ A

  data Fix (f : F) : Set where
    fold : ⟦ f ⟧ᶠ (Fix f) → Fix f

mutual
  Uᵀ : (a : U) → (⟦ a ⟧ → Set) → Set
  Uᵀ ⊤     A = A tt
  Uᵀ (μ f) A = μᵀ f A

  Fᵀ : (f : F)(a : U) → (⟦ f ⟧ᶠ ⟦ a ⟧ → Set) → Set
  Fᵀ I       a A = Uᵀ a A
  Fᵀ (K a)   _ A = Uᵀ a A
  Fᵀ (f + g) a A = Fᵀ f a (A ∘ inl) × Fᵀ g a (A ∘ inr)
  Fᵀ (f * g) a A = Fᵀ f a (λ x₁ → Fᵀ g a (λ x₂ → A (x₁ , x₂)))

  record μᵀ (f : F)(A : Fix f → Set) : Set where
    coinductive
    field unfold : Fᵀ f (μ f) (A ∘ fold)

open μᵀ

mutual
  lookup : ∀ a {B} → Uᵀ a B → (x : ⟦ a ⟧) → B x
  lookup ⊤     t x        = t
  lookup (μ f) t (fold x) = lookupᶠ f f (t .unfold) x

  lookupᶠ : ∀ f g {B} → Fᵀ f (μ g) B → (i : ⟦ f ⟧ᶠ (Fix g)) → B i
  lookupᶠ I       h t (fold i)  = lookupᶠ h h (t .unfold) i
  lookupᶠ (K a)   h t i         = lookup a t i
  lookupᶠ (f + g) h t (inl i)   = lookupᶠ f h (t .proj₁) i
  lookupᶠ (f + g) h t (inr i)   = lookupᶠ g h (t .proj₂) i  
  lookupᶠ (f * g) h t (i₁ , i₂) = lookupᶠ g h (lookupᶠ f h t i₁) i₂

  tabulate : ∀ a {B} → ((i : ⟦ a ⟧) → B i) → Uᵀ a B
  tabulate ⊤     g = g tt
  tabulate (μ f) g .unfold = tabulateF f f (g ∘ fold)

  {-# TERMINATING #-} -- Agda plz
  tabulateF : ∀ f g {B} → ((i : ⟦ f ⟧ᶠ (Fix g)) → B i) → Fᵀ f (μ g) B
  tabulateF I       h j .unfold = tabulateF h h (j ∘ fold)
  tabulateF (K a)   h j = tabulate a j
  tabulateF (f + g) h j = tabulateF f h (j ∘ inl) , tabulateF g h (j ∘ inr)
  tabulateF (f * g) h j = tabulateF f h λ i₁ → tabulateF g h λ i₂ → j (i₁ , i₂)

