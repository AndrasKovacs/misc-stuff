{-# OPTIONS --without-K #-}

module ch01 where

module ex1-3 where
  open import Lib hiding (Σ; proj₁; proj₂; _,_)

  data Σ (A : Set)(B : A → Set) : Set where
    _,_ : (a : A)(b : B a) → Σ A B
  
  π₁ : ∀ {A B} → Σ A B → A
  π₁ (a , _) = a
  
  π₂ : ∀ {A B}(p : Σ A B) → B (π₁ p)
  π₂ (_ , b) = b

  ,η : ∀ {A}{B}(p : Σ A B) → (π₁ p , π₂ p) ≡ p
  ,η (a , b) = refl
  
  Σ-ind : ∀{A : Set}{B : A → Set}(Σᴾ : Σ A B → Set)(,ᴾ : ∀ a b → Σᴾ (a , b)) → ∀ p → Σᴾ p
  Σ-ind {A}{B} Σᴾ ,ᴾ p = coe (Σᴾ & ,η p) (,ᴾ (π₁ p) (π₂ p))

  Σ-ind-β :
    ∀{A : Set}{B : A → Set}(Σᴾ : Σ A B → Set)(,ᴾ : ∀ a b → Σᴾ (a , b))
    → ∀ a b → Σ-ind Σᴾ ,ᴾ (a , b) ≡ ,ᴾ a b
  Σ-ind-β Σᴾ ,ᴾ a b = refl

module ex1-6 where
  open import Lib hiding (_×_; _,_)

  _×_ : Set → Set → Set
  A × B = (b : Bool) → if b then A else B

  _,_ : ∀ {A B} → A → B → A × B
  (a , b) false = b
  (a , b) true  = a

  ,η : ∀ {A B}(p : A × B) → (p true , p false) ≡ p
  ,η p = ext λ {true → refl; false → refl}

  ×-ind : ∀ {A B : Set}(×ᴾ : A × B → Set) → (∀ a b → ×ᴾ (a , b)) → ∀ p → ×ᴾ p
  ×-ind ×ᴾ ,ᴾ p  = coe (×ᴾ & ,η p) (,ᴾ (p true) (p false))

  

