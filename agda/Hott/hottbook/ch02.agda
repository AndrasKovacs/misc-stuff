{-# OPTIONS --without-K #-}

module ch02 where
open import Lib

module EckmannHilton where
  
  Set* : Set₁
  Set* = ∃ λ (A : Set) → A
  
  Ω : ℕ → Set* → Set
  Ω zero    (A , a) = A
  Ω (suc n) (A , a) = Ω n ((a ≡ a) , refl)
  
  _★_ : {A : Set}{a b c : A}{p q : a ≡ b}{r s : b ≡ c} → p ≡ q → r ≡ s → (p ◾ r) ≡ (q ◾ s)
  _★_ {A} {a} {b} {c} {p} {q} {r} {s} α β = (_◾ r) & α ◾ (q ◾_) & β
  
  _★'_ : {A : Set}{a b c : A}{p q : a ≡ b}{r s : b ≡ c} → p ≡ q → r ≡ s → (p ◾ r) ≡ (q ◾ s)
  _★'_ {A} {a} {b} {c} {p} {q} {r} {s} α β = (p ◾_) & β ◾ (_◾ s) & α
  
  id& : ∀ {α}{A : Set α}{x y : A}(p : x ≡ y) → id & p ≡ p
  id& refl = refl
  
  idr : ∀ {α}{A : Set α}{x y : A}(p : x ≡ y) → (p ◾ refl) ≡ p
  idr refl = refl
  
  inv : ∀ {α}{A : Set α}{x y : A}(p : x ≡ y) → (p ◾ p ⁻¹) ≡ refl
  inv refl = refl
  
  ◾ₗrefl :
    ∀ {A : Set}{a b : A}{p q : a ≡ b}(α : p ≡ q) → ((_◾ refl) & α) ≡ (idr p ◾ α ◾ idr q ⁻¹)
  ◾ₗrefl {p = p} refl = inv (idr p) ⁻¹
  
  comm : ∀ {A*}(α β : Ω 2 A*) → (α ◾ β) ≡ (β ◾ α)
  comm {A , a} α β = s1 ◾ s2 α β ◾ s3
  
    where
      s1 : (α ◾ β) ≡ (α ★ β)
      s1 rewrite id& β | ◾ₗrefl α ◾ idr α = refl
      
      s2 : ∀ {a b c : A}{p q : a ≡ b}{r s : b ≡ c}(α : p ≡ q)(β : r ≡ s) → (α ★ β) ≡ (α ★' β)
      s2 {a} {b} {c} {p} refl refl = refl
      
      s3 : (α ★' β) ≡ (β ◾ α)
      s3 rewrite id& β | ◾ₗrefl α ◾ idr α = refl
      

