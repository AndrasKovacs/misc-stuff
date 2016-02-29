
module Chapter04 where

open import Data.Product
open import Level renaming (suc to lsuc; zero to lzero)
open import Function
open import Data.Unit
open import Data.Bool
open import Data.Empty

record _▹_ (I J : Set) : Set₁ where
  constructor _◃_$_
  field
    Sh : J → Set
    Po : ∀ j → Sh j → Set
    ri : ∀ j (s : Sh j)(p : Po j s) → I
  ⟦_⟧ : (I → Set) → (J → Set)
  ⟦_⟧ X j = Σ (Sh j) λ s → (p : Po j s) → X (ri j s p)
open _▹_ public

_⇒_ : ∀ {k l}{I : Set k} → (I → Set l) → (I → Set l) → Set (l ⊔ k)
X ⇒ Y = ∀ {i} → X i → Y i

imap : ∀ {I J}{C : I ▹ J}{X Y} → (X ⇒ Y) → ⟦ C ⟧ X ⇒ ⟦ C ⟧ Y
imap f (s , k) = s , f ∘ k

data ITree {J : Set}(C : J ▹ J)(j : J) : Set where
  ⟨_⟩ : ⟦ C ⟧ (ITree C) j → ITree C j

Natᶜ : ⊤ ▹ ⊤
Natᶜ = const Bool ◃ const (λ { true → ⊥ ; false → ⊥ }) $ _

zeroᶜ : ITree Natᶜ tt
zeroᶜ = ⟨ true , (λ ()) ⟩

sucᶜ :  ITree Natᶜ tt → ITree Natᶜ tt
sucᶜ n = ⟨ false , const n ⟩

open import Data.Nat hiding (_⊔_)

VecC : Set → ℕ ▹ ℕ
VecC A = VS ◃ {!!} $ {!!} where
  VS : ℕ → Set
  VS zero    = ⊤
  VS (suc _) = A

  VP : {j : ℕ} → VS j → Set
  VP {zero}  s = ⊥
  VP {suc j} s = ⊤

  Vr : ∀ {n}{s : VS n} → VP {n} s → ℕ
  Vr {zero}  p = {!!}
  Vr {suc n} p = {!!}


