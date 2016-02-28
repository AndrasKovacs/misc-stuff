module Chapter03 where

open import Data.Product
open import Function
open import Data.Empty
open import Data.Unit
open import Data.Sum
open import Data.Bool

record Con : Set₁ where
  constructor _◃_
  field
    Sh : Set
    Po : Sh → Set
  ⟦_⟧ᶜ : Set → Set
  ⟦_⟧ᶜ X = Σ Sh λ s → Po s → X
open Con public       
infixr 1 _◃_

-- _⟨?⟩_ : ∀ {ℓ} {P : Bool → Set ℓ} → P true → P false → ∀ b → P b
-- (t ⟨?⟩ f) true  = t
-- (t ⟨?⟩ f) false = f

ⱽ_ = uncurry
infix 0 ⱽ_

Kᶜ : Set → Con
Kᶜ A = A ◃ const ⊥

Iᶜ : Con
Iᶜ = ⊤ ◃ const ⊤

_+ᶜ_ : Con → Con → Con
(S ◃ P) +ᶜ (S' ◃ P') = (S ⊎ S') ◃ [ P , P' ]′

_×ᶜ_ : Con → Con → Con
(S ◃ P) ×ᶜ (S' ◃ P') = (S × S') ◃ λ {(s , s') → P s ⊎ P' s' }

Σᶜ : (A : Set) (C : A → Con) → Con
Σᶜ A C = ∃ (Sh ∘ C) ◃ λ {(a , s) → Po (C a) s}

-- skip exercises 3.1, 3.2

_→ᶜ_ : Con → Con → Set
(S ◃ P) →ᶜ (S' ◃ P') = ∃ λ (f : S → S') → ∀ s → P' (f s) → P s

_/ᶜ_ : ∀ {C C'} → C →ᶜ C' → ∀ {X} → ⟦ C ⟧ᶜ X → ⟦ C' ⟧ᶜ X
(to , fro) /ᶜ (s , k) = to s , k ∘ fro s

morphᶜ : ∀ {C C'} → (∀ {X} → ⟦ C ⟧ᶜ X → ⟦ C' ⟧ᶜ X) → C →ᶜ C'
morphᶜ f = (λ s → proj₁ (f (s , id))) , (λ s → proj₂ (f (s , id)))

idᶜ : ∀ {C} → C →ᶜ C
idᶜ = id , λ s z → z

_∘ᶜ_ : ∀ {C D E} → D →ᶜ E → C →ᶜ D → C →ᶜ E
(to , fro) ∘ᶜ (to' , fro') = to ∘ to' , λ s z → fro' s (fro (to' s) z)

data W (C : Con) : Set where
  ⟨_⟩ : ⟦ C ⟧ᶜ (W C) → W C

unW : ∀ {C} → W C → ⟦ C ⟧ᶜ (W C)
unW ⟨ x ⟩ = x

NatW : Set
NatW = W (Bool ◃ (λ {true → ⊥; false → ⊤}))

zeroW : NatW
zeroW = ⟨ true , const ⟨ (true , (λ ())) ⟩ ⟩

sucW : NatW → NatW
sucW ⟨ n ⟩ = ⟨ false , const ⟨ n ⟩ ⟩

recW : ∀ {α}{A : Set α} → A → (NatW → A → A) → NatW → A
recW z s ⟨ true  , f ⟩ = z
recW z s ⟨ false , f ⟩ = s (f tt) (recW z s (f tt))

addW : NatW → NatW → NatW
addW a b = recW b (const sucW) a

_⋆_ : Con → Set → Set
C ⋆ X = W (Kᶜ X +ᶜ C)

open import Chapter01

conFunctor : ∀ {C} → EndoFunctor ⟦ C ⟧ᶜ
conFunctor = rec (λ {f (s , fa) → s , f ∘ fa})

freeMonad : (C : Con) → Monad (_⋆_ C)
freeMonad C = rec (λ x → ⟨ ((inj₁ x) , (λ ())) ⟩) bindCon where
   bindCon : ∀ {A B} → C ⋆ A → (A → C ⋆ B) → C ⋆ B
   bindCon ⟨ inj₁ x , c ⟩ f = f x
   bindCon ⟨ inj₂ s , c ⟩ f = ⟨ ((inj₂ s) , (λ p → bindCon (c p) f)) ⟩

⋆-map : ∀ {C A B} → (A → B) → C ⋆ A → C ⋆ B
⋆-map f ⟨ inj₁ x , next ⟩ = ⟨ ((inj₁ (f x)) , (λ bot → ⋆-map f (next bot))) ⟩
⋆-map f ⟨ inj₂ y , next ⟩ = ⟨ ((inj₂ y)     , (λ p   → ⋆-map f (next p))) ⟩

data _∈⋆_ {A C} (a : A) : C ⋆ A → Set where
  here  : ∀ {c} → a ∈⋆ ⟨ inj₁ a , c ⟩
  there : ∀ {s c} p → a ∈⋆ c p → a ∈⋆ ⟨ inj₂ s , c ⟩

_⋆ᶜ : Con → Con
_⋆ᶜ C = (C ⋆ ⊤) ◃ _∈⋆_ tt

to' : ∀ {X} C (s : C ⋆ ⊤) → (Po (C ⋆ᶜ) s → X) → C ⋆ X
to' C ⟨ inj₁ x , next ⟩ f = ⟨ inj₁ (f here) , (λ ()) ⟩
to' C ⟨ inj₂ s , next ⟩ f = ⟨ inj₂ s , (λ p → to' C (next p) (f ∘ there p)) ⟩

to : ∀ {X} C → ⟦ C ⋆ᶜ ⟧ᶜ X → C ⋆ X
to = uncurry ∘ to'

fro : ∀ {X} C → C ⋆ X → ⟦ C ⋆ᶜ ⟧ᶜ X 
fro C ⟨ inj₁ x , _    ⟩ = ⟨ inj₁ tt , (λ ()) ⟩ , λ _ → x
fro C ⟨ inj₂ s , next ⟩ =
  ⟨ inj₂ s , (λ p → proj₁ (fro C (next p))) ⟩ ,
  (λ {(there p p') → proj₂ (fro C (next p)) p'})

-- module FM {C} = Monad (freeMonad C)

call : ∀ {C} → (s : Sh C) → C ⋆ Po C s
call s = ⟨ inj₂ s , (λ p → ⟨ inj₁ p , (λ ()) ⟩) ⟩

Π⊥ : (S : Set) (T : S → Set) → Set
Π⊥ S T = ∀ s → (S ◃ T) ⋆ T s

open import Data.Nat
open import Data.Maybe

-- First take a look at Free Turing Completenes paper
gas : ∀ {S T} → ℕ → Π⊥ S T → (s : S) → Maybe (T s)
gas zero    f s = nothing
gas (suc n) f s with f s
... | ⟨ inj₁ x  , next ⟩ = just x
... | ⟨ inj₂ s' , next ⟩ = {!!}




