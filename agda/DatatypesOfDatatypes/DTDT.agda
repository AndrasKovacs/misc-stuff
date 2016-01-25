
module DTDT where

open import Function

module Chapter01 where
  
  record EndoFunctor (F : Set → Set) : Set₁ where
    constructor rec  
    field
      map : ∀ {S T} → (S → T) → F S → F T
  open EndoFunctor ⦃...⦄ public

  record Applicative (F : Set → Set) : Set₁ where
    constructor rec
    infixl 2 _⊛_ 
    field
       pure : ∀ {X} → X → F X
       _⊛_  : ∀ {S T} → F (S → T) → F S → F T
    applicativeEndoFunctor : EndoFunctor F
    applicativeEndoFunctor = record {map = _⊛_ ∘ pure}
  open Applicative ⦃...⦄ public

  open import Data.Vec hiding (_>>=_; map; _⊛_)

  instance
    applicativeVec : ∀ {n} → Applicative (flip Vec n)
    applicativeVec = record { pure = replicate ; _⊛_ = Data.Vec._⊛_ }

    applicativeFun : ∀ {S} → Applicative λ X → S → X
    applicativeFun = record { pure = const ; _⊛_ = _ˢ_ }

  record Monad (F : Set → Set) : Set₁ where
    constructor rec  
    field
      return : ∀ {X} → X → F X
      _>>=_  : ∀ {S T} → F S → (S → F T) → F T
    monadApplicative : Applicative F
    monadApplicative = record {
        pure = return
      ; _⊛_ = λ mf mx → mf >>= λ f → mx >>= λ x → return (f x)
      }
  open Monad ⦃...⦄

  module _ where
    open import Data.Nat
    instance
      monadVec : ∀ {n} → Monad (flip Vec n)
      monadVec {zero}  = record { return = pure ; _>>=_ = λ _ _ → [] }
      monadVec {suc n} = record { return = pure ; _>>=_ = λ ma f → Data.Vec.map (head ∘ f) ma }

  instance
    applicativeId : Applicative id
    applicativeId = record { pure = id ; _⊛_ = id }

    applicativeComp : ∀ {F G} → Applicative F → Applicative G → Applicative (F ∘ G)
    applicativeComp apF apG = record {
      pure = Applicative.pure apF ∘ Applicative.pure apG  ;
      _⊛_ = liftA2 apF (Applicative._⊛_ apG) }
      where liftA2 : ∀ {A B C F} → Applicative F → (A → B → C) → F A → F B → F C
            liftA2 ap f a b = (ap Applicative.⊛ (ap Applicative.⊛ Applicative.pure ap f) a) b

  record Monoid (X : Set) : Set where
    constructor rec
    infixr 4 _∙_
    field
      ε   : X
      _∙_ : X → X → X
    monoidApplicative : Applicative (const X)
    monoidApplicative = rec (const ε) _∙_
  open Monoid ⦃...⦄ public
    
  instance
    open import Data.Product   
    applicative-× : ∀ {F G} → Applicative F → Applicative G → Applicative (λ X → F X × G X)
    applicative-× apF apG = rec
      (λ x → (Applicative.pure apF x) , Applicative.pure apG x)
      (λ {(ff , gf) (fx , gx) → ((apF Applicative.⊛ ff) fx) , ((apG Applicative.⊛ gf) gx) })

  record Traversable (F : Set → Set) : Set₁ where
    constructor rec
    field
      traverse : ∀ {G S T} ⦃ AG : Applicative G ⦄ → (S → G T) → F S → G (F T)
    traversableEndoFunctor : EndoFunctor F
    traversableEndoFunctor = rec traverse -- identity applicative
  open Traversable ⦃...⦄ public

  instance
    traversableVec : ∀ {n} → Traversable (flip Vec n)
    traversableVec = rec vtr
      where
        vtr : ∀ {A : Set}{n B F}⦃ _ : Applicative F ⦄ → (A → F B) → Vec A n → F (Vec B n)
        vtr f []               = pure []
        vtr ⦃ aF ⦄ f (a ∷ as) = pure ⦃ aF ⦄ _∷_ ⊛ f a ⊛ vtr ⦃ aF ⦄ f as

  transpose : ∀ {n m}{X : Set} → Vec (Vec X n) m → Vec (Vec X m) n
  transpose = traverse id

  open import Data.Unit

  crush : ∀ {A M F} ⦃ _ : Traversable F ⦄ ⦃ _ : Monoid M ⦄ → (A → M) → F A → M
  crush {{_}}{{m}} = traverse {T = ⊤} {{monoidApplicative {{m}}}}

  open import Data.Bool

  _⟨?⟩_ : ∀ {ℓ} {P : Bool → Set ℓ} → P true → P false → ∀ b → P b
  (t ⟨?⟩ f) true  = t
  (t ⟨?⟩ f) false = f

  _+_ : Set → Set → Set
  S + T = Σ Bool (S ⟨?⟩ T)

  open import Data.Nat renaming (_+_ to _+ℕ_; _*_ to _*ℕ_)

  record Normal : Set₁ where
    constructor _/_
    field
      Shape : Set
      size  : Shape → ℕ
    ⟦_⟧ₙ : Set → Set
    ⟦ X ⟧ₙ = Σ Shape (Vec X ∘ size)
  open Normal public
  infixr 0 _/_

  VecN : ℕ → Normal
  VecN n = ⊤ / const n

  ListN : Normal
  ListN = ℕ / id

  Kₙ : Set → Normal
  Kₙ A = A / const 0

  IKₙ : Normal
  IKₙ = VecN 1
  


