
{-# OPTIONS --type-in-type --no-positivity-check --no-termination-check #-}

module _ where

open import Function
open import Data.Nat

data List (A : Set) : Set where
  []  : List A
  _∷_ : A → List A → List A
infixr 5 _∷_

_++_ : ∀ {A} → List A → List A → List A
[]       ++ ys = ys
(x ∷ xs) ++ ys = x ∷ xs ++ ys

record Functor (F : Set → Set) : Set where
  constructor rec
  field map : ∀ {A B} → (A → B) → F A → F B
open Functor {{...}}

record Monad (M : Set → Set) : Set where
  constructor rec
  field
    pure             : ∀ {A} → A → M A
    _>>=_            : ∀ {A B} → M A → (A → M B) → M B
    {{MonadFunctor}} : Functor M
  infixl 1 _>>=_ _>>_

  join : ∀ {A} → M (M A) → M A
  join mma = mma >>= id

  _>>_ : ∀ {A B} → M A → M B → M B
  ma >> mb = ma >>= λ _ → mb
  
open Monad {{...}}

instance
  FunctorList : Functor List
  FunctorList = rec mapList where
    mapList : ∀ {A B} → (A → B) → List A → List B
    mapList f []       = []
    mapList f (x ∷ xs) = f x ∷ mapList f xs  

  MonadList : Monad List
  MonadList = rec (λ a → a ∷ []) bindList where
    bindList : ∀ {A B} → List A → (A → List B) → List B
    bindList []       f = []
    bindList (x ∷ xs) f = f x ++ bindList xs f

--------------------------------------------------------------------------------

data Free (F : Set → Set) (A : Set) : Set where
  val  : A → Free F A
  free : F (Free F A) → Free F A

instance
  FunctorFree : ∀ {F}{{_ : Functor F}} → Functor (Free F)
  FunctorFree {F} = rec mapFree where  
    mapFree : ∀ {A B} → (A → B) → Free F A → Free F B
    mapFree f (val x)   = val (f x)
    mapFree f (free fa) = free (map (mapFree f) fa)
    
  MonadFree : ∀ {F}{{_ : Functor F}} → Monad (Free F)
  MonadFree {F} = rec val bindFree where
    bindFree : ∀ {A B} → Free F A → (A → Free F B) → Free F B
    bindFree (val x)   f = f x
    bindFree (free fa) f = free (map (flip bindFree f) fa)

data Reader R K : Set where
  Ask : (R → K) → Reader R K

instance
  FunctorReader : ∀ {R} → Functor (Reader R)
  FunctorReader = rec λ f → λ {(Ask k) → Ask (f ∘ k)}

data State S K : Set where
  Get : (S → K) → State S K
  Put : S → K → State S K

instance
  FunctorState : ∀ {S} → Functor (State S)
  FunctorState = rec λ f → λ {(Get k) → Get (f ∘ k); (Put s k) → Put s (f k)}

--------------------------------------------------------------------------------

data _⊎_ (F G : Set → Set) A : Set where
  inl : F A → (F ⊎ G) A
  inr : G A → (F ⊎ G) A

instance
  Functor⊎ : ∀ {F G}{{_ : Functor F}}{{_ : Functor G}} → Functor (F ⊎ G)
  Functor⊎ {F}{G} = rec λ f → λ {(inl fa) → inl (map f fa); (inr ga) → inr (map f ga)}


--------------------------------------------------------------------------------

open import Data.Unit
open import Data.Empty

-- open import Data.Unit
-- open import Data.Empty
-- open import Data.Product

-- ask : ∀ {R S} → Free (Reader R ⊎ State S) R
-- ask = free $ inl $ Ask pure

-- get : ∀ {R S} → Free (Reader R ⊎ State S) S
-- get = free $ inr $ Get pure

-- put : ∀  {R S} → S → Free (Reader R ⊎ State S) ⊤
-- put n = free $ inr $ Put n (pure tt)

-- iter : ∀ {A} → (A → A) → A → ℕ → A
-- iter s z zero    = z
-- iter s z (suc n) = s (iter s z n)

-- times : ∀ {M A}{{_ : Monad M}} → ℕ → M A → M ⊤
-- times n ma = iter (ma >>_) (pure tt) n

-- foo : Free (Reader ℕ ⊎ State ℕ) ⊤
-- foo =
--   ask >>= λ r →
--   get >>= λ n →
--   put $ r + n

-- run : ∀ {R S A} → Free (Reader R ⊎ State S) A → R → S → A × S
-- run (val a)                 r s = a , s
-- run (free (inl (Ask k)))    r s = run (k r) r s
-- run (free (inr (Get k)))    r s = run (k s) r s
-- run (free (inr (Put s' k))) r s = run k r s'


