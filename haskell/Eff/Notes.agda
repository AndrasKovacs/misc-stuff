
{-# OPTIONS --type-in-type --no-positivity-check --no-termination-check #-}

-- Agda normalization tests

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
open import Data.Product

get : ∀ {S} → Free (State S) S
get = free (Get pure)

put : ∀ {S} → S → Free (State S) ⊤
put s = free (Put s (pure tt))

inc : Free (State ℕ) ⊤
inc = get >>= λ n → put (suc n)

Nat : Set
Nat = ∀ N → (N → N) → N → N

times : ∀ {M}{{_ : Monad M}} → Nat → M ⊤ → M ⊤
times n m = n _ (m >>_) (pure tt)

fromℕ : ℕ → Nat
fromℕ zero    N s z = z
fromℕ (suc n) N s z = s (fromℕ n N s z)

run : ∀ {S A} → Free (State S) A → S → A × S
run (val x)           s = x , s
run (free (Get k))    s = run (k s) s
run (free (Put s' k)) s = run k s'

-- we can't normalize past "times" - we'd need supercompilation for that
test = λ n → run $ times n inc

--------------------------------------------------------------------------------

-- inlined church state

CS : Set → Set → Set
CS S A = ∀ R → (A → R) → ((S → R) → R) → (S → R → R) → R

instance
  FunctorCS : ∀ {S} → Functor (CS S)
  FunctorCS = rec λ f ma R pure → ma R (pure ∘ f)

  MonadCS : ∀ {S} → Monad (CS S)
  MonadCS = rec
    (λ a _ pure _ _ → pure a)
    (λ ma f _ pure get put → ma _ (λ a → f a _ pure get put) get put )

get' : ∀ {S} → CS S S
get' = λ _ p get put → get p

put' : ∀ {S} → S → CS S ⊤
put' s = λ _ p get put → put s (p tt)

inc' : CS ℕ ⊤
inc' = get' >>= λ n → put' (suc n)

run' : ∀ {S A} → CS S A → S → A × S
run' ma = ma _ _,_ (λ got s → got s s) (λ s' put _ → put s')

test' = λ n → run' $ times n inc'

-- Plain state
--------------------------------------------------------------------------------

ST : Set → Set → Set
ST S A = S → A × S

instance
  FunctorST : ∀ {S} → Functor (ST S)
  FunctorST = rec (λ f ma s → let (a , s') = ma s in f a , s')

  MonadST : ∀ {S} → Monad (ST S)
  MonadST = rec _,_ (λ ma f → uncurry f ∘ ma)

get'' : ∀ {S} → ST S S
get'' = λ s → s , s

put'' : ∀ {S} → S → ST S ⊤
put'' s = λ _ → tt , s

inc'' : ST ℕ ⊤
inc'' = get'' >>= λ n → put'' (suc n)

test'' = λ n → times n inc''

