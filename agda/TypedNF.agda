
-- Only vars
--------------------------------------------------------------------------------

-- infixl 5 _,_
-- infix 3 _∋_
-- infix 4 _⊢_ 

-- data Con : Set
-- data Ty Γ : Set
-- data _∋_ : (Γ : Con) → Ty Γ → Set
-- data _⊢_ (Γ : Con) : Ty Γ → Set

-- data Con where
--   ∙   : Con
--   _,_ : (Γ : Con) (A : Ty Γ) → Con

-- data Ty Γ where
--   U  : Ty Γ
--   El : (t : Γ ⊢ U) → Ty Γ

-- wkTy : ∀ {Γ B} → Ty Γ → Ty (Γ , B)
-- wkTm : ∀ {Γ A B} → Γ ⊢ A → (Γ , B) ⊢ wkTy A

-- data _∋_ where
--   zero : ∀{Γ}{A : Ty Γ} → Γ , A ∋ wkTy A
--   suc  : ∀{Γ}{A B : Ty Γ} → Γ ∋ A → Γ , B ∋ wkTy A

-- data _⊢_ Γ where
--   var : ∀ {A} → Γ ∋ A → Γ ⊢ A

-- wkTm (var x) = var (suc x)
-- wkTy U       = U
-- wkTy (El t)  = El (wkTm t)

-- -- example
-- p : (∙ , U , El (var zero) , El (var (suc zero))) ⊢ El (var (suc (suc zero)))
-- p = var zero





-- Problem: coherence, essentially
-- wkTm needs wkTy-comm needs wkTm-comm needs wkTm, ...

-- Vars + non-dependent functions
--------------------------------------------------------------------------------

{-# OPTIONS --no-termination-check #-}

module TypedNF where

open import Data.Nat
open import Relation.Binary.PropositionalEquality

infixl 5 _,_
infix 3 _∋_
infix 4 _⊢_ _⊢n_
infixl 8 _∙_
infixr 5 _⇒_

data Con : ℕ → Set
data Ty {n} (Γ : Con n) : Set
data _∋_ : ∀{n}(Γ : Con n) → Ty Γ → Set
data _⊢_ {n}(Γ : Con n) : Ty Γ → Set
data _⊢n_ {n} (Γ : Con n) : Ty Γ → Set

data Con where
  ε   : Con 0
  _,_ : ∀ {n}(Γ : Con n) (A : Ty Γ) → Con (suc n)

strip : ∀{n i} → Con n → i ≤ n → Con (n ∸ i)
strip Γ       z≤n     = Γ
strip (Γ , _) (s≤s p) = strip Γ p

data Ty {n} Γ where
  U   : Ty Γ
  El  : (t : Γ ⊢ U) → Ty Γ
  _⇒_ : (A B : Ty Γ) → Ty Γ

insert : ∀{i n}(Γ : Con n) (p : i ≤ n) → Ty (strip Γ p) → Con (suc n)
wkTy   : ∀{i n}{Γ : Con n} (p : i ≤ n) (A' : Ty (strip Γ p)) → Ty Γ → Ty (insert Γ p A')
wkTm   : ∀{i n}{Γ : Con n} (p : i ≤ n) (A' : Ty (strip Γ p)) {A : Ty Γ} → Γ ⊢ A  → insert Γ p A' ⊢ wkTy p A' A
wkVar  : ∀{i n}{Γ : Con n} (p : i ≤ n) (A' : Ty (strip Γ p)) {A : Ty Γ} → Γ ∋ A  → insert Γ p A' ∋ wkTy p A' A
wkNe   : ∀{i n}{Γ : Con n} (p : i ≤ n) (A' : Ty (strip Γ p)) {A : Ty Γ} → Γ ⊢n A → insert Γ p A' ⊢n wkTy p A' A

insert Γ       z≤n     A' = Γ , A'
insert (Γ , A) (s≤s p) A' = insert Γ p A' , wkTy p A' A

-- 1. wkTy return type + proof
-- 2. try with TERMINATING
-- 3. use parameters
-- 4. Hoffman syntax and semantics of dependent types

-- standard model = presheaf model with 1-elem category


data _∋_ where
  zero : ∀{n Γ}{A : Ty {n} Γ}   → Γ , A ∋ wkTy z≤n A A
  suc  : ∀{n Γ}{A B : Ty {n} Γ} → Γ ∋ A → Γ , B ∋ wkTy z≤n B A

suc-∋ : ∀{n Γ}{A B : Ty {n} Γ} → Γ ∋ A → Γ , B ∋ wkTy z≤n B A
suc-∋ = suc

zero-∋ : ∀{n Γ}{A : Ty {n} Γ}   → Γ , A ∋ wkTy z≤n A A
zero-∋ = zero

data _⊢_ {n} Γ where
  ne  : ∀ {A} → Γ ⊢n A → Γ ⊢ A
  ƛ   : ∀ {A B} → Γ , A ⊢ wkTy z≤n A B → Γ ⊢ A ⇒ B

data _⊢n_ {n} Γ where
  var : ∀ {A} → Γ ∋ A → Γ ⊢n A
  _∙_ : ∀ {A B} → Γ ⊢n A ⇒ B → Γ ⊢ A → Γ ⊢n B

wkTy p A' U       = U
wkTy p A' (El t)  = El (wkTm p A' t)
wkTy p A' (A ⇒ B) = wkTy p A' A ⇒ wkTy p A' B

wkNe p A' (var v) = var (wkVar p A' v)
wkNe p A' (n ∙ t) = wkNe p A' n ∙ wkTm p A' t
wkVar             z≤n     A' v       = suc v
wkVar {Γ = Γ , A} (s≤s p) A' zero    = {!zero-∋ {Γ = insert Γ p A'}{wkTy p A' A}!}
wkVar {Γ = Γ , A} (s≤s p) A' (suc v) = {!suc-∋ {B = wkTy p A' A}(wkVar p A' v)!}

wkNe-comm :
  ∀ {i n}{Γ : Con n} (p : i ≤ n) (A' : Ty (strip Γ p)) A B (x : Γ ⊢n B)
  → wkNe (s≤s p) A' (wkNe z≤n A x) ≡ {!wkNe p A' x!} -- wkNe z≤n (wkTy p A' A) (wkNe p A' x)

wkTm-comm :
  ∀ {i n}{Γ : Con n} (p : i ≤ n) (A' : Ty (strip Γ p)) A (t : Γ ⊢ U)
  → wkTm (s≤s p) A' (wkTm z≤n A t) ≡  wkTm z≤n (wkTy p A' A) (wkTm p A' t)  

wkTy-comm :
  ∀ {i n}{Γ : Con n} (p : i ≤ n) (A' : Ty (strip Γ p)) A B 
  → wkTy (s≤s p) A' (wkTy z≤n A B) ≡ wkTy z≤n (wkTy p A' A) (wkTy p A' B)

wkTm p A' (ne n) = ne (wkNe p A' n)
wkTm {i}{n}{Γ} p A' (ƛ {A}{B} t)  =
  ƛ (subst (insert Γ p A' , wkTy p A' A ⊢_) (wkTy-comm p A' A B) (wkTm (s≤s p) A' t))

wkNe-comm p A' A n       = {!!}
wkTm-comm p A' A (ne x)  = {!!} -- cong ne (wkNe-comm p A' A U x)

wkTy-comm p A' A U       = refl
wkTy-comm p A' A (El t)  = cong El (wkTm-comm p A' A t)
wkTy-comm p A' A (B ⇒ C) = cong₂ _⇒_ (wkTy-comm p A' A B) (wkTy-comm p A' A C)

