
module TypedNF2 where

open import Data.Nat
open import Relation.Binary.PropositionalEquality
open import Data.Product
open import Function

-- idea : try to implement weakening on preterms and prove commutativity there
-- define typed NF as relation, use weakening on preterms in definition
-- index by (∃ λ x → WellTyped x), try to prove IsProp (WellTyped x) alongside

Var : ℕ → Set
Var n = ∃ (_< n)

Ix : ℕ → Set
Ix n = ∃ (_≤ n)

vsuc : ∀ {n} → Var n → Var (suc n)
vsuc = map _ s≤s

isuc : ∀ {n} → Ix n → Ix (suc n)
isuc = map _ s≤s 

wkVar : ∀ {n} → Ix n → Var n → Var (suc n)
wkVar (zero  , p)     (b     , q)       = , s≤s q
wkVar (suc a , p)     (zero  , s≤s z≤n) = , s≤s z≤n
wkVar (suc a , s≤s p) (suc b , s≤s q)   = vsuc (wkVar (, p) (, q))

wkIx : ∀ {n} → Ix n → Ix n → Ix (suc n)
wkIx (zero  , p)     (b , q)         = , s≤s q
wkIx (suc a , p)     (zero , z≤n)    = , z≤n
wkIx (suc a , s≤s p) (suc m , s≤s q) = isuc (wkIx (, p) (, q))

data Ne' (n : ℕ) : Set
data Tm' (n : ℕ) : Set
data Ty' (n : ℕ) : Set
data Con' : ℕ → Set

data Ne' n where
  var : Var n → Ne' n
  _∙_ : Ne' n → Tm' n → Ne' n

data Tm' n where
  ne : Ne' n → Tm' n
  ƛ  : Ty' n → Tm' (suc n) → Tm' n

data Ty' n where
  U   : Ty' n
  El  : Tm' n → Ty' n
  _⇒_ : Ty' n → Ty' n → Ty' n

data Con' where
  ε   : Con' 0
  _,_ : ∀ {n} → Con' n → Ty' n → Con' (suc n)

wkNe : ∀ {n} → Ix n → Ne' n → Ne' (suc n)
wkTm : ∀ {n} → Ix n → Tm' n → Tm' (suc n)
wkTy : ∀ {n} → Ix n → Ty' n → Ty' (suc n)
wkNe i (var v) = var (wkVar i v)
wkNe i (f ∙ x) = wkNe i f ∙ wkTm i x
wkTm i (ne x)  = ne (wkNe i x)
wkTm i (ƛ A t) = ƛ (wkTy i A) (wkTm (map _ s≤s i) t)
wkTy i U       = U
wkTy i (El x)  = El (wkTm i x)
wkTy i (A ⇒ B) = wkTy i A ⇒ wkTy i B

wkVar-comm :
  ∀ {n} (a b : Ix n)(c : Var n)
  → wkVar (wkIx b a) (wkVar b c) ≡ wkVar (wkIx a b) (wkVar a c)
wkVar-comm (_ , z≤n)   (_ , z≤n)   _ = refl
wkVar-comm (_ , z≤n)   (_ , s≤s _) _ = refl
wkVar-comm (_ , s≤s _) (_ , z≤n)   _ = refl
wkVar-comm (_ , s≤s _) (_ , s≤s _) (_ , s≤s z≤n)     = refl
wkVar-comm (_ , s≤s p) (_ , s≤s q) (_ , s≤s (s≤s r)) =
  cong vsuc (wkVar-comm (, p) (, q) (, s≤s r))

wkTm-comm : ∀ {n} (i j : Ix n) A → wkTm (wkIx j i) (wkTm j A) ≡ wkTm (wkIx i j) (wkTm i A)
wkNe-comm : ∀ {n} (i j : Ix n) A → wkNe (wkIx j i) (wkNe j A) ≡ wkNe (wkIx i j) (wkNe i A)
wkTy-comm : ∀ {n} (i j : Ix n) A → wkTy (wkIx j i) (wkTy j A) ≡ wkTy (wkIx i j) (wkTy i A)
wkTm-comm i j (ne n)  = cong ne (wkNe-comm i j n)
wkTm-comm i j (ƛ A t) = cong₂ ƛ (wkTy-comm i j A) (wkTm-comm (isuc i) (isuc j) t)
wkNe-comm i j (var v) = cong var (wkVar-comm i j v)
wkNe-comm i j (f ∙ x) = cong₂ _∙_ (wkNe-comm i j f) (wkTm-comm i j x)
wkTy-comm i j U       = refl
wkTy-comm i j (El x)  = cong El (wkTm-comm i j x)
wkTy-comm i j (A ⇒ B) = cong₂ _⇒_ (wkTy-comm i j A) (wkTy-comm i j B)

--------------------------------------------------------------------------------

data Con : ℕ → Set
data Ty {n}(Γ : Con n) : Ty' n → Set
data Tm {n}(Γ : Con n) : Tm' n → ∃ (Ty Γ) → Set
data Ne {n}(Γ : Con n) : Ne' n → ∃ (Ty Γ) → Set

data Con where
  ε   : Con 0
  _,_ : ∀ {n A'} (Γ : Con n) (A : Ty Γ A') → Con (suc n)

data Ty {n} Γ where
  U   : Ty Γ U
  El  : ∀ {t} → Tm Γ t (, U) → Ty Γ (El t)
  _⇒_ : ∀ {A B} → Ty Γ A → Ty Γ B → Ty Γ (A ⇒ B)

data Tm {n} Γ where
  ne : ∀ {n A} → Ne Γ n A → Tm Γ (ne n) A
  ƛ  : ∀ {A B}{A' : Ty Γ A}{B' : Ty Γ B}{t}{t' : Tm (Γ , A') t ((wkTy (, z≤n) B) , {!!})} → Tm Γ (ƛ A t) (, (A' ⇒ B'))

data Ne {n} Γ where



--------------------------------------------------------------------------------



-- -- Problem: coherence, essentially
-- -- wkTm needs wkTy-comm needs wkTm-comm needs wkTm, ...

-- -- Vars + non-dependent functions
-- --------------------------------------------------------------------------------

-- {-# OPTIONS --no-termination-check #-}

-- module TypedNF where

-- open import Data.Nat
-- open import Relation.Binary.PropositionalEquality

-- infixl 5 _,_
-- infix 3 _∋_
-- infix 4 _⊢_ _⊢n_
-- infixl 8 _∙_
-- infixr 5 _⇒_

-- data Con : ℕ → Set
-- data Ty {n} (Γ : Con n) : Set
-- data _∋_ : ∀{n}(Γ : Con n) → Ty Γ → Set
-- data _⊢_ {n}(Γ : Con n) : Ty Γ → Set
-- data _⊢n_ {n} (Γ : Con n) : Ty Γ → Set

-- data Con where
--   ε   : Con 0
--   _,_ : ∀ {n}(Γ : Con n) (A : Ty Γ) → Con (suc n)

-- strip : ∀{n i} → Con n → i ≤ n → Con (n ∸ i)
-- strip Γ       z≤n     = Γ
-- strip (Γ , _) (s≤s p) = strip Γ p

-- data Ty {n} Γ where
--   U   : Ty Γ
--   El  : (t : Γ ⊢ U) → Ty Γ
--   _⇒_ : (A B : Ty Γ) → Ty Γ

-- insert : ∀{i n}(Γ : Con n) (p : i ≤ n) → Ty (strip Γ p) → Con (suc n)
-- wkTy   : ∀{i n}{Γ : Con n} (p : i ≤ n) (A' : Ty (strip Γ p)) → Ty Γ → Ty (insert Γ p A')
-- wkTm   : ∀{i n}{Γ : Con n} (p : i ≤ n) (A' : Ty (strip Γ p)) {A : Ty Γ} → Γ ⊢ A  → insert Γ p A' ⊢ wkTy p A' A
-- wkVar  : ∀{i n}{Γ : Con n} (p : i ≤ n) (A' : Ty (strip Γ p)) {A : Ty Γ} → Γ ∋ A  → insert Γ p A' ∋ wkTy p A' A
-- wkNe   : ∀{i n}{Γ : Con n} (p : i ≤ n) (A' : Ty (strip Γ p)) {A : Ty Γ} → Γ ⊢n A → insert Γ p A' ⊢n wkTy p A' A

-- insert Γ       z≤n     A' = Γ , A'
-- insert (Γ , A) (s≤s p) A' = insert Γ p A' , wkTy p A' A

-- -- 1. wkTy return type + proof
-- -- 2. try with TERMINATING
-- -- 3. use parameters
-- -- 4. Hoffman syntax and semantics of dependent types

-- -- standard model = presheaf model with 1-elem category


-- data _∋_ where
--   zero : ∀{n Γ}{A : Ty {n} Γ}   → Γ , A ∋ wkTy z≤n A A
--   suc  : ∀{n Γ}{A B : Ty {n} Γ} → Γ ∋ A → Γ , B ∋ wkTy z≤n B A

-- suc-∋ : ∀{n Γ}{A B : Ty {n} Γ} → Γ ∋ A → Γ , B ∋ wkTy z≤n B A
-- suc-∋ = suc

-- zero-∋ : ∀{n Γ}{A : Ty {n} Γ}   → Γ , A ∋ wkTy z≤n A A
-- zero-∋ = zero

-- data _⊢_ {n} Γ where
--   ne  : ∀ {A} → Γ ⊢n A → Γ ⊢ A
--   ƛ   : ∀ {A B} → Γ , A ⊢ wkTy z≤n A B → Γ ⊢ A ⇒ B

-- data _⊢n_ {n} Γ where
--   var : ∀ {A} → Γ ∋ A → Γ ⊢n A
--   _∙_ : ∀ {A B} → Γ ⊢n A ⇒ B → Γ ⊢ A → Γ ⊢n B

-- wkTy p A' U       = U
-- wkTy p A' (El t)  = El (wkTm p A' t)
-- wkTy p A' (A ⇒ B) = wkTy p A' A ⇒ wkTy p A' B

-- wkNe p A' (var v) = var (wkVar p A' v)
-- wkNe p A' (n ∙ t) = wkNe p A' n ∙ wkTm p A' t
-- wkVar             z≤n     A' v       = suc v
-- wkVar {Γ = Γ , A} (s≤s p) A' zero    = {!zero-∋ {Γ = insert Γ p A'}{wkTy p A' A}!}
-- wkVar {Γ = Γ , A} (s≤s p) A' (suc v) = {!suc-∋ {B = wkTy p A' A}(wkVar p A' v)!}

-- wkNe-comm :
--   ∀ {i n}{Γ : Con n} (p : i ≤ n) (A' : Ty (strip Γ p)) A B (x : Γ ⊢n B)
--   → wkNe (s≤s p) A' (wkNe z≤n A x) ≡ {!wkNe p A' x!} -- wkNe z≤n (wkTy p A' A) (wkNe p A' x)

-- wkTm-comm :
--   ∀ {i n}{Γ : Con n} (p : i ≤ n) (A' : Ty (strip Γ p)) A (t : Γ ⊢ U)
--   → wkTm (s≤s p) A' (wkTm z≤n A t) ≡  wkTm z≤n (wkTy p A' A) (wkTm p A' t)  

-- wkTy-comm :
--   ∀ {i n}{Γ : Con n} (p : i ≤ n) (A' : Ty (strip Γ p)) A B 
--   → wkTy (s≤s p) A' (wkTy z≤n A B) ≡ wkTy z≤n (wkTy p A' A) (wkTy p A' B)

-- wkTm p A' (ne n) = ne (wkNe p A' n)
-- wkTm {i}{n}{Γ} p A' (ƛ {A}{B} t)  =
--   ƛ (subst (insert Γ p A' , wkTy p A' A ⊢_) (wkTy-comm p A' A B) (wkTm (s≤s p) A' t))

-- wkNe-comm p A' A n       = {!!}
-- wkTm-comm p A' A (ne x)  = {!!} -- cong ne (wkNe-comm p A' A U x)

-- wkTy-comm p A' A U       = refl
-- wkTy-comm p A' A (El t)  = cong El (wkTm-comm p A' A t)
-- wkTy-comm p A' A (B ⇒ C) = cong₂ _⇒_ (wkTy-comm p A' A B) (wkTy-comm p A' A C)


