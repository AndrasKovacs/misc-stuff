-- Vars + non-dependent functions
--------------------------------------------------------------------------------

open import Data.Nat
open import Relation.Binary.PropositionalEquality

infixl 5 _,_
infix 3 _∋_
infix 4 _⊢_ _⊢ₙ_
-- infixl 8 _∙_
infixr 5 _⇒_

data Con : ℕ → Set
data Ty {n} (Γ : Con n) : Set
data _∋_ : ∀{n}(Γ : Con n) → Ty Γ → Set
data _⊢_ {n}(Γ : Con n) : Ty Γ → Set
data _⊢ₙ_ {n} (Γ : Con n) : Ty Γ → Set

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
wkNe   : ∀{i n}{Γ : Con n} (p : i ≤ n) (A' : Ty (strip Γ p)) {A : Ty Γ} → Γ ⊢ₙ A → insert Γ p A' ⊢ₙ wkTy p A' A

insert Γ       z≤n     A' = Γ , A'
insert (Γ , A) (s≤s p) A' = insert Γ p A' , wkTy p A' A

wkTy p A' U       = U
wkTy p A' (El t)  = El (wkTm p A' t)
wkTy p A' (A ⇒ B) = wkTy p A' A ⇒ wkTy p A' B

data _∋_ where
  zero : ∀{n Γ}{A : Ty {n} Γ}   → Γ , A ∋ wkTy z≤n A A
  suc  : ∀{n Γ}{A B : Ty {n} Γ} → Γ ∋ A → Γ , B ∋ wkTy z≤n B A

suc-∋ : ∀{n Γ}{A B : Ty {n} Γ} → Γ ∋ A → Γ , B ∋ wkTy z≤n B A
suc-∋ = suc

zero-∋ : ∀{n Γ}{A : Ty {n} Γ}   → Γ , A ∋ wkTy z≤n A A
zero-∋ = zero

-- TODO : prove commutativity of weakening

-- wkTy z≤n (wkTy p A' A) (wkTy p A' A)  == wkTy (s≤s p) A' (wkTy z≤n A A)
-- wkTy z≤n (wkTy p A' A) (wkTy p A' .A) == wkTy (s≤s p) A' (wkTy z≤n A .A)
-- wkTy (s≤s p) A' (wkTy z≤n A B)        == wkTy z≤n (wkTy p A' A) (wkTy p A' B)

insert-comm :
  ∀ {n i i'}{Γ : Con n}{p p' A A'}
  → insert {i'} (insert {i} Γ p A) p' A' ≡ {!insert {i'}!}
insert-comm = {!!}


wkVar             z≤n     A' v       = suc v
wkVar {Γ = Γ , A} (s≤s p) A' zero    = {!zero-∋ {Γ = insert Γ p A'}{wkTy p A' A}!}
wkVar {Γ = Γ , A} (s≤s p) A' (suc v) = {!suc-∋ {B = wkTy p A' A}(wkVar p A' v)!}

data _⊢_ {n} Γ where
  ne  : ∀ {A} → Γ ⊢ₙ A → Γ ⊢ A
  ƛ   : ∀ {A B} → Γ , A ⊢ wkTy z≤n A B → Γ ⊢ A ⇒ B

wkTm p A' (ne n) = ne (wkNe p A' n)
wkTm {n}{i}{Γ} p A' (ƛ {A}{B} t)  = ƛ {!wkTm (s≤s p) A' t!}

data _⊢ₙ_ {n} Γ where
  var : ∀ {A} → Γ ∋ A → Γ ⊢ₙ A
  _∙_ : ∀ {A B} → Γ ⊢ₙ A ⇒ B → Γ ⊢ A → Γ ⊢ₙ B

wkNe p A' (var v) = var (wkVar p A' v)
wkNe p A' (n ∙ t) = wkNe p A' n ∙ wkTm p A' t


-- -- Vars + non-dependent functions
-- --------------------------------------------------------------------------------

-- open import Data.Nat 


-- infixl 5 _,_
-- infix 3 _∋_
-- infix 4 _⊢_ _⊢ₙ_
-- -- infixl 8 _∙_
-- infixr 5 _⇒_

-- data Con : ℕ → Set
-- data Ty {n} (Γ : Con n) : Set
-- data _∋_ : ∀{n}(Γ : Con n) → Ty Γ → Set
-- data _⊢_ {n}(Γ : Con n) : Ty Γ → Set
-- data _⊢ₙ_ {n} (Γ : Con n) : Ty Γ → Set

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

-- insert : ∀{n i}(Γ : Con n) (p : i ≤ n) → Ty (strip Γ p) → Con (suc n)
-- wkTy   : ∀{n i}{Γ : Con n} (p : i ≤ n) (A' : Ty (strip Γ p)) → Ty Γ → Ty (insert Γ p A')
-- wkTm   : ∀{n i}{Γ : Con n} (p : i ≤ n) (A' : Ty (strip Γ p)) {A : Ty Γ} → Γ ⊢ A  → insert Γ p A' ⊢ wkTy p A' A
-- wkVar  : ∀{n i}{Γ : Con n} (p : i ≤ n) (A' : Ty (strip Γ p)) {A : Ty Γ} → Γ ∋ A  → insert Γ p A' ∋ wkTy p A' A
-- wkNe   : ∀{n i}{Γ : Con n} (p : i ≤ n) (A' : Ty (strip Γ p)) {A : Ty Γ} → Γ ⊢ₙ A → insert Γ p A' ⊢ₙ wkTy p A' A

-- insert Γ       z≤n     A' = Γ , A'
-- insert (Γ , A) (s≤s p) A' = insert Γ p A' , wkTy p A' A

-- wkTy p A' U       = U
-- wkTy p A' (El t)  = El (wkTm p A' t)
-- wkTy p A' (A ⇒ B) = wkTy p A' A ⇒ wkTy p A' B

-- data _∋_ where
--   zero : ∀{n Γ}{A : Ty {n} Γ}   → Γ , A ∋ wkTy z≤n A A
--   suc  : ∀{n Γ}{A B : Ty {n} Γ} → Γ ∋ A → Γ , B ∋ wkTy z≤n B A

-- wkVar z≤n     A' zero    = suc zero
-- wkVar (s≤s p) A' zero    = {!!}
-- wkVar z≤n     A' (suc v) = {!!}
-- wkVar (s≤s p) A' (suc v) = {!!}

-- data _⊢_ {n} Γ where
--   ne  : ∀ {A} → Γ ⊢ₙ A → Γ ⊢ A
--   ƛ   : ∀ {A B} → Γ , A ⊢ wkTy z≤n A B → Γ ⊢ A ⇒ B

-- wkTm p A' (ne n) = ne (wkNe p A' n)
-- wkTm p A' (ƛ t)  = ƛ {!!}

-- data _⊢ₙ_ {n} Γ where
--   var : ∀ {A} → Γ ∋ A → Γ ⊢ₙ A
--   _∙_ : ∀ {A B} → Γ ⊢ₙ A ⇒ B → Γ ⊢ A → Γ ⊢ₙ B

-- wkNe p A' (var v) = {!!}
-- wkNe p A' (n ∙ t) = wkNe p A' n ∙ wkTm p A' t



--------------------------------------------------------------------------------
-- infixl 5 _,_
-- infix 3 _∋_
-- infix 4 _⊢_ _⊢ₙ_
-- infixl 8 _∙_
-- infixr 5 _⇒_

-- data Con : Set
-- data Ty Γ : Set
-- data _∋_ : (Γ : Con) → Ty Γ → Set
-- data _⊢_ (Γ : Con) : Ty Γ → Set
-- data _⊢ₙ_ (Γ : Con) : Ty Γ → Set

-- data Con where
--   ε   : Con
--   _,_ : (Γ : Con) (A : Ty Γ) → Con

-- data Ty Γ where
--   U   : Ty Γ
--   El  : (t : Γ ⊢ U) → Ty Γ
--   _⇒_ : (A B : Ty Γ) → Ty Γ

-- wkTy : ∀ {Γ B} → Ty Γ → Ty (Γ , B)
-- wkTm : ∀ {Γ A B} → Γ ⊢ A → (Γ , B) ⊢ wkTy A
-- wkNe : ∀ {Γ A B} → Γ ⊢ₙ A → (Γ , B) ⊢ₙ wkTy A

-- data _∋_ where
--   zero : ∀{Γ}{A : Ty Γ}   → Γ , A ∋ wkTy A
--   suc  : ∀{Γ}{A B : Ty Γ} → Γ ∋ A → Γ , B ∋ wkTy A

-- data _⊢_ Γ where
--   ne  : ∀ {A} → Γ ⊢ₙ A → Γ ⊢ A
--   ƛ   : ∀ {A B} → Γ , A ⊢ wkTy B → Γ ⊢ A ⇒ B

-- data _⊢ₙ_ Γ where
--   var : ∀ {A} → Γ ∋ A → Γ ⊢ₙ A
--   _∙_ : ∀ {A B} → Γ ⊢ₙ A ⇒ B → Γ ⊢ A → Γ ⊢ₙ B

-- wkTy U       = U
-- wkTy (El t)  = El (wkTm t)
-- wkTy (A ⇒ B) = wkTy A ⇒ wkTy B
-- wkTm (ne n)  = ne (wkNe n)
-- wkTm {Γ}{A ⇒ B}{B'}(ƛ t)   = ƛ {!wkTm {Γ , A}{wkTy B}{wkTy B'} t!}
-- wkNe (var v) = var (suc v)
-- wkNe (n ∙ t) = wkNe n ∙ wkTm t 


-- some weakening operation that inserts into Con
-- !! and 




-- -- Vars + non-dependent functions
-- --------------------------------------------------------------------------------

-- infixl 5 _,_
-- infix 3 _∋_
-- infix 4 _⊢_ _⊢ₙ_
-- -- infixl 8 _∙_
-- infixr 5 _⇒_

-- data Con : Set
-- data Ty Γ : Set
-- data _∋_ : (Γ : Con) → Ty Γ → Set
-- data _⊢_ (Γ : Con) : Ty Γ → Set
-- data _⊢ₙ_ (Γ : Con) : Ty Γ → Set

-- data Con where
--   ε   : Con
--   _,_ : (Γ : Con) (A : Ty Γ) → Con

-- data Ty Γ where
--   U   : Ty Γ
--   El  : (t : Γ ⊢ U) → Ty Γ
--   _⇒_ : (A B : Ty Γ) → Ty Γ

-- _-_ : ∀ Γ {A} → Γ ∋ A → Con
-- wkTy₁ : ∀ {Γ B} → Ty Γ → Ty (Γ , B)

-- -- wkTm : ∀ {Γ A B} → Γ ⊢ A → (Γ , B) ⊢ wkTy A
-- -- wkNe : ∀ {Γ A B} → Γ ⊢ₙ A → (Γ , B) ⊢ₙ wkTy A

-- data _∋_ where
--   zero : ∀{Γ}{A : Ty Γ}   → Γ , A ∋ wkTy₁ A
--   suc  : ∀{Γ}{A B : Ty Γ} → Γ ∋ A → Γ , B ∋ wkTy₁ A

-- wkTy : ∀ {Γ 

-- (Γ , A) - zero  = Γ
-- (Γ , A) - suc v = (Γ - v) , {!!}
-- wkTy₁ {Γ}{B} A  = {!!}

-- data _⊢_ Γ where
--   -- ne  : ∀ {A} → Γ ⊢ₙ A → Γ ⊢ A
--   -- ƛ   : ∀ {A B} → Γ , A ⊢ wkTy B → Γ ⊢ A ⇒ B

-- data _⊢ₙ_ Γ where
--   -- var : ∀ {A} → Γ ∋ A → Γ ⊢ₙ A
--   -- _∙_ : ∀ {A B} → Γ ⊢ₙ A ⇒ B → Γ ⊢ A → Γ ⊢ₙ B

-- -- wkTy U       = U
-- -- wkTy (El t)  = El (wkTm t)
-- -- wkTy (A ⇒ B) = wkTy A ⇒ wkTy B
-- -- wkTm (ne n)  = ne (wkNe n)
-- -- wkTm {Γ}{A ⇒ B}{B'}(ƛ t)   = ƛ {!wkTm {Γ , A}{wkTy B}{wkTy B'} t!}
-- -- wkNe (var v) = var (suc v)
-- -- wkNe (n ∙ t) = wkNe n ∙ wkTm t







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




