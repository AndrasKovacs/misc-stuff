{-# OPTIONS --without-K #-}

open import Relation.Binary.PropositionalEquality

data Con : Set
data Emb : Con → Con → Set
data Sub (Γ : Con) : Con → Set
data Ty (Γ : Con) : Set
data Tm (Γ : Con) : Ty Γ → Set
data Var : ∀ Γ → Ty Γ → Set

data _~ᵗ_ {Γ} : Ty Γ → Ty Γ → Set
data _~ᶜ_ : Con → Con → Set
data _~_ {Γ} : ∀ {A} → Tm Γ A → Tm Γ A → Set
data _~ˢ_ {Γ} : ∀ {Δ} → Sub Γ Δ → Sub Γ Δ → Set

idₑ  : ∀ {Γ}     → Emb Γ Γ
Tyₑ  : ∀ {Γ Δ}   → Emb Γ Δ → Ty Δ → Ty Γ
Varₑ : ∀ {Γ Δ A} → (σ : Emb Γ Δ) → Var Δ A → Var Γ (Tyₑ σ A)
Tmₑ  : ∀ {Γ Δ A} → (σ : Emb Γ Δ) → Tm Δ A  → Tm Γ  (Tyₑ σ A)
idₛ  : ∀ {Γ}     → Sub Γ Γ
Tyₛ  : ∀ {Γ Δ}   → Sub Γ Δ → Ty Δ → Ty Γ
Varₛ : ∀ {Γ Δ A} → (σ : Sub Γ Δ) → Var Δ A → Var Γ (Tyₛ σ A)
Tmₛ  : ∀ {Γ Δ A} → (σ : Sub Γ Δ) → Tm Δ A  → Tm Γ  (Tyₛ σ A)

Tyₛ-id : ∀ {Γ} A → A ≡ Tyₛ {Γ} idₛ A
Tyₛ-id A = {!!}

Tyₛ~ : ∀ {Γ Δ}{σ σ' : Sub Γ Δ} → σ ~ˢ σ' → ∀ A → Tyₛ σ A ~ᵗ Tyₛ σ' A
Tyₛ~ p A = {!!}

≡→~ᵗ : ∀ {Γ}{A A' : Ty Γ} → A ≡ A' → A ~ᵗ A'


data Con where
  ∙   : Con
  _,_ : (Γ : Con) → Ty Γ → Con

data Ty Γ where
  coe : ∀ {Δ} → Δ ~ᶜ Γ → Ty Δ → Ty Γ
  U   : Ty Γ
  Π   : (A : Ty Γ) → Ty (Γ , A) → Ty Γ
  El  : Tm Γ U → Ty Γ

data _~ᶜ_ where
  ~refl : ∀ {Γ} → Γ ~ᶜ Γ
  _~⁻¹  : ∀ {Γ Δ} → Γ ~ᶜ Δ → Δ ~ᶜ Γ
  _~◾_  : ∀ {Γ Δ Σ} → Γ ~ᶜ Δ → Δ ~ᶜ Σ → Γ ~ᶜ Σ
  _,_   : ∀ {Γ A Γ' A'}(p : Γ ~ᶜ Γ') → coe p A ~ᵗ A' → (Γ , A) ~ᶜ (Γ' , A')



data Emb where
  ∙    :                          Emb  ∙             ∙
  keep : ∀ {Γ Δ A}(σ : Emb Γ Δ) → Emb (Γ , Tyₑ σ A) (Δ , A)
  drop : ∀ {Γ Δ A}(σ : Emb Γ Δ) → Emb (Γ , A      )  Δ

data Sub Γ where
  ∙    : Sub Γ ∙
  _,_  : ∀ {Δ A}(σ : Sub Γ Δ) → Tm Γ (Tyₛ σ A) → Sub Γ (Δ , A)

,ₛ : ∀ {Γ Δ} A (σ : Sub Γ Δ) → Tm Γ (Tyₛ σ A) → Sub Γ (Δ , A)
,ₛ A σ t = σ , t

data _~ᵗ_ {Γ} where
  ~refl : ∀ {A} → A ~ᵗ A
  trunc : ∀ {A p} → coe p A ~ᵗ A
  _~⁻¹  : ∀ {A B} → A ~ᵗ B → B ~ᵗ A
  _~◾_  : ∀ {A B C} → A ~ᵗ B → B ~ᵗ C → A ~ᵗ C
  ~El   : ∀ {t t'} → t ~ t' → El t ~ᵗ El t'
  ~Π    : ∀ {A A' : Ty Γ}{B B'}(p : A ~ᵗ A') → coe (~refl , (trunc ~◾ p)) B ~ᵗ B' → Π A B ~ᵗ Π A' B'

≡→~ᵗ refl = ~refl

data Var where
  vz : ∀ {Γ A} →           Var (Γ , A) (Tyₑ (drop idₑ) A)
  vs : ∀ {Γ A} → Var Γ A → Var (Γ , A) (Tyₑ (drop idₑ) A)

data Tm Γ where
  coe : ∀ {Δ A A'} → (p : Δ ~ᶜ Γ) → coe p A' ~ᵗ A → Tm Δ A' → Tm Γ A
  var : ∀ {A}   → Var Γ A → Tm Γ A
  lam : ∀ {A B} → Tm (Γ , A) B → Tm Γ (Π A B)
  app : ∀ {A B} → Tm Γ (Π A B) →(a : Tm Γ A) → Tm Γ (Tyₛ (idₛ , coe ~refl (trunc ~◾ ≡→~ᵗ (Tyₛ-id A)) a) B)

data _~ˢ_ {Γ} where
  ~refl : ∀ {Δ}{σ : Sub Γ Δ} → σ ~ˢ σ
  _~⁻¹  : ∀ {Δ}{σ δ : Sub Γ Δ} → σ ~ˢ δ → δ ~ˢ σ
  _~◾_  : ∀ {Δ}{σ δ ν : Sub Γ Δ} → σ ~ˢ δ → δ ~ˢ ν → σ ~ˢ ν
  _,_   :
    ∀ {Δ A}{σ δ : Sub Γ Δ}{t : Tm Γ (Tyₛ σ A)}{t' : Tm Γ (Tyₛ δ A)}
    (p : σ ~ˢ δ) → coe ~refl (trunc ~◾ Tyₛ~ p A) t ~ t' →  (,ₛ A σ t) ~ˢ (,ₛ A δ t')

idₑ {∙}     = ∙
idₑ {Γ , A} = {!keep (idₑ {Γ})!}
Tyₑ  = {!!}
Varₑ = {!!}
Tmₑ  = {!!}
idₛ  = {!!}
Tyₛ  = {!!}
Varₛ = {!!}
Tmₛ  = {!!}

data _~_ {Γ} where
  ~refl : ∀ {A}{t : Tm Γ A} → t ~ t
  trunc : ∀ {A} p q (t : Tm Γ A) → coe p q t ~ t
  _~⁻¹  : ∀ {A}{t t' : Tm Γ A} → t ~ t' → t' ~ t
  _~◾_  : ∀ {A}{t t' t'' : Tm Γ A} → t ~ t' → t' ~ t'' → t ~ t''

  app   : ∀ {A B}{f f' : Tm Γ (Π A B)}{x x' : Tm Γ A}
    → f ~ f' → (p : x ~ x')
    → app f x ~
      coe ~refl (trunc ~◾ Tyₛ~ {Γ}{Γ , A}
        {idₛ , coe ~refl (trunc ~◾ ≡→~ᵗ (Tyₛ-id A)) x'}
        {idₛ , coe ~refl (trunc ~◾ ≡→~ᵗ (Tyₛ-id A)) x}
        (~refl , {!!}) B) (app f' x')
  lam   : ∀ {A B}{t t' : Tm (Γ , A) B} → t ~ t' → lam t ~ lam t'

  β : ∀ {A B}(t : Tm (Γ , A) B)(a : Tm Γ A) → app (lam t) a ~ Tmₛ (idₛ , coe ~refl (trunc ~◾ ≡→~ᵗ (Tyₛ-id A)) a) t
  η : ∀ {A B}(f : Tm Γ (Π A B)) → f ~ lam (app (Tmₑ (drop idₑ) f) (var vz))


{-



{-# OPTIONS --type-in-type #-}

open import Data.Empty
open import Data.Unit

P = λ A → A → Set

postulate
  peirce : ∀ A B → ((A → B) → A) → A
  peirce' :
    ∀ A (A' : P A) B (B' : P B)
      (f : (A → B) → A)(f' : (g : A → B)(g' : ∀ a → A' a → B' (g a)) → A' (f g))
    → A' (peirce A B f)

bot : ⊥
bot = peirce' ⊤ (λ _ → ⊥) ⊥ (λ _ → ⊥) (λ _ → tt) (λ f _ → f tt)


{-

{-# OPTIONS --type-in-type #-}
-- parametricity inconsistent with classical logic

open import Function

Eq : (A : Set) → A → A → Set
Eq A x y = (P : A → Set) → P x → P y

refl : ∀ {A} x → Eq A x x
refl x P px = px

_⁻¹ : ∀ {A x y} → Eq A x y → Eq A y x
p ⁻¹ = λ P → p (λ z → P z → P _) (λ x → x)

_◾_ : ∀ {A x y z} → Eq A x y → Eq A y z → Eq A x z
p ◾ q = λ P z → q P (p P z)

_&_ : ∀ {A B x y}(f : A → B) → Eq A x y → Eq B (f x) (f y)
f & p = λ P → p (λ z → P (f z))

infixr 5 _◾_
infixl 6 _⁻¹
infixl 4 _&_

------------------------------------------------------------

record Nat : Set where
  constructor con
  field
    C : Set
    z : C
    s : C → C
open Nat

record Nat⇒ (N N' : Nat) : Set where
  constructor con
  open Nat
  field
    rec  : C N → C N'
    recz : Eq _ (rec (z N)) (z N')
    recs : ∀ n → Eq _ (rec (s N n)) (s N' (rec n))
open Nat⇒

data ⊥ : Set where

record ⊤ : Set where
  constructor tt

Nat∘ : ∀ {N N' N'' : Nat} → Nat⇒ N' N'' → Nat⇒ N N' → Nat⇒ N N''
Nat∘ (con rec recz recs) (con rec' recz' recs') =
  con (rec ∘ rec') ((rec & recz') ◾ recz) (λ n → (rec & recs' n) ◾ (recs (rec' n)))

Nat-id : (N : Nat) → Nat⇒ N N
Nat-id (con C z s) = con id (refl z) (λ n → refl (s n))

record Initial (N : Nat) : Set where
  constructor con
  field
    init : (N' : Nat) → Nat⇒ N N'
    univ : (N' : Nat) → (f : Nat⇒ N N') → Eq _ f (init N')
open Initial

init-id : (N : Nat)(iN : Initial N)(f : Nat⇒ N N) → Eq _ f (Nat-id N)
init-id N i f = univ i N f ◾ univ i N (Nat-id N) ⁻¹

-- rec-id : {N : Nat}{f : Nat⇒ N N} → Eq _ f (Nat-id N) → Eq _ (rec f) id
-- rec-id p = rec & p

-- open import Data.Product

-- init-ind :
--   (ℕ : Nat)(i : Initial ℕ)(P : C ℕ → Set) → (∀ n → P n → P (s ℕ n)) → P (z ℕ) → ∀ n → P n
-- init-ind ℕ i P ps pz n =
--   subst P (cong (_$ n) (rec-id _ (init-id ℕ i fromTo))) (proj₂ (rec to n))
--   where
--     ℕP : Nat
--     ℕP = con (∃ P) (z ℕ , pz) (λ {(n , pn) → (s ℕ n , ps n pn)})

--     to : Nat⇒ ℕ ℕP
--     to = init i ℕP

--     from : Nat⇒ ℕP ℕ
--     from = con proj₁ refl (λ n → refl)

--     fromTo : Nat⇒ ℕ ℕ
--     fromTo = Nat∘ from to

------------------------------------------------------------

CNat = ∀ N → (N → N) → N → N

cz : CNat
cz N s z = z

cs : CNat → CNat
cs n N s z = s (n _ s z)

postulate
  CNat' :
    ∀ N           (N' : N → Set)
      (s : N → N) (s' : (n : N) → N' n → N' (s n))
      z           (z' : N' z)
      (n : CNat)
    → N' (n N s z)

cnat : Nat
cnat = con CNat cz cs

open import Data.Product

init-cnat : Initial cnat
init-cnat =
  con
    (λ {(con N z s) → con (λ n → n N s z) (refl z) (λ n → refl (s (n N s z)))})
    (λ {(con N z s) f P pf → {!!}} )


open import Relation.Binary.PropositionalEquality

-- foo : ∀ N (s : N → N) z (n : CNat) → n N s z ≡ n CNat cs cz N s z
-- foo N s z n = {!CNat' N!}

-- foo : (n : CNat) → Eq CNat n (n CNat cs cz)
-- foo n P pn = CNat' CNat P cs {!!} cz {!!} n

-- CNat-ind : (P : CNat → Set)(cs' : ∀ n → P n → P (cs n)) → P cz → (n : CNat) → P n
-- CNat-ind P cs' cz' n = {!CNat' CNat P cs cs' cz cz' n!}

CNat-ind : (P : CNat → Set)(cs' : ∀ n → P n → P (cs n)) → P cz → (n : CNat) → P n
CNat-ind P cs' cz' n = {!CNat' CNat P cs cs' cz cz' n!}


Id = ∀ A → A → A

postulate Id' : ∀ (f : Id) A (A' : A → Set) a → A' a → A' (f A a)

postulate
  ext : ∀ {a b} → Extensionality a b


idid : ∀ (f : Id) → f ≡ (λ A x → x)
idid f = {!Id' f Id (_≡ (λ A x → x)) f!}
  -- ext λ A → ext λ a → Id' f A (_≡ a) a _≡_.refl


Sum = λ A B → ∀ S → (A → S) → (B → S) → S

postulate
  Sum' :
    ∀ A B (s : Sum A B) → ∀ S (S' : S → Set) l (l' : ∀ a → S' (l a)) r (r' : ∀ b → S' (r b))
    → S' (s S l r)

inj₁ : ∀ A B → A → Sum A B
inj₁ A B a _ l r = l a

inj₂ : ∀ A B → B → Sum A B
inj₂ A B b _ l r = r b

import Data.Sum as S

-- sum-unique : ∀ A B (s : Sum A B) → (∃ λ a → inj₁ _ _ a ≡ s) S.⊎ (∃ λ b → inj₂ _ _ b ≡ s)
-- sum-unique A B s = {!!}



-- postulate
--   peirce  : ∀ (A B : Set) → ((A → B) → A) → B
--   peirce' :
--     ∀ A (A' : A → Set)
--       B (B' : B → Set)
--       (f : (A → B) → A)(f' : (g : A → B)(g' : ∀ a (a' : A' a) → B' (g a)) → A' (f g))
--     → B' (peirce A B f)


-- bot : ⊥
-- bot = {!!}





-}



-}
