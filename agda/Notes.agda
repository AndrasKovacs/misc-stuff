{-# OPTIONS --without-K #-}


open import Relation.Binary.PropositionalEquality
open import Data.Product renaming (proj₁ to ₁; proj₂ to ₂)
open import Agda.Primitive hiding (_⊔_)
open import Function

_◾_ = trans; infixr 4 _◾_
_⁻¹ = sym; infix 6 _⁻¹
ap = cong

-- data Tm (Γ : Con) : Ty → Set where
--   var : ∀ {A} → Var Γ A → Tm Γ A
--   app : ∀ {B} → Tm Γ (ι⇒ B) → Tm Γ ι → Tm Γ B


module SigCons where

  data Tree : Set where
    leaf : Tree
    node : Tree → Tree → Tree

  ⊤ : Set
  ⊤ = leaf ≡ leaf

  pattern tt = refl

  ⊤η : (p : ⊤) → p ≡ tt
  ⊤η tt = refl

  ⊥ : Set
  ⊥ = leaf ≡ node leaf leaf

  ⊥-elim : ∀{i}{A : Set i} → ⊥ → A
  ⊥-elim {A} ()

  choose : Tree → Set
  choose leaf             = ⊤
  choose (node leaf leaf) = ⊤
  choose _                = ⊥

  Bool : Set
  Bool = Σ Tree choose

  pattern true  = leaf , tt
  pattern false = node leaf leaf , tt

  Bool-elim : ∀{i}(P : Bool → Set i) → P true → P false → ∀ b → P b
  Bool-elim P pt pf true  = pt
  Bool-elim P pt pf false = pf

  infixr 4 _⊎_
  _⊎_ : Set → Set → Set
  A ⊎ B = Σ Bool (Bool-elim (λ _ → Set) A B)

  pattern inj₁ a = true  , a
  pattern inj₂ b = false , b

  ⊎-Elim : ∀ {i A B}(P : A ⊎ B → Set i) → (∀ a → P (inj₁ a)) → (∀ b → P (inj₂ b))
           → ∀ ab → P ab
  ⊎-Elim P f g (inj₁ a) = f a
  ⊎-Elim P f g (inj₂ b) = g b

  isℕ : Tree → Set
  isℕ leaf                = ⊤
  isℕ (node leaf u)       = isℕ u
  isℕ (node (node _ _) u) = ⊥

  ℕ : Set
  ℕ = ∃ isℕ

  zero : ℕ
  zero = leaf , tt

  suc : ℕ → ℕ
  suc (t , p) = node leaf t , p

  ℕ-elim : ∀ {i}(P : ℕ → Set i) → P zero → (∀ {n} → P n → P (suc n)) → ∀ n → P n
  ℕ-elim P z s (leaf        , tt) = z
  ℕ-elim P z s (node leaf r , p)  = s (ℕ-elim P z s (r , p))

  Ty = ℕ

  Con : ℕ → Set
  Con = ℕ-elim _ ⊤ (λ V → V × Ty)

  Var : ∀ n → Con n → Ty → Set
  Var = ℕ-elim
    (λ n → Con n → Ty → Set) (λ _ _ → ⊥)
    (λ {n} V Γ A → (A ≡ ₂ Γ) ⊎ V (₁ Γ) A)

  vz : ∀ n {Γ A} → Var (suc n) (Γ , A) A
  vz n = inj₁ refl

  vs : ∀ n {Γ A B} → Var n Γ A → Var (suc n) (Γ , B) A
  vs n v = inj₂ v

  -- data Tm n (Γ : Con n) : Ty → Set
  -- data Sp n (Γ : Con n) : Ty → Ty → Set

  -- data Sp n Γ where
  --   []  : ∀ {A} → Sp n Γ A A
  --   _∷_ : ∀ {A B} → Tm n Γ zero → Sp n Γ A B → Sp n Γ (suc A) B

  -- data Tm n Γ where
  --   ne : ∀ {A} → Var n Γ A → Sp n Γ A zero → Tm n Γ zero

  isSp : Tree → ∀ n (Γ : Con n) → Ty → Ty → Set
  isTm : Tree → ∀ n (Γ : Con n) → Ty → Set
  isSp leaf        n Γ A  B = A ≡ B
  isSp (node t sp) n Γ sB C = ∃ λ B → isTm t n Γ zero × isSp sp n Γ B C × sB ≡ suc B
  isTm t n Γ Z = ∃ λ A → Var n Γ A × isSp t n Γ A zero × Z ≡ zero

  Sp : ∀ n (Γ : Con n) → Ty → Ty → Set
  Sp n Γ A B = ∃ λ sp → isSp sp n Γ A B

  Tm : ∀ n (Γ : Con n) → Ty → Set
  Tm n Γ A = ∃ λ t → isTm t n Γ A

  [] : ∀ {n Γ A} → Sp n Γ A A
  [] = leaf , refl

  infixr 5 _∷_
  _∷_ : ∀ {n Γ A B} → Tm n Γ zero → Sp n Γ A B → Sp n Γ (suc A) B
  _∷_ (t , p) (sp , q) = node t sp , _ , p , q , refl

  ne : ∀ {n Γ A} → Var n Γ A → Sp n Γ A zero → Tm n Γ zero
  ne v (sp , p) = sp , _ , v , p , refl

  -- example: construction of Natural numbers from Tm
  n₀ = zero
  n₁ = suc zero
  n₂ = suc (suc zero)

  NatSig : Con n₂
  NatSig = (tt , zero) , suc zero

  Nat : Set
  Nat = Tm n₂ NatSig zero

  Zero : Nat
  Zero = ne (inj₂ (inj₁ refl)) []

  Suc : Nat → Nat
  Suc n = ne (inj₁ refl) (n ∷ [])

  NatElim : ∀ {i}(P : Nat → Set i) → P Zero → (∀ n → P n → P (Suc n)) → ∀ n → P n
  NatElim P z s (sp , _ , ((fst , snd₁) , snd) , p , tt) = {!!}
  -- NatElim P z s (leaf     , _ , inj₂ (inj₁ tt) , tt , tt) = z
  -- NatElim P z s (node t leaf , _ , inj₁ tt , ((.leaf , .tt) , q , tt , tt) , tt) =
  --   s (t , q) (NatElim P z s (t , q))
  -- NatElim P z s (sp , _ , inj₂ (inj₂ ()) , p , tt)

  -- NatElim P z s (leaf , _ , inj₂ (inj₁ tt) , tt , tt) = z



module BinTreeCons where

  open import Data.Nat hiding (_<_)
  open import Data.Sum
  open import Data.Unit
  open import Data.Empty

  data Tree : ℕ → Set
  data Tree↓ : ℕ → Set

  data Tree where
    leaf   : Tree zero
    nodeL  : ∀ {n} → Tree  n → Tree↓ n → Tree (suc n)
    nodeR  : ∀ {n} → Tree↓ n → Tree  n → Tree (suc n)
    nodeLR : ∀ {n} → Tree  n → Tree  n → Tree (suc n)

  data Tree↓ where
    here  : ∀ {n} → Tree  n → Tree↓ (suc n)
    there : ∀ {n} → Tree↓ n → Tree↓ (suc n)

  pattern injᵃ x = inj₁ x
  pattern injᵇ x = inj₂ (inj₁ x)
  pattern injᶜ x = inj₂ (inj₂ x)

  t1 : Tree 1
  t1 = nodeLR leaf leaf

  t2 : Tree 2
  t2 = nodeL t1 (here leaf)

  t3 : Tree 3
  t3 = nodeL t2 (there (here leaf))

  BTree = ∃ Tree

  infix 3 _<_
  data _<_ : ℕ → ℕ → Set where
    here  : ∀ {n} → n < suc n
    there : ∀ {n m} → n < m → n < suc m

  <-trs : ∀ {n m k} → n < m → m < k → n < k
  <-trs p here      = there p
  <-trs p (there q) = there (<-trs p q)

  s< : ∀ {n m} → suc n < m → n < m
  s< here = there here
  s< (there p) = there (s< p)

  0<s : ∀ n → 0 < suc n
  0<s zero    = here
  0<s (suc n) = there (0<s n)

  s<s : ∀ {n m} → n < m → suc n < suc m
  s<s here      = here
  s<s (there p) = there (s<s p)

  foo : ∀ {n m} → suc n < suc m → n < m
  foo here = here
  foo {m = suc m} (there p) = there (foo p)

  <-irrefl : ∀ {n} → n < n → ⊥
  <-irrefl {suc n} p = <-irrefl {n} (foo p)

  postulate
    ℕ-set : ∀ {n : ℕ}(p : n ≡ n) → p ≡ refl

  lem : ∀ {n m}(e : n ≡ m) → (p : n < suc m) → p ≡ subst (λ x → n < suc x) e (_<_.here {n})
  lem e here      rewrite ℕ-set e = refl
  lem refl (there p) = ⊥-elim (<-irrefl p)

  <-irr : ∀ {n m}(p q : n < m) → p ≡ q
  <-irr p here = lem refl p
  <-irr here (there q) = ⊥-elim (<-irrefl q)
  <-irr (there p) (there q) = ap there (<-irr p q)

  cmp : ∀ n m → (n < m) ⊎ (m < n) ⊎ (n ≡ m)
  cmp zero zero = inj₂ (inj₂ refl)
  cmp zero (suc m) = inj₁ (0<s m)
  cmp (suc n) zero = inj₂ (inj₁ (0<s n))
  cmp (suc n) (suc m) with cmp n m
  ... | inj₁ p        = inj₁ (s<s p)
  ... | inj₂ (inj₁ p) = inj₂ (inj₁ (s<s p))
  ... | inj₂ (inj₂ p) = inj₂ (inj₂ (cong suc p))

  cmp-refl : ∀ n → cmp n n ≡ injᶜ refl
  cmp-refl zero    = refl
  cmp-refl (suc n) rewrite cmp-refl n = refl

  tree↓ : ∀ {n} → (∃ λ m → m < n × Tree m) → Tree↓ n
  tree↓ (_ , here    , t) = here t
  tree↓ (_ , there p , t) = there (tree↓ (_ , p , t))

  tree↑ : ∀ {n} → Tree↓ n → (∃ λ m → m < n × Tree m)
  tree↑ (here t)  = _ , here , t
  tree↑ (there t) = ₁ (tree↑ t) , there (₁ (₂ (tree↑ t))) , ₂ (₂ (tree↑ t))

  tree↑↓ : ∀ {n} t → tree↓ (tree↑ {n} t) ≡ t
  tree↑↓ (here _) = refl
  tree↑↓ (there t) rewrite tree↑↓ t = refl

  tree↓↑ : ∀ {n} x → tree↑ (tree↓ {n} x) ≡ x
  tree↓↑ (_ , here    , t) = refl
  tree↓↑ (_ , there p , t) rewrite tree↓↑ (_ , p , t) = refl

  leaf' : BTree
  leaf' = 0 , leaf

  node : BTree → BTree → BTree
  node (n , l) (m , r) with cmp n m
  ... | injᵃ p    = suc m , nodeR (tree↓ (_ , p , l)) r
  ... | injᵇ p    = suc n , nodeL l (tree↓ (_ , p , r))
  ... | injᶜ refl = suc n , nodeLR l r

  BTreeElim : ∀ {i}(P : BTree → Set i) → P leaf' → (∀ {l r} → P l → P r → P (node l r))
               → ∀ t → P t
  BTree↓Elim : ∀ {i}(P : BTree → Set i) → P leaf' → (∀ {l r} → P l → P r → P (node l r))
               → ∀ {n}(t : Tree↓ n) → P (_ , tree↑ t .₂ .₂)
  BTreeElim P pl pn (_ , leaf)       = pl
  BTreeElim P pl pn (_ , nodeL {n} l r)
    with cmp n (₁ (tree↑ r)) | pn (BTreeElim P pl pn (_ , l)) (BTree↓Elim P pl pn r)
  ... | injᵃ p | hyp = ⊥-elim (<-irrefl (<-trs (tree↑ r .₂ .₁) p))
  ... | injᵇ p | hyp = subst (λ x → P (suc n , nodeL l x))
                             (  ap (λ x → tree↓ (₁ (tree↑ r) , x , tree↑ r .₂ .₂)) (<-irr _ _)
                              ◾ tree↑↓ r) hyp
  ... | injᶜ p | hyp = ⊥-elim (<-irrefl (subst ( tree↑ r .₁ <_) p (tree↑ r .₂ .₁)))
  BTreeElim P pl pn (_ , nodeR {n} l r)
    with cmp (₁ (tree↑ l)) n | pn (BTree↓Elim P pl pn l) (BTreeElim P pl pn (_ , r))
  ... | injᵃ p | hyp = subst (λ x → P (suc n , nodeR x r))
                             (   ap (λ x → tree↓ (₁ (tree↑ l) , x , tree↑ l .₂ .₂)) (<-irr _ _)
                               ◾ tree↑↓ l)
                             hyp
  ... | injᵇ p | hyp = ⊥-elim (<-irrefl (<-trs p (tree↑ l .₂ .₁)))
  ... | injᶜ p | hyp = ⊥-elim (<-irrefl (subst (_< n) p (tree↑ l .₂ .₁)))
  BTreeElim P pl pn (_ , nodeLR {n} l r) with
    cmp n n | cmp-refl n | pn (BTreeElim P pl pn (_ , l)) (BTreeElim P pl pn (_ , r))
  ... | _ | refl | hyp = hyp
  BTree↓Elim P pl pn (here  t) = BTreeElim P pl pn (_ , t)
  BTree↓Elim P pl pn (there t) = BTree↓Elim P pl pn t


  leafβ : ∀ {i P pl}{pn : ∀ {l r} → P l → P r → P (node l r)}
          → BTreeElim {i} P pl pn leaf' ≡ pl
  leafβ = refl

  -- need eliminators to prove, but obvious
  nodeβ : ∀ {i P pl}{pn : ∀ {l r} → P l → P r → P (node l r)}{l r}
          → BTreeElim {i} P pl pn (node l r)
          ≡ pn (BTreeElim P pl pn l) (BTreeElim P pl pn r)
  nodeβ {i} {P} {pl} {pn} {n , l} {m , r}
    with cmp n m | pn (BTreeElim P pl pn (n , l)) (BTreeElim P pl pn (m , r))
  nodeβ | injᵃ p    | bar = {!!}
  nodeβ | injᵇ p    | bar = {!!}
  nodeβ | injᶜ refl | bar = {!!}
