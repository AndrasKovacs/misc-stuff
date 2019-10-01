{-# OPTIONS --without-K #-}

{-
Claim: finitary inductive types are constructible from Π,Σ,Uᵢ,_≡_ and ℕ, without
quotiens. Sketch in two parts.

1. First, sketch construction of finitary inductive types from Π, Σ, Uᵢ, _≡_ and binary trees.
   Here I only show this for really simple, single-sorted closed inductive types,
   but it should work for indexed inductive types as well.

   The method is the following: we inductively define signatures as typing contexts,
   and a type for constructor terms. Then for every signature we can construct an
   initial (term) model. This is a minimal simply-typed version of "Constructing
   Quotient Inductive-Inductive Types".

   Every type which we use here can be straightforwardly constructed from binary trees,
   using recursively defined annotations and well-formedness predicates. E.g. natural
   numbers are linear trees, and constructors terms are given with a typing predicate
   on trees.

   In this file I only get constructor terms from trees, and I import other
   types. I do this because when everything is given with trees, I get confusing
   pattern coverage checking behavior from Agda and lots of coding noise.

2. Binary trees are constructible from Π, Σ, Uᵢ, _≡_, and ℕ, with weak computation rules.

   Related:
     This paper gives a construction of finitary inductive types from natural
     numbers and set quotients, which they derive from function and prop extensionality.

       https://arxiv.org/abs/1612.00693

   But it turns out we don't need quotients! In section 1 we sketched constructing
   finitary inductive types from binary tress, so here we set out to construct
   binary trees from natural numbers.

   The classical approach (also used in the above paper) to get binary trees, is
   to take the fixpoint of the functor F = λ A → ⊤ ⊎ (A × A), defined as the
   quotient (Σ ℕ λ n → Fⁿ ⊥)/R, where R relates representations of the same tree
   at different n-levels of Fⁿ⊥ approximation.

   We can ditch quotients if every tree is uniquely represented. So, we define
   mutually Tree' : ℕ → Set and Tree'↓ : ℕ → Set, where Tree' n is the set of
   trees with height n, and Tree'↓ n is the set of trees with height less than n.
   I don't think the definition is particularly deep, it just works out.


If we combine this with previous results:

  Page 63 of:
  https://eutypes.cs.ru.nl/eutypes_pmwiki/uploads/Main/books-of-abstracts-TYPES2019.pdf

and some goodwill, we get that:

  Any finitary inductive type (large, indexed, inductive-inductive, you name it)
  can be reduced in *extensional type theory* to Π,Σ,Uᵢ,ℕ,_≡_.

We need the extensional part because reductions of ind-ind types only work
so far with UIP and funext.

-}

-- Library
--------------------------------------------------------------------------------

open import Agda.Primitive hiding (_⊔_)
open import Data.Empty
open import Data.Nat hiding (_<_)
open import Data.Product renaming (proj₁ to ₁; proj₂ to ₂)
open import Data.Sum
open import Data.Unit
open import Function
open import Relation.Binary.PropositionalEquality

_◾_ = trans; infixr 4 _◾_
_⁻¹ = sym; infix 6 _⁻¹
ap  = cong
tr  = subst

J : ∀ {α β}{A : Set α} {x : A}
      (P : {y : A} → x ≡ y → Set β) → P refl → ∀ {y}(p : x ≡ y) → P p
J P pr refl = pr

hedberg :
  ∀ {α}{A : Set α}
  → ((x y : A) → (x ≡ y) ⊎ (x ≢ y))
  → ∀ {x y : A}(p q : x ≡ y) → p ≡ q
hedberg {_}{A} eq? {x}{y} p q =
  f-inv p ⁻¹ ◾ ap (_◾ f refl ⁻¹) (f-const p q) ◾ f-inv q
  where
    f : {x y : A} → x ≡ y → x ≡ y
    f {x}{y} p with eq? x y
    ... | inj₁ eq   = eq
    ... | inj₂ ¬eq  = ⊥-elim (¬eq p)

    f-const : ∀ {x y} p q → f {x}{y} p ≡ f q
    f-const {x}{y} p q  with eq? x y
    ... | inj₁ eq  = refl
    ... | inj₂ ¬eq = ⊥-elim (¬eq q)

    f-inv : ∀ {x y} p → (f {x}{y} p ◾ f refl ⁻¹) ≡ p
    f-inv refl = J (λ p → (p ◾ p ⁻¹) ≡ refl) refl (f refl)

data ABC (A B C : Set) : Set where
  inᵃ : A → ABC A B C
  inᵇ : B → ABC A B C
  inᶜ : C → ABC A B C

infix 3 _<_
data _<_ : ℕ → ℕ → Set where  -- also definable by recursion on ℕ
  here  : ∀ {n} → n < suc n
  there : ∀ {n m} → n < m → n < suc m

<-trs : ∀ {n m k} → n < m → m < k → n < k
<-trs p here      = there p
<-trs p (there q) = there (<-trs p q)

pred< : ∀ {n m} → suc n < m → n < m
pred< here = there here
pred< (there p) = there (pred< p)

0<s : ∀ n → 0 < suc n
0<s zero    = here
0<s (suc n) = there (0<s n)

s<s : ∀ {n m} → n < m → suc n < suc m
s<s here      = here
s<s (there p) = there (s<s p)

pred<pred : ∀ {n m} → suc n < suc m → n < m
pred<pred here = here
pred<pred {m = suc m} (there p) = there (pred<pred p)

<-irrefl : ∀ {n} → n < n → ⊥
<-irrefl {suc n} p = <-irrefl {n} (pred<pred p)

ℕ-set : ∀ {n : ℕ}(p : n ≡ n) → p ≡ refl
ℕ-set p = hedberg dec p refl
  where
    open import Relation.Nullary
    dec : (x y : ℕ) → x ≡ y ⊎ x ≢ y
    dec x y with Data.Nat._≟_ x y
    dec x y | yes p = inj₁ p
    dec x y | no ¬p = inj₂ ¬p

<-prop : ∀ {n m}(p q : n < m) → p ≡ q
<-prop p here = lem refl p where
  lem : ∀ {n m}(e : n ≡ m) → (p : n < suc m) → p ≡ tr (λ x → n < suc x) e here
  lem e here rewrite ℕ-set e = refl
  lem refl (there p) = ⊥-elim (<-irrefl p)
<-prop here (there q) = ⊥-elim (<-irrefl q)
<-prop (there p) (there q) = ap there (<-prop p q)

cmp : ∀ n m → ABC (n < m) (m < n) (n ≡ m)
cmp zero zero = inᶜ refl
cmp zero (suc m) = inᵃ (0<s m)
cmp (suc n) zero = inᵇ (0<s n)
cmp (suc n) (suc m) with cmp n m
... | inᵃ p = inᵃ (s<s p)
... | inᵇ p = inᵇ (s<s p)
... | inᶜ p = inᶜ (ap suc p)

cmp-refl : ∀ n → cmp n n ≡ inᶜ refl
cmp-refl zero = refl
cmp-refl (suc n) rewrite cmp-refl n = refl


-- Part 1
--------------------------------------------------------------------------------

module InductiveTypesFromBinaryTree where

  data Tree : Set where
    leaf : Tree
    node : Tree → Tree → Tree

  open import Data.Unit -- constructible as : ⊤ = (leaf ≡ leaf)

  -- Ty, Con, Var are also constructible from Tree
  infix 2 ι⇒_
  data Ty : Set where     -- as linear trees
    ι : Ty
    ι⇒_ : Ty → Ty

  infixl 3 _▶_
  data Con : Set where    -- as lists (Ty-annotated linear tree)
    ∙   : Con
    _▶_ : Con → Ty → Con

  data Var : Con → Ty → Set where   -- definable by recursion on Con
    vz : ∀ {Γ A} → Var (Γ ▶ A) A
    vs : ∀ {Γ A B} → Var Γ A → Var (Γ ▶ B) A

  -- Terms. The intrinsic inductive definition would be the following:

  -- data Tm n (Γ : Con n) : Ty → Set
  -- data Sp n (Γ : Con n) : Ty → Ty → Set

  -- data Sp n Γ where
  --   []  : ∀ {A} → Sp n Γ A A
  --   _∷_ : ∀ {A B} → Tm n Γ zero → Sp n Γ A B → Sp n Γ (suc A) B

  -- data Tm n Γ where
  --   ne : ∀ {A} → Var n Γ A → Sp n Γ A zero → Tm n Γ zero

  -- well-formedness predicates
  Tmw : Con → Ty → Tree → Set
  Spw : Con → Ty → Ty → Tree → Set
  Tmw Γ i t = ∃ λ A → Var Γ A × Spw Γ A ι t × i ≡ ι
  Spw Γ A   B leaf        = A ≡ B
  Spw Γ ι⇒A B (node t sp) = ∃ λ A → Tmw Γ ι t × Spw Γ A B sp × ι⇒A ≡ (ι⇒ A)

  Tm : Con → Ty → Set
  Tm Γ A = ∃ (Tmw Γ A)

  Sp : Con → Ty → Ty → Set
  Sp Γ A B = ∃ (Spw Γ A B)

  [] : ∀ {Γ A} → Sp Γ A A
  [] = leaf , refl

  infixr 5 _∷_
  _∷_ : ∀ {Γ A B} → Tm Γ ι → Sp Γ A B → Sp Γ (ι⇒ A) B
  _∷_ (t , p) (sp , q) = node t sp , _ , p , q , refl

  ne : ∀ {Γ A} → Var Γ A → Sp Γ A ι → Tm Γ ι
  ne v (sp , p) = sp , _ , v , p , refl

  -- Example: construction of natural numbers from Tm. This is possible for any
  -- signature.
  NatSig : Con
  NatSig = ∙ ▶ ι ▶ (ι⇒ ι)  -- ∙ ▶ zero : Nat ▶ suc : Nat → Nat

  Nat : Set
  Nat = Tm NatSig ι

  Zero : Nat
  Zero = ne (vs vz) []

  Suc : Nat → Nat
  Suc n = ne vz (n ∷ [])

  NatElim : ∀ {i}(P : Nat → Set i) → P Zero → (∀ n → P n → P (Suc n)) → ∀ n → P n
  NatElim P z s (node t leaf , _ , vz , (_ , t* , refl , refl) , refl) =
    s (t , t*) (NatElim P z s (t , t*))
  NatElim P z s (node t (node _ _) , _ , vz , (_ , t* , (_ , _ , _ , ()) , refl) , refl)
  NatElim P z s (leaf , _ , vs vz , refl , refl) = z
  NatElim P z s (sp   , _ , vs (vs ()) , sp* , refl)


-- Part 2
--------------------------------------------------------------------------------

module BinaryTreeFromNaturals where

  -- The inductive definition for height-indexed trees would be the following:
  -- data Tree : ℕ → Set
  -- data Tree↓ : ℕ → Set

  -- data Tree where
  --   leaf   : Tree zero
  --   nodeL  : ∀ {n} → Tree  n → Tree↓ n → Tree (suc n)
  --   nodeR  : ∀ {n} → Tree↓ n → Tree  n → Tree (suc n)
  --   nodeLR : ∀ {n} → Tree  n → Tree  n → Tree (suc n)

  -- data Tree↓ where
  --   here  : ∀ {n} → Tree  n → Tree↓ (suc n)
  --   there : ∀ {n} → Tree↓ n → Tree↓ (suc n)

  -- Tree' n is the set of trees with height n.
  -- Tree'↓ n is the set of trees with height less than n.
  Tree'  : ℕ → Set
  Tree'↓ : ℕ → Set
  Tree' zero    = ⊤  -- "leaf" is the only tree with height 0.
  Tree' (suc n) =
    ABC (Tree'  n × Tree'↓ n) -- The left subtree is taller
        (Tree'↓ n × Tree'  n) -- The right subtree is taller
        (Tree'  n × Tree'  n) -- Subtrees have the same height
  Tree'↓ zero    = ⊥
  Tree'↓ (suc n) = Tree' n ⊎ Tree'↓ n

  Tree : Set
  Tree = ∃ Tree'

  tree↓ : ∀ {n m} → m < n → Tree' m → Tree'↓ n
  tree↓ (here   ) t = inj₁ t
  tree↓ (there p) t = inj₂ (tree↓ p t)

  tree↑ : ∀ {n} → Tree'↓ n → (∃ λ m → m < n × Tree' m)
  tree↑ {suc n} (inj₁ t) = n , here , t
  tree↑ {suc n} (inj₂ t) = tree↑ t .₁ , there (tree↑ t .₂ .₁) , tree↑ t .₂ .₂

  tree↓↑ : ∀ {n} (t : Tree'↓ n) → tree↓ (tree↑ t .₂ .₁) (tree↑ t .₂ .₂) ≡ t
  tree↓↑ {suc n} (inj₁ _) = refl
  tree↓↑ {suc n} (inj₂ t) rewrite tree↓↑ t = refl

  --------------------------------------------------------------------------------

  leaf : Tree
  leaf = 0 , tt

  node : Tree → Tree → Tree
  node (n , l) (m , r) with cmp n m
  ... | inᵃ p    = suc m , inᵇ (tree↓ p l , r)
  ... | inᵇ p    = suc n , inᵃ (l , tree↓ p r)
  ... | inᶜ refl = suc n , inᶜ (l , r)

  -- eliminator
  --------------------------------------------------------------------------------
  TreeElim : ∀ {i}(P : Tree → Set i) → P leaf → (∀ {l r} → P l → P r → P (node l r))
               → ∀ {n} (t : Tree' n)  → P (_ , t)
  Tree↓Elim : ∀ {i}(P : Tree → Set i) → P leaf → (∀ {l r} → P l → P r → P (node l r))
               → ∀ {n}(t : Tree'↓ n) → P (_ , tree↑ t .₂ .₂)
  TreeElim P pl pn {zero} tt = pl
  TreeElim P pl pn {suc n} (inᵃ (l , r))
    with cmp n (₁ (tree↑ r)) | pn (TreeElim P pl pn l) (Tree↓Elim P pl pn r)
  ... | inᵃ p | hyp = ⊥-elim (<-irrefl (<-trs (tree↑ r .₂ .₁) p))
  ... | inᵇ p | hyp = tr (λ x → P (suc n , inᵃ (l , x)))
                         (ap (λ x → tree↓ x _) (<-prop _ _) ◾ tree↓↑ r)
                         hyp
  ... | inᶜ p | hyp = ⊥-elim (<-irrefl (tr ( tree↑ r .₁ <_) p (tree↑ r .₂ .₁)))
  TreeElim P pl pn {suc n} (inᵇ (l , r))
    with cmp (₁ (tree↑ l)) n | pn (Tree↓Elim P pl pn l) (TreeElim P pl pn r)
  ... | inᵃ p | hyp = tr (λ x → P (suc n , inᵇ (x , r)))
                         (ap (λ x → tree↓ x _) (<-prop _ _) ◾ tree↓↑ l)
                         hyp
  ... | inᵇ p | hyp = ⊥-elim (<-irrefl (<-trs p (tree↑ l .₂ .₁)))
  ... | inᶜ p | hyp = ⊥-elim (<-irrefl (subst (_< n) p (tree↑ l .₂ .₁)))
  TreeElim P pl pn {suc n} (inᶜ (l , r)) with
    cmp n n | cmp-refl n | pn (TreeElim P pl pn l) (TreeElim P pl pn r)
  ... | _ | refl | hyp = hyp
  Tree↓Elim P pl pn {suc n} (inj₁ t) = TreeElim P pl pn t
  Tree↓Elim P pl pn {suc n} (inj₂ t) = Tree↓Elim P pl pn t


  -- computation rules
  --------------------------------------------------------------------------------
  leafβ : ∀ {i P pl}{pn : ∀ {l r} → P l → P r → P (node l r)}
          → TreeElim {i} P pl pn (leaf .₂) ≡ pl
  leafβ = refl

  -- Agda doesn't want to let me prove this with with-pattern,
  -- I'd have to switch to ABC-elimination.
  -- Seems alright though.
  nodeβ : ∀ {i P pl}{pn : ∀ {l r} → P l → P r → P (node l r)}{l r}
          → TreeElim {i} P pl pn (node l r .₂)
          ≡ pn (TreeElim P pl pn (l .₂)) (TreeElim P pl pn (r .₂))
  nodeβ {i} {P} {pl} {pn} {n , l} {m , r} = {!!}
