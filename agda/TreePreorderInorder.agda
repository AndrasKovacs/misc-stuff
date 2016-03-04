
-- Binary trees are unambiguously identified by their preorder and inorder traversals

module _ {α}(A : Set α) where

open import Data.Empty
open import Data.List hiding ([_])
open import Data.Nat
open import Data.Product renaming (map to productMap)
open import Data.Sum renaming (map to sumMap)
open import Data.Unit
open import Function
open import Relation.Binary.PropositionalEquality hiding (preorder; [_])
open import Relation.Nullary
import Level as L

open import Data.List.Properties using (length-++; ∷-injective)
open import Data.Nat.Properties.Simple using (+-suc)

data Tree : Set α where
  leaf : Tree
  node : (x : A) (l r : Tree) → Tree

data InTree (x : A) : Tree → Set α where
  here  : ∀ {l r}   → InTree x (node x l r)
  left  : ∀ {y l r} → InTree x l → InTree x (node y l r)
  right : ∀ {y l r} → InTree x r → InTree x (node y l r)

data InList (x : A) : List A → Set α where
  here  : ∀ {xs}   → InList x (x ∷ xs)
  there : ∀ {y xs} → InList x xs → InList x (y ∷ xs)

inOrder : Tree → List A
inOrder leaf         = []
inOrder (node x l r) = inOrder l ++ x ∷ inOrder r

preOrder : Tree → List A
preOrder leaf         = []
preOrder (node x l r) = x ∷ preOrder l ++ preOrder r

-- Disjointness
DisjLists : List A → List A → Set α
DisjLists xs ys = ∀ {x} → InList x xs → ¬ InList x ys

DisjTrees : Tree → Tree → Set α
DisjTrees t t' = ∀ {x} → InTree x t → ¬ InTree x t'

NoDupList : List A → Set α
NoDupList []       = L.Lift ⊤
NoDupList (x ∷ xs) = ¬ InList x xs × NoDupList xs

-- A tree is nodup if its subtrees are disjoint and nodup and the root
-- value is not in the subtrees
NoDupTree : Tree → Set α
NoDupTree leaf = L.Lift ⊤
NoDupTree (node x l r) = 
  ¬ InTree x l × ¬ InTree x r × NoDupTree l × NoDupTree r × DisjTrees l r

infixr 5 _^++_ _++^_
_^++_ : ∀ {x xs} ys → InList x xs → InList x (ys ++ xs)
[]       ^++ e = e
(_ ∷ ys) ^++ e = there (ys ^++ e)

_++^_ : ∀ {x xs} → InList x xs → ∀ ys → InList x (xs ++ ys)
here    ++^ ys = here
there e ++^ ys = there (e ++^ ys)

listSplit : ∀ {x} xs {ys} → InList x (xs ++ ys) → InList x xs ⊎ InList x ys
listSplit []       here      = inj₂ here
listSplit (_ ∷ _)  here      = inj₁ here
listSplit []       (there e) = sumMap (λ ()) (λ _ → there e) $ listSplit [] e
listSplit (_ ∷ xs) (there e) = sumMap there id $ listSplit xs e 

InI⇒InT : ∀ {x} t → InList x (inOrder t) → InTree x t
InI⇒InT leaf ()
InI⇒InT (node x l r) e with listSplit (inOrder l) e
... | inj₁ el         = left (InI⇒InT l el)
... | inj₂ here       = here
... | inj₂ (there er) = right (InI⇒InT r er)

InP⇒InT : ∀ {x} t → InList x (preOrder t) → InTree x t
InP⇒InT leaf ()
InP⇒InT (node _ _ _) here      = here
InP⇒InT (node x l r) (there e) = 
  [ left ∘ InP⇒InT l , right ∘ InP⇒InT r ] (listSplit (preOrder l) e)

InT⇒InP : ∀ {x} t → InTree x t → InList x (preOrder t)
InT⇒InP leaf ()
InT⇒InP (node x l r) here      = here
InT⇒InP (node x l r) (left p)  = there (InT⇒InP l p ++^ preOrder r)
InT⇒InP (node x l r) (right p) = there (preOrder l ^++ InT⇒InP r p)

ND++ : ∀ xs ys → NoDupList xs → NoDupList ys → DisjLists xs ys → NoDupList (xs ++ ys)
ND++ []       _  _          pys _    = pys
ND++ (_ ∷ xs) ys (px , pxs) pys disj =
  ([ px , disj here ] ∘ listSplit xs) , ND++ _ _ pxs pys (disj ∘ there)

NDSplit : ∀ xs {ys} → NoDupList (xs ++ ys) → NoDupList xs × NoDupList ys × DisjLists xs ys
NDSplit [] p = L.lift tt , p , (λ ())
NDSplit (x ∷ xs) {ys} (px , pxs) with NDSplit xs pxs
... | ndxs , ndys , disj = (px ∘ flip _++^_ ys , ndxs) , ndys , disj' 
  where
  disj' : DisjLists (x ∷ xs) ys
  disj' here      e' = px (xs ^++ e')
  disj' (there e) e' = disj e e'

NDT⇒NDI : ∀ t → NoDupTree t → NoDupList (inOrder t)
NDT⇒NDI leaf _ = L.lift tt
NDT⇒NDI (node x l r) (pxl , pxr , pl , pr , disj) =
  ND++ _ _ (NDT⇒NDI l pl) (pxr ∘ InI⇒InT r , NDT⇒NDI r pr) disj' 
  where
  disj' : DisjLists (inOrder l) (x ∷ inOrder r)
  disj' e here       = pxl  (InI⇒InT l e)
  disj' e (there e') = disj (InI⇒InT l e) (InI⇒InT r e')

NDT⇒NDP : ∀ t → NoDupTree t → NoDupList (preOrder t)
NDT⇒NDP leaf _ = L.lift tt
NDT⇒NDP (node _ l r) (pxl , pxr , pl , pr , disj) =
  ([ pxl ∘ InP⇒InT l , pxr ∘ InP⇒InT r ] ∘ listSplit (preOrder l))
  ,
  (ND++ _ _ (NDT⇒NDP l pl) (NDT⇒NDP r pr) (λ e e' → disj (InP⇒InT l e) (InP⇒InT r e')))

NDP⇒NDT : ∀ t → NoDupList (preOrder t) → NoDupTree t
NDP⇒NDT leaf p = L.lift tt
NDP⇒NDT (node x l r) (px , plr) with NDSplit (preOrder l) plr
... | pl , pr , disj = 
  (λ e → px (InT⇒InP l e ++^ preOrder r)) , 
  (λ e → px (preOrder l ^++ InT⇒InP r e)) , 
  NDP⇒NDT l pl , 
  NDP⇒NDT r pr , 
  (λ e e' → disj (InT⇒InP l e) (InT⇒InP r e'))

NDInsert : 
  ∀ {x} xs xs' {ys ys'}
  → NoDupList (xs ++ x ∷ ys)
  → NoDupList (xs' ++ x ∷ ys')
  → (xs ++ x ∷ ys) ≡ (xs' ++ x ∷ ys')
  → xs ≡ xs' × ys ≡ ys'
NDInsert [] []        _  _       p = refl , (proj₂ $ ∷-injective p)
NDInsert [] (_ ∷ xs') _ (px , _) p rewrite proj₁ $ ∷-injective p = ⊥-elim (px (xs' ^++ here))
NDInsert (_ ∷ xs) []  (px , _) _ p rewrite proj₁ $ ∷-injective p = ⊥-elim (px (xs ^++ here))
NDInsert (_ ∷ xs) (x ∷ xs') (px , nda) (px' , ndb) p with ∷-injective p
... | eqx , p' rewrite eqx = productMap (cong (_∷_ x)) id $ NDInsert _ _ nda ndb p'

trav-length : ∀ t → length (inOrder t) ≡ length (preOrder t)
trav-length leaf         = refl
trav-length (node x l r) rewrite 
    length-++ (inOrder l)  {x ∷ inOrder r} 
  | length-++ (preOrder l) {preOrder r}
  | trav-length l 
  | trav-length r 
  | +-suc (length (preOrder l)) (length (preOrder r)) 
  = refl

++-inj : 
    {xs xs' ys ys' : List A} 
  → xs ++ ys ≡ xs' ++ ys' → length xs ≡ length xs'
  → xs ≡ xs' × ys ≡ ys'
++-inj {[]}    {_ ∷ _}  p1 ()
++-inj {_ ∷ _} {[]}     p1 ()
++-inj {[]}    {[]}     p1 p2 = refl , p1
++-inj {_ ∷ _} {_  ∷ _} p1 p2 with ∷-injective p1
++-inj {x ∷ _} {.x ∷ _} _  p2 | refl , p1 = 
  productMap (cong (_∷_ x)) id (++-inj p1 (cong pred p2))

travEq : 
  ∀ t t' 
  → NoDupTree t
  → preOrder t ≡ preOrder t' 
  → inOrder t ≡ inOrder t'
  → t ≡ t'
travEq leaf         leaf            _ _ _ = refl
travEq leaf         (node _ _ _)    _ () _
travEq (node _ _ _) leaf            _ () _
travEq (node x l r) (node x' l' r') ndt pre ino 

-- Equality of root values
  with ∷-injective pre | ndt
... | px , pre' | pxl , pxr , pl , pr , disj 
  rewrite sym px

-- Get "NoDupTree t'" proof
  with NDP⇒NDT (node x l' r') (subst NoDupList pre (NDT⇒NDP _ ndt))
... | ndt' 

-- Equality of inorder subtree traversals
  with NDInsert (inOrder l) (inOrder l') (NDT⇒NDI _ ndt) (NDT⇒NDI _ ndt') ino
... | eqlI , eqrI 

-- Equality of preorder subtree traversals
  with ++-inj {preOrder l}{preOrder l'} pre' 
       (subst₂ _≡_ (trav-length l) (trav-length l') (cong length eqlI))
... | eqlP , eqrP 

-- Finish
  rewrite 
    travEq l l' pl eqlP eqlI 
  | travEq r r' pr eqrP eqrI 
  = refl
