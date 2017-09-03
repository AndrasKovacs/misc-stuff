
open import Lib hiding (_×_; ⊤)
import Lib as L
open import Category.Monad
open import Data.Maybe hiding (map)
open module MaybeM {α} = RawMonad {α} Data.Maybe.monad public

mutual
  -- Types
  data * : Set where
    ⊤ : *
    μ : F → *

    -- Functors
  data F : Set where
    I       : F
    K       : * → F
    _+_ _×_ : F → F → F

infixr 5 _+_
infixr 6 _×_

mutual
  ⟦_⟧ : * → Set
  ⟦ ⊤   ⟧ = L.⊤
  ⟦ μ f ⟧ = ⟦μ⟧ f

  ⟦_⟧ᶠ : F → Set → Set
  ⟦ I     ⟧ᶠ A = A
  ⟦ K a   ⟧ᶠ _ = ⟦ a ⟧
  ⟦ f + g ⟧ᶠ A = ⟦ f ⟧ᶠ A ⊎ ⟦ g ⟧ᶠ A
  ⟦ f × g ⟧ᶠ A = ⟦ f ⟧ᶠ A L.× ⟦ g ⟧ᶠ A

  data ⟦μ⟧ (f : F) : Set where
    ⟨_⟩ : ⟦ f ⟧ᶠ (⟦μ⟧ f) → ⟦μ⟧ f

out : ∀ {f} → ⟦μ⟧ f → ⟦ f ⟧ᶠ (⟦μ⟧ f)
out ⟨ t ⟩ = t

data AtLeastOne (A B : Set) : Set where
  left  : A → AtLeastOne A B
  right : B → AtLeastOne A B
  both  : A → B → AtLeastOne A B

mutual
  -- non-empty functor
  *ᵀ : * → Set → Set
  *ᵀ ⊤     A = A
  *ᵀ (μ f) A = μᵀ f A

  data μᵀ (f : F)(A : Set) : Set where
    ⟨_⟩ : Fᵀ f (μ f) A → μᵀ f A

  -- non-empty higher functor
  Fᵀ : F → * → Set → Set
  Fᵀ I       a A = *ᵀ a A
  Fᵀ (K a)   _ A = *ᵀ a A
  Fᵀ (f + g) a A = AtLeastOne (Fᵀ f a A) (Fᵀ g a A)
  Fᵀ (f × g) a A = Fᵀ f a (Fᵀ g a A)

outᵀ : ∀ {f A} → μᵀ f A → Fᵀ f (μ f) A
outᵀ ⟨ t ⟩ = t

module TrieOps where
  mutual
    lookup : ∀ a {B} → *ᵀ a B → ⟦ a ⟧ → Maybe B
    lookup ⊤     t     i     = just t
    lookup (μ f) ⟨ t ⟩ ⟨ i ⟩ = lookupF f f t i

    lookupF : ∀ f g {B} → Fᵀ f (μ g) B → ⟦ f ⟧ᶠ (⟦μ⟧ g) → Maybe B
    lookupF I       h ⟨ t ⟩      ⟨ i ⟩     = lookupF h h t i
    lookupF (K a)   h t          i         = lookup a t i
    lookupF (f + g) h (left l)   (inl i)   = lookupF f h l i
    lookupF (f + g) h (left l)   (inr i)   = nothing
    lookupF (f + g) h (right r)  (inl i)   = nothing
    lookupF (f + g) h (right r)  (inr i)   = lookupF g h r i
    lookupF (f + g) h (both l r) (inl i)   = lookupF f h l i
    lookupF (f + g) h (both l r) (inr i)   = lookupF g h r i
    lookupF (f × g) h t          (il , ir) = lookupF f h t il >>= (λ t' → lookupF g h t' ir)

  mutual
    modify : ∀ a {B} → Maybe (*ᵀ a B) → ⟦ a ⟧ → (Maybe B → Maybe B) → Maybe (*ᵀ a B)
    modify ⊤     t i     m = m t
    modify (μ f) t ⟨ i ⟩ m = ⟨_⟩ <$> modifyF f f (outᵀ <$> t) i m

    modifyF : ∀ f g {B} → Maybe (Fᵀ f (μ g) B) → ⟦ f ⟧ᶠ (⟦μ⟧ g) → (Maybe B → Maybe B) → Maybe (Fᵀ f (μ g) B)
    modifyF I       h t                 ⟨ i ⟩     m = ⟨_⟩ <$> modifyF h h (outᵀ <$> t) i m
    modifyF (K a)   h t                 i         m = modify a t i m
    modifyF (f + g) h (just (left l))   (inl i)   m = left <$> modifyF f h (just l) i m
    modifyF (f + g) h (just (left l))   (inr i)   m = both l <$> modifyF g h nothing i m
    modifyF (f + g) h (just (right r))  (inl i)   m = both <$> modifyF f h nothing i m ⊛ just r
    modifyF (f + g) h (just (right r))  (inr i)   m = right <$> modifyF g h (just r) i m
    modifyF (f + g) h (just (both l r)) (inl i)   m = both <$> modifyF f h (just l) i m ⊛ just r
    modifyF (f + g) h (just (both l r)) (inr i)   m = both l <$> modifyF g h (just r) i m
    modifyF (f + g) h nothing           (inl i)   m = left <$> modifyF f h nothing i m
    modifyF (f + g) h nothing           (inr i)   m = right <$> modifyF g h nothing i m
    modifyF (f × g) h t                 (il , ir) m = modifyF f h t il (λ t → modifyF g h t ir m)

mutual
  lt : (A : *) → ⟦ A ⟧ → ⟦ A ⟧ → Set
  lt ⊤     t     u     = ⊥
  lt (μ f) ⟨ t ⟩ ⟨ u ⟩ = ltF f f t u

  ltF : ∀ F G → ⟦ F ⟧ᶠ (⟦μ⟧ G) → ⟦ F ⟧ᶠ (⟦μ⟧ G) → Set
  ltF I       H ⟨ t ⟩     ⟨ u ⟩     = ltF H H t u
  ltF (K A)   H t         u         = lt A t u
  ltF (F + G) H (inl t)   (inl u)   = ltF F H t u
  ltF (F + G) H (inl t)   (inr u)   = L.⊤
  ltF (F + G) H (inr t)   (inl u)   = L.⊥
  ltF (F + G) H (inr t)   (inr u)   = ltF G H t u
  ltF (F × G) H (t₁ , t₂) (u₁ , u₂) = ltF F H t₁ u₁ ⊎ ((t₁ ≡ u₁) L.× ltF G H t₂ u₂)

--------------------------------------------------------------------------------

mutual
  foldr : ∀ a {B C : Set} → (B → C → C) → (B → C) → *ᵀ a B → C
  foldr ⊤     c z t     = z t
  foldr (μ f) c z ⟨ t ⟩ = foldrF f f c z t

  {-# TERMINATING #-}
  foldrF : ∀ (f g : F) {B C : Set} → (B → C → C) → (B → C) → Fᵀ f (μ g) B → C
  foldrF I       h c z ⟨ t ⟩      = foldrF h h c z t
  foldrF (K a)   h c z t          = foldr a c z t
  foldrF (f + g) h c z (left l)   = foldrF f h c z l
  foldrF (f + g) h c z (right r)  = foldrF g h c z r
  foldrF (f + g) h c z (both l r) = foldrF f h c (λ b → c b (foldrF g h c z r)) l
  foldrF (f × g) h c z t          = foldrF f h (λ t r → foldrF g h c (λ b → c b r) t) (foldrF g h c z) t

--------------------------------------------------------------------------------

open import Relation.Nullary
open import Relation.Nullary.Decidable hiding (map)

Injective : ∀ {A B : Set} → (A → B) → Set
Injective f = ∀ {x y} → f x ≡ f y → x ≡ y

Dec≡-cong :
  ∀ {A B : Set}{f : A → B} → Injective f → ∀ {x y} → Dec (x ≡ y) → Dec (f x ≡ f y)
Dec≡-cong {f = f} inj (yes p) = yes (f & p)
Dec≡-cong {f = f} inj (no ¬p) = no (¬p ∘ inj)

⟨⟩-inj : ∀ {f} → Injective (⟦μ⟧.⟨_⟩ {f})
⟨⟩-inj refl = refl

inl-inj : ∀ {A B} → Injective (inl {A}{B})
inl-inj refl = refl

inr-inj : ∀ {A B} → Injective (inr {A}{B})
inr-inj refl = refl

_,-inj : ∀ {A B : Set}(t : A) → Injective ((B → A L.× B) ∋ _,_ t)
_,-inj t refl = refl

mutual
  eq? : ∀ a (t u : ⟦ a ⟧) → Dec (t ≡ u)
  eq? ⊤     t     u     = yes refl
  eq? (μ f) ⟨ t ⟩ ⟨ u ⟩ = Dec≡-cong ⟨⟩-inj (eqF? f f t u)

  eqF? : ∀ f g (t u : ⟦ f ⟧ᶠ (⟦μ⟧ g)) → Dec (t ≡ u)
  eqF? I h ⟨ t ⟩ ⟨ u ⟩ = Dec≡-cong ⟨⟩-inj (eqF? h h t u)
  eqF? (K a) h t u = eq? a t u
  eqF? (f + g) h (inl t) (inl u) = Dec≡-cong inl-inj (eqF? f h t u)
  eqF? (f + g) h (inl t) (inr u) = no (λ ())
  eqF? (f + g) h (inr t) (inl u) = no (λ ())
  eqF? (f + g) h (inr t) (inr u) = Dec≡-cong inr-inj (eqF? g h t u)
  eqF? (f × g) h (t₁ , t₂) (u₁ , u₂) with eqF? f h t₁ u₁
  ... | yes refl = Dec≡-cong (t₁ ,-inj) (eqF? g h t₂ u₂)
  ... | no ¬p    = no (λ {refl → ¬p refl})

--------------------------------------------------------------------------------

open import Data.List

List1 : Set → Set
List1 A = A L.× List A

map1 : ∀ {A B} → (A → B) → List1 A → List1 B
map1 f (a , as) = f a , map f as

_++1_ : ∀ {A} → List1 A → List1 A → List1 A
(x , xs) ++1 (y , ys) = x , xs ++ (y ∷ ys)

_∷1_ : ∀ {A} → A → List1 A → List1 A
a ∷1 (a' , as) = a , a' ∷ as

concat1 : ∀ {A} → List1 (List1 A) → List1 A
concat1 ((a , as) , ass) = a , as ++ concatMap (uncurry _∷_) ass

unzip1 : ∀ {A B} → List1 (A ⊎ B) → AtLeastOne (List1 A) (List1 B)
unzip1 (inl a , []) = left (a , [])
unzip1 (inr b , []) = right (b , [])
unzip1 (ab , ab' ∷ abs) = case unzip1 (ab , abs) of λ {
  (left as)    → case ab of λ {(inl a) → left (a ∷1 as); (inr b) → both as (b , [])};
  (right bs)   → case ab of λ {(inl a) → both (a , []) bs; (inr b) → right (b ∷1 bs)};
  (both as bs) → case ab of λ {(inl a) → both (a ∷1 as) bs; (inr b) → both as (b ∷1 bs)}}

first : ∀ {A B C : Set} → (A → C) → A L.× B → C L.× B
first f (a , b) = (f a , b)

Assocs : * → Set → Set
Assocs a B = List1 (⟦ a ⟧ L.× B)

{-# TERMINATING #-}
OrdKeys : ∀ {a B} → Assocs a B → Set
OrdKeys (a , [])                     = L.⊤
OrdKeys ((a , _) , ((a' , v) ∷ abs)) = lt _ a a' L.× OrdKeys ((a' , v) , abs)

AssocsF : F → F → Set → Set
AssocsF f g B = List1 (⟦ f ⟧ᶠ (⟦μ⟧ g) L.× B)

{-# TERMINATING #-}
OrdKeysF : ∀ {f g B} → AssocsF f g B → Set
OrdKeysF ((a , v) , []) = L.⊤
OrdKeysF {f}{g}((a , _) , (a' , v) ∷ abs) = ltF f g a a' L.× OrdKeysF {f}{g}((a' , v) , abs)

group : ∀ {A B} → List1 (⟦ A ⟧ L.× B) → List1 (⟦ A ⟧ L.× List1 B)
group ((k , v) , [])             = (k , v , []) , []
group ((k , v) , (k' , v') ∷ ys) with eq? _ k k'
... | yes _    = {!!}
... | no ¬p    = {!!}

-- --------------------------------------------------------------------------------

-- mutual
--   toList : ∀ a {B} → *ᵀ a B → Assocs a B
--   toList ⊤     t     = (tt , t) , []
--   toList (μ f) ⟨ t ⟩ = map1 (first ⟨_⟩) (toListF f f t)

--   {-# TERMINATING #-}
--   toListF : ∀ f g {B} → Fᵀ f (μ g) B → AssocsF f g B
--   toListF I       h ⟨ t ⟩      = map1 (first ⟨_⟩) (toListF h h t)
--   toListF (K a)   h t          = toList a t
--   toListF (f + g) h (left l)   = map1 (first inl) (toListF f h l)
--   toListF (f + g) h (right r)  = map1 (first inr) (toListF g h r)
--   toListF (f + g) h (both l r) = map1 (first inl) (toListF f h l) ++1 map1 (first inr) (toListF g h r)
--   toListF (f × g) h t          =
--     concat1 (map1 (λ {(k , v) → map1 (first (_,_ k)) (toListF g h v)}) (toListF f h t))

-- mutual
--   fromList : ∀ a {B} → Assocs a B → *ᵀ a B
--   fromList ⊤     abs = proj₂ (proj₁ abs)
--   fromList (μ f) abs = ⟨ fromListF f f (map1 (first out) abs) ⟩

--   {-# TERMINATING #-}
--   fromListF : ∀ f g {B} → AssocsF f g B → Fᵀ f (μ g) B
--   fromListF I       h abs = ⟨ fromListF h h (map1 (first out) abs) ⟩
--   fromListF (K a)   h abs = fromList a abs
--   fromListF (f + g) h abs =
--     case unzip1 (map1 (λ {((inl k) , v) → inl (k , v); ((inr k) , v) → inr (k , v)}) abs) of λ {
--       (left l)   → left (fromListF f h l);
--       (right r)  → right (fromListF g h r);
--       (both l r) → both (fromListF f h l) (fromListF g h r)}
--   fromListF (f × g) h abs = fromListF f h {!!} -- requires grouping operation



-- OrdKeys : ∀ {a B} → ⟦ a ⟧ → Assocs a B → Set
-- OrdKeys a (end (a' , _))   = lt _ a a'
-- OrdKeys a ((a' , _) ∷ abs) = lt _ a a' L.× OrdKeys a' abs

-- AssocsF : F → F → Set → Set
-- AssocsF f g B = List (⟦ f ⟧ᶠ (⟦μ⟧ g) L.× B)

-- OrdKeysF : ∀ {f g B} → ⟦ f ⟧ᶠ (⟦μ⟧ g) → AssocsF f g B → Set
-- OrdKeysF {f}{g} a (end (a' , _))   = ltF f g a a'
-- OrdKeysF {f}{g} a ((a' , _) ∷ abs) = ltF f g a a' L.× OrdKeysF {f}{g} a abs


-- data List (A : Set) : Set where
--   end : A → List A
--   _∷_ : A → List A → List A
-- infixr 5 _∷_

-- _++_ : ∀ {A} → List A → List A → List A
-- end x    ++ ys = x ∷ ys
-- (x ∷ xs) ++ ys = x ∷ (xs ++ ys)

-- map : ∀ {A B} → (A → B) → List A → List B
-- map f (end a)  = end (f a)
-- map f (a ∷ as) = f a ∷ map f as

-- concat : ∀ {A} → List (List A) → List A
-- concat (end ass)  = ass
-- concat (as ∷ ass) = as ++ concat ass

-- Assocs : * → Set → Set
-- Assocs a B = List (⟦ a ⟧ L.× B)

-- unzip : ∀ {A B} → List (A ⊎ B) → AtLeastOne (List A) (List B)
-- unzip (end (inl a)) = left (end a)
-- unzip (end (inr b)) = right (end b)
-- unzip (inl a ∷ abs) =
--   case unzip abs of λ {
--     (left as)    → left (a ∷ as);
--     (right bs)   → both (end a) bs;
--     (both as bs) → both (a ∷ as) bs}
-- unzip (inr b ∷ abs) =
--   case unzip abs of λ {
--     (left as)    → both as (end b);
--     (right bs)   → right (b ∷ bs);
--     (both as bs) → both as (b ∷ bs)}

-- OrdKeys : ∀ {a B} → ⟦ a ⟧ → Assocs a B → Set
-- OrdKeys a (end (a' , _))   = lt _ a a'
-- OrdKeys a ((a' , _) ∷ abs) = lt _ a a' L.× OrdKeys a' abs

-- AssocsF : F → F → Set → Set
-- AssocsF f g B = List (⟦ f ⟧ᶠ (⟦μ⟧ g) L.× B)

-- OrdKeysF : ∀ {f g B} → ⟦ f ⟧ᶠ (⟦μ⟧ g) → AssocsF f g B → Set
-- OrdKeysF {f}{g} a (end (a' , _))   = ltF f g a a'
-- OrdKeysF {f}{g} a ((a' , _) ∷ abs) = ltF f g a a' L.× OrdKeysF {f}{g} a abs

-- idea : toList via foldr, fromList via insert

-- mutual
--   toList : ∀ a {B} → *ᵀ a B → Assocs a B
--   toList ⊤     t     = end (tt , t)
--   toList (μ f) ⟨ t ⟩ = map (λ {(k , v) → ⟨ k ⟩ , v}) (toListF f f t)

--   {-# TERMINATING #-}
--   toListF : ∀ f g {B} → Fᵀ f (μ g) B → AssocsF f g B
--   toListF I       h ⟨ t ⟩      = map (λ {(k , v) → ⟨ k ⟩ , v}) (toListF h h t)
--   toListF (K a)   h t          = toList a t
--   toListF (f + g) h (left l)   = map (λ {(k , v) → inl k , v}) (toListF f h l)
--   toListF (f + g) h (right r)  = map (λ {(k , v) → inr k , v}) (toListF g h r)
--   toListF (f + g) h (both l r) =
--        map (λ {(k , v) → inl k , v}) (toListF f h l)
--     ++ map (λ {(k , v) → inr k , v}) (toListF g h r)
--   toListF (f × g) h t          =
--     concat (map (λ {(k , v) → map (λ {(k' , v') → (k , k') , v'}) (toListF g h v)}) (toListF f h t))

-- mutual
--   fromList : ∀ a {B} → Assocs a B → *ᵀ a B
--   fromList ⊤    (end (_ , b))   = b
--   fromList ⊤    ((_ , b) ∷ abs) = b -- impossible if input is ordered
--   fromList (μ f) abs            = ⟨ fromListF f f (map (λ {(k , v) → out k , v}) abs) ⟩

--   {-# TERMINATING #-}
--   fromListF : ∀ f g {B} → AssocsF f g B → Fᵀ f (μ g) B
--   fromListF I       h abs = ⟨ fromListF h h (map (λ {(k , v) → out k , v}) abs) ⟩
--   fromListF (K a)   h abs = fromList a abs
--   fromListF (f + g) h abs =
--     case unzip (map (λ {((inl k) , v) → inl (k , v); ((inr k) , v) → inr (k , v)}) abs) of λ {
--       (left l)   → left (fromListF f h l);
--       (right r)  → right (fromListF g h r);
--       (both l r) → both (fromListF f h l) (fromListF g h r)}

--   fromListF (f × g) h abs = {!!}

--------------------------------------------------------------------------------

Trie : * → Set → Set
Trie a B = Maybe (*ᵀ a B)

pattern empty = nothing

lookup : ∀ {a B} → ⟦ a ⟧ → Trie a B → Maybe B
lookup i t = t >>= λ t → TrieOps.lookup _ t i

insert : ∀ {a B} → ⟦ a ⟧ → B → Trie a B → Trie a B
insert i b t = TrieOps.modify _ t i (λ _ → just b)

singleton : ∀ {a B} → ⟦ a ⟧ → B → Trie a B
singleton i b = insert i b empty

delete : ∀ {a B} → ⟦ a ⟧ → Trie a B → Trie a B
delete i t = TrieOps.modify _ t i (λ _ → nothing)

--------------------------------------------------------------------------------

Bool : *
Bool = μ (K ⊤ + K ⊤)

true : ⟦ Bool ⟧
true = ⟨ inl tt ⟩

false : ⟦ Bool ⟧
false = ⟨ inr tt ⟩

-- List : * → *
-- List A = μ (K ⊤ + K A × I)

-- nil : ∀ {a} → ⟦ List a ⟧
-- nil = ⟨ inl tt ⟩

-- _∷_ : ∀ {a} → ⟦ a ⟧ → ⟦ List a ⟧ → ⟦ List a ⟧
-- a ∷ as = ⟨ inr (a , as) ⟩
-- infixr 5 _∷_

-- Nat : *
-- Nat = μ (K ⊤ + I)

-- zero : ⟦ Nat ⟧
-- zero = ⟨ inl tt ⟩

-- suc : ⟦ Nat ⟧ → ⟦ Nat ⟧
-- suc n = ⟨ inr n ⟩

-- k1 : ⟦ List Bool ⟧
-- k1 = true ∷ nil

-- t1 = insert (true ∷ true ∷ nil) (suc zero) (insert nil zero (singleton k1 (suc (suc zero))))
-- l1 = lookup k1 t1

