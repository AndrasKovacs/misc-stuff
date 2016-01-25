
-- Sum of finite family of finite types is finite

open import Data.List renaming (map to lmap) hiding ([_])
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Nullary
open import Data.Empty
open import Data.Product renaming (map to pmap)
open import Data.Unit hiding (_≤_)
open import Function
open import Level renaming (suc to lsuc; zero to lzero)
open import Data.Sum renaming (map to smap)
open import Algebra

module LM {α}{A : Set α} = Algebra.Monoid (Data.List.monoid A)

data _∈_ {α}{A : Set α}(x : A) : List A → Set α where
  here  : ∀ {xs} → x ∈ (x ∷ xs)
  there : ∀ {y ys} → x ∈ ys → x ∈ (y ∷ ys)

module _ {α}{A : Set α} where 

  _∉_ : A → List A → Set α
  x ∉ xs = ¬ (x ∈ xs)
  
  Unique : List A → Set α
  Unique []       = Lift ⊤
  Unique (x ∷ xs) = x ∉ xs × Unique xs

  Disjoint : List A → List A → Set α
  Disjoint xs ys = ∀ {x} → x ∈ xs → x ∉ ys

  ∈-split : ∀ {x : A} xs {ys} → x ∈ (xs ++ ys) → (x ∈ xs) ⊎ (x ∈ ys)
  ∈-split []       here      = inj₂ here
  ∈-split (_ ∷ _)  here      = inj₁ here
  ∈-split []       (there e) = smap (λ ()) (λ _ → there e) $ ∈-split [] e
  ∈-split (_ ∷ xs) (there e) = smap there id $ ∈-split xs e

  ∈-case : ∀ {x y : A} {xs} → x ∈ (y ∷ xs) → x ≡ y ⊎ x ∈ xs
  ∈-case here      = inj₁ refl
  ∈-case (there p) = inj₂ p

  Unique++ : ∀ {xs ys} → Unique xs → Unique ys → Disjoint xs ys → Unique (xs ++ ys)
  Unique++ {[]} _ uys _ = uys
  Unique++ {x ∷ xs} (x∉xs , uxs) uys disj =
    [ x∉xs , disj here ] ∘ ∈-split xs , Unique++ uxs uys (disj ∘ there)

  _∈++_ :  ∀ {a : A}{as} → a ∈ as → ∀ bs → a ∈ (as ++ bs)
  _∈++_ here      bs = here
  _∈++_ (there p) bs = there (p ∈++ bs)
  
  _++∈_ : ∀ {a : A}{as} bs → a ∈ as → a ∈ (bs ++ as)
  []       ++∈ p = p
  (x ∷ bs) ++∈ p = there (bs ++∈ p)

record Finite {α}(A : Set α) : Set α where
  constructor rec
  field
    enum     : List A
    complete : ∀ a → a ∈ enum
    unique   : Unique enum

module _ {α β}{A : Set α}{B : Set β} where

  ∈-map-extract : ∀ {as b}{f : A → B} → b ∈ lmap f as → ∃ λ a → b ≡ f a
  ∈-map-extract {[]} ()
  ∈-map-extract {x ∷ as} here = x , refl
  ∈-map-extract {x ∷ as} (there p) = ∈-map-extract p  

  Injection : (A → B) → Set _
  Injection f = ∀ {a a'} → f a ≡ f a' → a ≡ a'

  ∈-unmap : ∀ {f : A → B}{a} as → Injection f → f a ∈ lmap f as → a ∈ as
  ∈-unmap [] inj ()
  ∈-unmap {f}{a} (a' ∷ as) inj p =
    [ (λ p₁ → subst (λ x → a ∈ (x ∷ as)) (inj p₁) here) , there ∘ ∈-unmap as inj ]′ (∈-case p)

  Unique-map : ∀ as {f : A → B} → Unique as → Injection f → Unique (lmap f as)
  Unique-map []       uas          inj = lift tt
  Unique-map (a ∷ as) (a∉as , uas) inj = a∉as ∘ ∈-unmap _ inj , Unique-map as uas inj

  ∈-map : ∀ {a : A}{as}(f : A → B) → a ∈ as → f a ∈ lmap f as
  ∈-map f here      = here
  ∈-map f (there p) = there (∈-map f p)
  
  ∈-concatMap : ∀ {a b as}(f : A → List B) → a ∈ as → b ∈ f a → b ∈ concatMap f as
  ∈-concatMap f (here {xs})    pb = pb ∈++ concatMap f xs
  ∈-concatMap f (there {y} pa) pb = f y ++∈ ∈-concatMap f pa pb

  ∈-concatMap-extract :
    ∀ {f : A → List B}{b as} → b ∈ concatMap f as → ∃ λ a → (a ∈ as) × (b ∈ f a)
  ∈-concatMap-extract {as = []} ()
  ∈-concatMap-extract {f}{as = a ∷ as} p =
    [ (λ z → a , here , z) ,
      (λ p → pmap id (pmap there id) (∈-concatMap-extract p)) ]′
    (∈-split (f a) p)

module _ {α β}{A : Set α}{B : A → Set β} where
  _,_-inj :
    ∀ {a a' b b'} → (∃ B ∋ (a , b)) ≡ (a' , b')
    → Σ (a ≡ a') λ p → subst B p b ≡ b'
  _,_-inj refl = refl , refl    

  _,_-inj' : ∀ {a b b'} → (∃ B ∋ (a , b)) ≡ (a , b') → b ≡ b'
  _,_-inj' refl = refl

  concatMap-Unique :
      {as : List A}{f : ∀ a → List (B a)}
    → Unique as → (∀ a → Unique (f a)) → Unique (concatMap (λ a → lmap (_,_ a) (f a)) as)
  concatMap-Unique {as = []}     uas          ufa = lift tt
  concatMap-Unique {as = a ∷ as}{f} (a∉as , uas) ufa =
    Unique++
      (Unique-map (f a) (ufa a) _,_-inj')
      (concatMap-Unique uas ufa)
      (λ p₁ p₂ →
        -- I'm sleepy ...
        let foo  = pmap id (pmap id ∈-map-extract) (∈-concatMap-extract {as = as} p₂)
            bar  = ∈-map-extract p₁
            baz  = proj₂ bar
            qux  = proj₂ $ proj₂ $ proj₂ foo
            frog = proj₁ $ proj₂ foo
            deer = proj₁ $ _,_-inj (trans (sym qux) baz)
        in a∉as (subst (λ x → x ∈ as) deer frog))

  Finite∃ : Finite A → (∀ a → Finite (B a)) → Finite (∃ B)
  Finite∃ finA finB =
    rec enum complete (concatMap-Unique (F.unique finA) (F.unique ∘ finB))
    where
      module F where open Finite public
      
      enum : List (∃ B)
      enum = concatMap (λ a → lmap ,_ (F.enum (finB a))) (F.enum finA)
      
      complete : ∀ (ap : ∃ B) → ap ∈ enum
      complete (a , pa) =
        ∈-concatMap _ (F.complete finA a) (∈-map (_,_ a) (F.complete (finB a) pa))
