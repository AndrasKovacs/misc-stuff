
{-# OPTIONS --type-in-type #-}

{-
Beta-eta reduction on Church-encoded terms doesn't work for supercompilation and fusion.
It's not robust or compositional, and only works when we specifically
write code for it.

In particular, more abstraction almost certainly results
in less fusion, contrary to what the Morte tutorial posits:

https://hackage.haskell.org/package/morte-1.0.1/docs/Morte-Tutorial.html#g:10

-}

open import Function
open import Relation.Binary.PropositionalEquality

-- lists

List : Set → Set
List A = ∀ L → (A → L → L) → L → L

[] : ∀ {A} → List A
[] _ c n = n

_∷_ : ∀ {A} → A → List A → List A
(x ∷ xs) _ c n = c x (xs _ c n)
infixr 5 _∷_

-- We'd like to have map fusion. So let's write it.
map : ∀ {A B} → (A → B) → List A → List B

-- translating the straightforward definition:
-- map f xs = foldr (λ x xs → f x ∷ xs) [] xs
map f xs = xs _ (λ x xs → f x ∷ xs) []

-- unfortunately, this doesn't fuse
f1 : ∀ {A B C} → (B → C) → (A → B) → List A → List C
f1 f g = map f ∘ map g

f2 : ∀ {A B C} → (B → C) → (A → B) → List A → List C
f2 f g = map (f ∘ g)

p1 : ∀ {A B C} → f1 {A}{B}{C} ≡ f2
p1 = {!!}

-- instead, we need to distribute the eliminators of the return type
map' : ∀ {A B} → (A → B) → List A → List B
map' f xs L c n = xs _ (λ x xs → c (f x) xs) n

f3 : ∀ {A B C} → (B → C) → (A → B) → List A → List C
f3 f g = map' f ∘ map' g

f4 : ∀ {A B C} → (B → C) → (A → B) → List A → List C
f4 f g = map' (f ∘ g)

p2 : ∀ {A B C} → f3 {A}{B}{C} ≡ f4
p2 = refl

-- another example: list _++_

_++_ : ∀ {A} → List A → List A → List A -- this version doesn't fuse
xs ++ ys = xs _ (λ x xs → x ∷ xs) ys

_++'_ : ∀ {A} → List A → List A → List A -- this version does
(xs ++' ys) r c n = xs _ c (ys r c n)

-- this fusion works with _++'_ but not with _++_
f5 : (f g h : Set → Set) (xs ys : List Set) → List Set
f5 f g h xs ys = map' f (map' g xs ++' map' h ys)

f6 : (f g h : Set → Set) (xs ys : List Set) → List Set
f6 f g h xs ys = map' (f ∘ g) xs ++' map' (f ∘ h) ys

p3 : f5 ≡ f6
p3 = refl

-- Now, you may say that enabling fusion takes a trivial amount of effort.
-- I try to show that in general it isn't trivial, and in many cases it
-- prevents us from reusing definitions or using higher-order definitions

-- for example, take concat for lists:

concat : ∀ {A} → List (List A) → List A
concat as = as _ _++'_ []  -- foldr (++) []

-- of course, this doesn't fuse
-- however, we can't reuse _++'_ in the correctly fusing version,
-- nor is it immediately transparent why it is the correct definition.

concat' : ∀ {A} → List (List A) → List A
concat' as r c n = as _ (λ xs acc → xs r c acc) n

-- In general, a fusing definition should be of the form

-- f a_1 a_2 ... a_n elim_1 elim_2 ... elim_n = t

-- where elim_i are the eliminators of the return type

-- This lets "g (f a_1 a_2 ... a_n)" neutral expressions reduce.
-- The eliminators provide a "hook" for external functions

-- It seems to me that converting an arbitrary function to a fusing
-- definition is not easier than supercompilation itself.

-- an example for concat fusion:
f7 : List Set → List Set
f7 = concat' ∘ map' (_∷ [])

p4 : f7 ≡ id
p4 = refl

f8 : List Set → List Set
f8 = concat ∘ map' (_∷ []) -- ≢ id

-- An example for what we can't do:
--   we can't define the Monoid instance for lists and have concat = mconcat
--   because that reduces to the wrong definition.

