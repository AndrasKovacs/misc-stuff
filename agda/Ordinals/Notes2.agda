{-# OPTIONS --postfix-projections --cubical #-}

open import Agda.Builtin.FromNat
open import Data.Nat hiding (_⊔_; _<_; _≤_)
open import Data.Unit hiding (_≤_)
open import Data.Empty
open import Function
open import Data.Sum
open import Level renaming (suc to lsuc; zero to lzero)
-- open import Relation.Binary.PropositionalEquality using (refl; _≡_)
-- import Relation.Binary.PropositionalEquality as Eq

open import Data.Product renaming (proj₁ to ₁; proj₂ to ₂)
open import Cubical.Core.Everything
import Cubical.Foundations.Prelude as P

instance
  Numberℕ : Number ℕ
  Numberℕ .Number.Constraint _ = ⊤
  Numberℕ .Number.fromNat    m = m

resolve : ∀ {i}{A : Set i}{{ _ : A}} → A
resolve {{a}} = a

tr  = P.subst;               {-# DISPLAY P.subst = tr  #-}
ap  = P.cong;                {-# DISPLAY P.cong  = ap  #-}
_⁻¹ = P.sym;   infix 6 _⁻¹;  {-# DISPLAY P.sym   = _⁻¹ #-}
_◾_ = P._∙_; infixr 5 _◾_;   {-# DISPLAY P._∙_   = _◾_ #-}

coe : ∀ {i}{A B : Set i} → A ≡ B → A → B
coe = tr id

open import Data.Maybe

iterℕ : ∀{i}{A : Set i} → ℕ → (A → A) → A → A
iterℕ zero    f = id
iterℕ (suc n) f = f ∘ iterℕ n f

--------------------------------------------------------------------------------
Fam = Σ Set λ A → A → Set

⊥ᶠ : Fam
⊥ᶠ = ⊥ , ⊥-elim

_+ᶠ_ : Fam → Fam → Fam; infixl 5 _+ᶠ_
F +ᶠ G = (F .₁ ⊎ G .₁) , [ F .₂ , G .₂ ]

_⇒ᶠ_ : Fam → Fam → Set; infixr 3 _⇒ᶠ_
F ⇒ᶠ G = Σ (F .₁ → G .₁) λ f → ∀ s → G .₂ (f s) → F .₂ s

data W (F : Fam) : Set where
  lim : (s : F .₁) → (F .₂ s → W F) → W F

Wmap : ∀ {F G} → F ⇒ᶠ G → W F → W G
Wmap (f , g) (lim s a) = lim (f s) (λ p → Wmap (f , g) (a (g s p)))

Bump : Fam → Fam
Bump (S , P) = Maybe S , maybe P (W (S , P))

U : ℕ → Fam
U zero    = ⊥ᶠ
U (suc n) = Bump (U n)

⇑ : ∀ {F} → W F → W (Bump F)
⇑ = Wmap (just , λ s z → z)

Ω : ∀ n → W (U (suc n))
Ω n = lim nothing ⇑

z : W (U 2)
z = lim (just nothing) λ {(lim () _)}

s : W (U 2) → W (U 2)
s a = lim nothing λ _ → a

iter : ∀ {n} → W (U n) → (W (U n) → W (U n)) → W (U n) → W (U n)
iter (lim s a) f b = lim s λ i → f (iter (a i) f b)

F : ∀ {n} → W (U (suc n)) → W (U n) → W (U n)
F (lim nothing  a) b = F (a b) b
F (lim (just s) a) b = lim s λ i → iter b (F (a i)) b

F↓ : ∀ {n} → W (U (suc (suc n))) → W (U 2)
F↓ {zero}  a = a
F↓ {suc n} a = F↓ {n} (F {suc (suc n)} a (Ω (suc n)))







-- data < {F} : W F → Set where
--   lim* : ∀ {s f} → F .₂ s → < (lim s f)
--   lim  : ∀ {s f p} → < (f p) → < (lim s f)

-- Bump : Fam → Fam
-- Bump F = sucᶠ (W F , <)

-- U : ℕ → Fam
-- U zero    = zeroᶠ
-- U (suc n) = Bump (U n)



-- -- ⇑ : ∀ {F} → W F → W (sucᶠ F)
-- -- ⇑ (lim s f) = lim (just s) (⇑ ∘ f)

-- Morph : Fam → Fam → Set
-- Morph (S , P) (S' , P') = Σ (S → S') λ f → ∀ s → P' (f s) → P s

-- wmap : ∀ {F G} → Morph F G → W F → W G
-- wmap (f , g) (lim s a) = lim (f s) (λ p → wmap (f , g) (a (g _ p)))

-- <map : ∀ {F G}(f : Morph F G) → ∀ a → < (wmap {F}{G} f a) → < a
-- <map (f , g) (lim s a) (lim* p)         = lim* (g s p)
-- <map (f , g) (lim s a) (lim {p = p} <a) = lim (<map (f , g) (a (g s p)) <a)

-- wmap2 : ∀ {F G} → Morph F G → Morph (W F , <) (W G , <)
-- wmap2 f = wmap f , <map f

-- -- sucᶠ is invariant in shapes!
-- smap : ∀ {F G} → Morph F G → Morph (sucᶠ F) (sucᶠ G)
-- smap (f , g) = (Data.Maybe.map f) , λ {nothing p → {!!}; (just x) p → g x p}

-- -- ⇑ : ∀ {n} → W (U n) → W (U (suc n))
-- -- ⇑ (lim s f) = lim (just {!!}) {!!}

-- -- f1 : W (U 0) → ⊥
-- -- f1 (lim () x)

-- f2 : W (U 1)
-- f2 = lim nothing (λ {(lim () _)})

-- Comp : ∀ {F G H} → Morph G H → Morph F G → Morph F H
-- Comp (f , g) (f' , g') = (f ∘ f') , λ s z → g' s (g (f' s) z)

-- justᶠ : ∀ {F} → Morph F (sucᶠ F)
-- justᶠ {S , P} = just , (λ s p → p)

-- -- foo : ∀ {F} → Morph F (Bump F)
-- -- foo F@{S , P} = Comp {F}{W F , <}{sucᶠ (W F , <)} justᶠ
-- --                 {!!}

-- foo : ∀ {n} → Morph (U n) (U (suc n))
-- foo {zero}  = (λ ()) , (λ ())
-- foo {suc n} = {!foo {n}!}


-- omega : ∀ n → W (U (suc n))
-- omega n = lim nothing (wmap foo)





-- < : ∀ {F} → W F → Set
-- < (lim s f) = ∃ λ p → Maybe (< (f p))


-- _<_ : ∀ {F} → W F → W F → Set; infix 3 _<_
-- _≤_ : ∀ {F} → W F → W F → Set; infix 3 _≤_
-- a < lim s b = ∃ λ p → a ≤ b p
-- a ≤ b       = a ≡ b ⊎ a < b

-- toFam : ∀ {F} → W F → Fam
-- toFam {F} a = (∃ (_< a)) , λ p → ∃ (_< p .₁)

-- ⇑ : ∀ {F} → W F → W (sucᶠ F)
-- ⇑ {S , P} (lim s a) = lim (just s) λ p → ⇑ {S , P} (a p)

-- fromFam : ∀ F → (F .₁ → W F) → W (sucᶠ F)
-- fromFam (S , P) foo = lim nothing λ s → ⇑ (foo s)

-- Lim : {A : Set} → (A → ∃ W) → ∃ W
-- Lim {A} f = {!₁ ∘ f!} , {!!}

-- Bump : ∃ W → ∃ W
-- Bump (F , a) = (sucᶠ (W F , ∃ ∘ flip _<_)) , (lim nothing {!!})

-- -- Ω : ∃ W → ∃ W
-- -- Ω (F , lim s f) = Bump (Lim λ p → Ω (F , f p))

-- Ω : ∃ W → Fam
-- Ω (F , lim s f) = limᶠ λ p → sucᶠ (W (Ω (_ , f p)) , ∃ ∘ flip _<_)



-- {!λ (p : P s) → Ω ((S , P) , f p)!}

-- luft : ∀ {F} → W (sucᶠ F) → W (W F , ∃ ∘ flip _<_)
-- luft {S , P} a = {!!}

-- blegh : ∀ {F } → W (sucᶠ F)
-- blegh {F} = lim nothing λ p → {!!}

-- Ωf : ∀ {F} → W F → Fam
-- Ωw : ∀ {F}(a : W F) → W (sucᶠ (Ωf a))
-- Ωf {S , P}(lim s a) = W (sucᶠ (limᶠ (Ωf ∘ a))) , ∃ ∘ flip _<_
-- Ωw {S , P}(lim s a) = lim nothing λ b → {!Ωw ∘ a!}

-- -- fromFam _ λ b → {!Ωw b!}

-- OMEGA : ∃ W → ∃ W
-- OMEGA (F , a) = sucᶠ (Ωf a) , Ωw a


-- open import Data.Fin using (zero; suc; Fin)

-- ω : Fam
-- ω = ℕ , Fin

-- z : W ω
-- z = lim 0 (λ ())

-- s : W ω → W ω
-- s a = lim 1 (λ _ → a)

-- Ω₀ = Ω z .₁

-- z₀ : Ω₀
-- z₀ = lim nothing λ ()

-- Ω₁ = Ω (s z) .₁

-- z₁ : Ω₁
-- z₁ = lim (just (zero , z₀)) λ ()

-- s₁ : Ω₁ → Ω₁
-- s₁ a = lim nothing (λ _ → a)

-- Ω₂ = Ω (s (s z)) .₁

-- limN : (Ω₁ → Ω₂) → Ω₂
-- limN a = lim nothing λ {(p , q) → a q}





-- Ω : ℕ → Fam
-- Ω zero    = zeroᶠ
-- Ω (suc n) = W (sucᶠ (Ω n)) , ∃ ∘ flip _<_
-- Ωω : Fam
-- Ωω = limᶠ Ω
-- foo = W (sucᶠ Ωω)





-- module Stuff where

--   ωᶠ : Fam
--   ωᶠ = limᶠ (λ n → iterℕ n sucᶠ zeroᶠ)

--   fin2ℕ : ∀ {n} → iterℕ n sucᶠ (⊥ , ⊥-elim) .₁ → ℕ
--   fin2ℕ {suc n} nothing = zero
--   fin2ℕ {suc n} (just x) = suc (fin2ℕ {n} x)

--   Ω₁ = W (sucᶠ ωᶠ)

--   z : Ω₁
--   z = lim (just (1 , nothing)) λ ()

--   lem : ∀ x → x < z → ⊥
--   lem x p = p .₁

--   s : Ω₁ → Ω₁
--   s a = lim (just (2 , nothing)) λ _ → a

--   limℕ : (ℕ → Ω₁) → Ω₁
--   limℕ a = lim nothing λ {(n , i) → a (fin2ℕ {n} i)}

--   ω : Ω₁
--   ω = limℕ λ n → iterℕ n s z


--   Ω₂ = W (sucᶠ (Ω₁ , ∃ ∘ flip _<_))

--   z' : Ω₂
--   z' = lim (just z) λ ()

--   s' : Ω₂ → Ω₂
--   s' a = lim (just (s z)) λ _ → a

--   -- OK
--   -- limℕ' : (ℕ → Ω₂) → Ω₂
--   -- limℕ' a = lim (just ω) λ { (i , (p , q) , r) → {!!}}

--   limΩ₁ : (Ω₁ → Ω₂) → Ω₂
--   limΩ₁ a = lim nothing a

--   Ω₃ = W (sucᶠ (Ω₂ , ∃ ∘ _<_))
