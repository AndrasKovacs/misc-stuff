

open import Data.String
open import Data.Bool

foo : (b : Bool) -> if b then String else Bool
foo false = true
foo true = "foo"

idfun : {a : Set} → a -> a
idfun x = x






























-- open import Data.Product
-- open import Data.Sum
-- open import Data.Unit
-- open import Function hiding (_⟨_⟩_)

-- ⊎elim :
--   ∀ {α β γ}{A : Set α}{B : Set β}(P : A ⊎ B → Set γ)
--   → (∀ a → P (inj₁ a))
--   → (∀ b → P (inj₂ b))
--   → ∀ x → P x
-- ⊎elim P f g (inj₁ x) = f x
-- ⊎elim P f g (inj₂ y) = g y

-- -- data P (I : Set) : Set₁ where
-- --   ret : I → F I

-- -- data F (I : Set) : Set₁ where
-- --   ret : I → F I
-- --   ind : I → F I → F I
-- --   arg : (A : Set) → (A → F I) → F I

-- -- open import Data.List
-- -- open import Data.Sum

-- -- F = List (List (

-- data Ty : Set₁ where
--   ι   : Ty
--   ι⇒_ : Ty → Ty
--   _⇒_ : Set → Ty → Ty

-- infixr 5 _⇒_

-- data Con : Set₁ where
--   ∙   : Con
--   _▶_ : Con → Ty → Con
-- infixl 4 _▶_

-- data Var : Con → Ty → Set where
--   vz : ∀ {Γ A} → Var (Γ ▶ A) A
--   vs : ∀ {Γ A B} → Var Γ A → Var (Γ ▶ B) A

-- data Tm (Γ : Con) : Ty → Set₁ where
--   var  : ∀ {A} → Var Γ A → Tm Γ A
--   appι : ∀ {A} → Tm Γ (ι⇒ A) → Tm Γ ι → Tm Γ A
--   app  : ∀ {A B} → Tm Γ (A ⇒ B) → A → Tm Γ B

-- ------------------------------------------------------------

-- Tyᶜ : Ty → Set → Set
-- Tyᶜ ι       X = X
-- Tyᶜ (ι⇒ A)  X = X → Tyᶜ A X
-- Tyᶜ (B ⇒ A) X = B → Tyᶜ A X

-- Conᶜ : Con → Set → Set
-- Conᶜ ∙       X = ⊤
-- Conᶜ (Γ ▶ A) X = Tyᶜ A X × Conᶜ Γ X

-- rec : ∀ {Γ A} → Tm Γ A → ∀ {X} → Conᶜ Γ X → Tyᶜ A X
-- rec (var vz)     γ = proj₁ γ
-- rec (var (vs x)) γ = rec (var x) (proj₂ γ)
-- rec (appι t u)   γ = rec t γ (rec u γ)
-- rec (app t u)    γ = rec t γ u

-- nat = Tm (∙ ▶ ι ▶ ι⇒ ι) ι

-- zero : nat
-- zero = var (vs vz)

-- suc : nat → nat
-- suc = appι (var vz)

-- foo : nat
-- foo = suc (suc (suc zero))

-- -- Conᴹ : Con →
-- -- ind : ∀ {Γ A}(Xᴹ : Tm Γ A → Set) →














-- -- data F : Set₁ where
-- --   I   : F
-- --   K   : Set → F
-- --   _+_ : F → F → F
-- --   _*_ : F → F → F

-- -- ⟦_⟧ : F → Set → Set
-- -- ⟦ I     ⟧ X = X
-- -- ⟦ K A   ⟧ X = A
-- -- ⟦ f + g ⟧ X = ⟦ f ⟧ X ⊎ ⟦ g ⟧ X
-- -- ⟦ f * g ⟧ X = ⟦ f ⟧ X × ⟦ g ⟧ X

-- -- Alg : F → Set → Set
-- -- Alg I       X = X → X
-- -- Alg (K A)   X = A → X
-- -- Alg (f + g) X = Alg f X × Alg g X
-- -- Alg (f * g) X = ⟦ f ⟧ X → Alg g X

-- -- foo : ∀ f A → (⟦ f ⟧ A → A) → Alg f A
-- -- foo I       A phi = phi
-- -- foo (K B)   A phi = phi
-- -- foo (f + g) A phi = foo f A (phi ∘ inj₁) , foo g A (phi ∘ inj₂)
-- -- foo (f * g) A phi = λ fa → foo g A (curry phi fa)

-- -- list : Set → F
-- -- list A = K ⊤ + (K A * I)



-- -- ⟦_⟧ : F → Set → Set
-- -- ⟦ I     ⟧ X = X
-- -- ⟦ K A   ⟧ X = A
-- -- ⟦ f + g ⟧ X = ⟦ f ⟧ X ⊎ ⟦ g ⟧ X
-- -- ⟦ f * g ⟧ X = ⟦ f ⟧ X × ⟦ g ⟧ X

-- -- data μ (f : F) : Set where
-- --   ⟨_⟩ : ⟦ f ⟧ (μ f) → μ f

-- -- ⟦_⟧ᴹ : (f : F)(A : Set)(Aᴹ : A → Set) → ⟦ f ⟧ A → Set
-- -- ⟦ I     ⟧ᴹ A Aᴹ x = Aᴹ x
-- -- ⟦ K B   ⟧ᴹ A Aᴹ x = ⊤
-- -- ⟦ f + g ⟧ᴹ A Aᴹ x = ⊎elim _ (⟦ f ⟧ᴹ A Aᴹ) (⟦ g ⟧ᴹ A Aᴹ) x
-- -- ⟦ f * g ⟧ᴹ A Aᴹ x = ⟦ f ⟧ᴹ A Aᴹ (proj₁ x) × ⟦ g ⟧ᴹ A Aᴹ (proj₂ x)

-- -- Alg : F → Set → Set
-- -- Alg I       X = X → X
-- -- Alg (K A)   X = A → X
-- -- Alg (f + g) X = Alg f X × Alg g X
-- -- Alg (f * g) X = ⟦ f ⟧ X → Alg g X

-- -- mutual
-- --   rec : ∀ {f}{A : Set} → Alg f A → μ f → A
-- --   rec {f} {A} alg ⟨ x ⟩ = rec' {f}{f}{A} alg {!!} x

-- --   rec' : ∀ {f g}{A : Set} → Alg f A → Alg g (μ f) → ⟦ g ⟧ (μ f) → A
-- --   rec' = {!!}

-- -- {!f X → (g X → X)!}

-- -- Alg f X ≡ f X → X

-- -- module _ (f : F)(fᴹ : Set)(⟨⟩ᴹ : ⟦ f ⟧ fᴹ → fᴹ) where
-- --   rec  : μ f → fᴹ
-- --   rec' : (g : F) → (⟦ g ⟧ fᴹ → fᴹ) → ⟦ g ⟧ (μ f) → fᴹ
-- --   rec ⟨ x ⟩            = rec' f ⟨⟩ᴹ x

-- --   rec' I         phi x = phi (rec x)
-- --   rec' (K A)     phi x = phi x
-- --   rec' (g₁ + g₂) phi (inj₁ x)  = {!!} -- rec' g₁ (phi ∘ inj₁) x
-- --   rec' (g₁ + g₂) phi (inj₂ x)  = rec' g₂ (phi ∘ inj₂) x
-- --   rec' (g₁ * g₂) phi (x₁ , x₂) = {!!}

--   -- rec' :
--   --   (f g : F)
--   --   (gᴹ : Set)
--   --   → (⟦ f ⟧ gᴹ → gᴹ)
--   --   → ⟦ f ⟧ (μ g) → gᴹ
--   -- rec' I         g gᴹ m x = {!rec g gᴹ!}
--   -- rec' (K A)     g gᴹ m x = m x
--   -- rec' (f₁ + f₂) g gᴹ m x = {!!}
--   -- rec' (f₁ * f₂) g gᴹ m x = {!!}

--   -- rec :
--   --   (f : F)
--   --   (fᴹ : Set)
--   --   → (⟦ f ⟧ fᴹ → fᴹ)
--   --   → μ f → fᴹ
--   -- rec f fᴹ m ⟨ x ⟩ = rec' f f fᴹ m x


--   -- map (rec f fᴹ m) : ⟦ f ⟧ (μ f) → ⟦ f ⟧ fᴹ

--   -- ind' :
--   --    (f g : F)
--   --    (μfᴹ : ⟦ f ⟧ (μ g) → Set)
--   --    (μgᴹ : μ g → Set) →
--   --    (∀ x → ⟦ f ⟧ᴹ (μ g) μgᴹ x → μfᴹ x)
--   --    → ∀ x → μfᴹ x
--   -- ind' I         g μfᴹ μgᴹ m x = m x (ind g μgᴹ {!!} x)
--   -- ind' (K A)     g μfᴹ μgᴹ m x = m x tt
--   -- ind' (f₁ + f₂) g μfᴹ μgᴹ m x = {!!}
--   -- ind' (f₁ * f₂) g μfᴹ μgᴹ m x =
--   --   m _ (ind' f₁ g (⟦ f₁ ⟧ᴹ (μ g) μgᴹ) μgᴹ (λ _ xᴹ → xᴹ) (proj₁ x) ,
--   --        ind' f₂ g (⟦ f₂ ⟧ᴹ (μ g) μgᴹ) μgᴹ (λ _ xᴹ → xᴹ) (proj₂ x))

--   -- ind :
--   --    (f : F)
--   --    (μfᴹ : μ f → Set) →
--   --    (∀ x → ⟦ f ⟧ᴹ (μ f) μfᴹ x → μfᴹ ⟨ x ⟩)
--   --    → ∀ x → μfᴹ x
--   -- ind f μfᴹ m ⟨ x ⟩ = ind' f f (μfᴹ ∘ ⟨_⟩) μfᴹ m x

-- -- fmapᴹ : (f : F)(A : Set)(Aᴹ : A → Set) → (∀ x → Aᴹ x) → (fa : ⟦ f ⟧ A) → ⟦ f ⟧ᴹ A Aᴹ fa
-- -- fmapᴹ I       A Aᴹ foo fa = foo fa
-- -- fmapᴹ (K B)   A Aᴹ foo fa = tt
-- -- fmapᴹ (f + g) A Aᴹ foo fa = ⊎elim (⊎elim (λ v → Set) (⟦ f ⟧ᴹ A Aᴹ) (⟦ g ⟧ᴹ A Aᴹ))
-- --                               (fmapᴹ f A Aᴹ foo)
-- --                               (fmapᴹ g A Aᴹ foo) fa
-- -- fmapᴹ (f * g) A Aᴹ foo fa = fmapᴹ f A Aᴹ foo (proj₁ fa) , fmapᴹ g A Aᴹ foo (proj₂ fa)

-- -- {-# TERMINATING #-}
-- -- ind : (f : F)(μfᴹ : μ f → Set) →
-- --    ((x : ⟦ f ⟧ (μ f)) →  ⟦ f ⟧ᴹ (μ f) μfᴹ x → μfᴹ ⟨ x ⟩)
-- --    → ∀ x → μfᴹ x
-- -- ind f μfᴹ ⟨⟩ᴹ ⟨ x ⟩ = ⟨⟩ᴹ x (fmapᴹ f (μ f) μfᴹ (ind f μfᴹ ⟨⟩ᴹ) x)
