
import Data.Unit as L
open import Data.Product hiding (curry; uncurry)
open import Data.Sum
open import Data.Empty
open import Level
open import Function

data Kind : Set where
  U : Kind
  _⇒_ : Kind → Kind → Kind

infixr 4 _⇒_
infixl 7 _∙_

data Ty : Kind → Set where
  ⊤    : Ty U
  K    : ∀ {a b} → Ty a → Ty b → Ty a
  S    : ∀ {a b c} → Ty (c ⇒ a ⇒ b) → Ty (c ⇒ a) → Ty (c ⇒ b)
  _∙_  : ∀ {a b} → Ty (a ⇒ b) → Ty a → Ty b
  Prod : Ty U → Ty U → Ty U
  Sum  : Ty U → Ty U → Ty U
  μ    : ∀ {a} → Ty (a ⇒ a) → Ty a

-- I : ∀ {a} → Ty (a ⇒ a)
-- I {a} = S ∙ K ∙ K {b = a}

-- _⊙_ : ∀ {a b c} → Ty (b ⇒ c) → Ty (a ⇒ b) → Ty (a ⇒ c)
-- f ⊙ g = S ∙ (K ∙ f) ∙ g

-- Prodₖ : ∀ {a} → Ty (a ⇒ a ⇒ a)
-- Prodₖ {U}     = Prod
-- Prodₖ {a ⇒ b} = S ∙ (K ∙ S) ∙ (S ∙ (K ∙ Prodₖ))

-- Sumₖ : ∀ {a} → Ty (a ⇒ a ⇒ a)
-- Sumₖ {U}     = Sum
-- Sumₖ {a ⇒ b} = S ∙ (K ∙ S) ∙ (S ∙ (K ∙ Sumₖ))

-- _*ₖ_ : ∀ {a} → Ty a → Ty a → Ty a
-- f *ₖ g = Prodₖ ∙ f ∙ g

-- _+ₖ_ : ∀ {a} → Ty a → Ty a → Ty a
-- f +ₖ g = Sumₖ ∙ f ∙ g

-- --------------------------------------------------------------------------------

⟦_⟧ᴷ : Kind → Set₁
⟦ U     ⟧ᴷ = Set
⟦ a ⇒ b ⟧ᴷ = ⟦ a ⟧ᴷ → ⟦ b ⟧ᴷ

⟦_⟧ᴷ' : Kind → Set₁
⟦ U     ⟧ᴷ' = Lift L.⊤
⟦ a ⇒ b ⟧ᴷ' = ⟦ a ⟧ᴷ × ⟦ b ⟧ᴷ'

uncurry : ∀ {k} → ⟦ k ⟧ᴷ → ⟦ k ⟧ᴷ' → Set
uncurry {U    } ⟦k⟧ args         = ⟦k⟧
uncurry {a ⇒ b} ⟦k⟧ (⟦a⟧ , args) = uncurry (⟦k⟧ ⟦a⟧) args

curry : ∀ {k} → (⟦ k ⟧ᴷ' → Set) → ⟦ k ⟧ᴷ
curry {U    } f = f (lift L.tt)
curry {a ⇒ b} f = λ ⟦a⟧ → curry (λ ⟦b⟧ → f (⟦a⟧ , ⟦b⟧))

mutual
  ⟦_⟧ : ∀ {a} → Ty a → ⟦ a ⟧ᴷ
  ⟦ ⊤        ⟧ = L.⊤
  ⟦ K a b    ⟧ = ⟦ a ⟧
  ⟦ S f g    ⟧ = λ x → ⟦ f ⟧ x (⟦ g ⟧ x)
  ⟦ A ∙ B    ⟧ = ⟦ A ⟧ ⟦ B ⟧
  ⟦ Prod a b ⟧ = ⟦ a ⟧ × ⟦ b ⟧
  ⟦ Sum  a b ⟧ = ⟦ a ⟧ ⊎ ⟦ b ⟧
  ⟦ μ F      ⟧ = curry (Fix F)

  data Fix {k}(F : Ty (k ⇒ k))(A : ⟦ k ⟧ᴷ') : Set where
    ⟨_⟩ : uncurry (⟦ F ⟧ (curry (Fix F))) A → Fix F A

--------------------------------------------------------------------------------

Kindᵀ : Kind → Set
Kindᵀ U       = Ty U → Ty U
Kindᵀ (a ⇒ b) = Ty a → Kindᵀ b

Tyᵀ : ∀ {k} → Ty k → Kindᵀ k
Tyᵀ ⊤          = id
Tyᵀ (K a b)    = Tyᵀ a
Tyᵀ (S f g)    = λ c → Tyᵀ f c (g ∙ c)
Tyᵀ (a ∙ b)    = Tyᵀ a b
Tyᵀ (Sum a b)  = λ x → Prod (Tyᵀ a x) (Tyᵀ b x)
Tyᵀ (Prod a b) = λ x → Tyᵀ a (Tyᵀ b x)
Tyᵀ (μ a)      = {!!}











-- import Data.Unit as L
-- open import Data.Product hiding (curry; uncurry)
-- open import Data.Sum
-- open import Data.Empty
-- open import Level
-- open import Function

-- data Kind : Set where
--   U : Kind
--   _⇒_ : Kind → Kind → Kind

-- infixr 4 _⇒_
-- infixl 7 _∙_

-- data Ty : Kind → Set where
--   ⊤    : Ty U
--   K    : ∀ {a b} → Ty (a ⇒ b ⇒ a)
--   S    : ∀ {a b c} → Ty ((c ⇒ a ⇒ b) ⇒ (c ⇒ a) ⇒ c ⇒ b)
--   _∙_  : ∀ {a b} → Ty (a ⇒ b) → Ty a → Ty b
--   Prod : Ty (U ⇒ U ⇒ U)
--   Sum  : Ty (U ⇒ U ⇒ U)
--   μ    : ∀ {a} → Ty (a ⇒ a) → Ty a

-- I : ∀ {a} → Ty (a ⇒ a)
-- I {a} = S ∙ K ∙ K {b = a}

-- _⊙_ : ∀ {a b c} → Ty (b ⇒ c) → Ty (a ⇒ b) → Ty (a ⇒ c)
-- f ⊙ g = S ∙ (K ∙ f) ∙ g

-- Prodₖ : ∀ {a} → Ty (a ⇒ a ⇒ a)
-- Prodₖ {U}     = Prod
-- Prodₖ {a ⇒ b} = S ∙ (K ∙ S) ∙ (S ∙ (K ∙ Prodₖ))

-- Sumₖ : ∀ {a} → Ty (a ⇒ a ⇒ a)
-- Sumₖ {U}     = Sum
-- Sumₖ {a ⇒ b} = S ∙ (K ∙ S) ∙ (S ∙ (K ∙ Sumₖ))

-- _*ₖ_ : ∀ {a} → Ty a → Ty a → Ty a
-- f *ₖ g = Prodₖ ∙ f ∙ g

-- _+ₖ_ : ∀ {a} → Ty a → Ty a → Ty a
-- f +ₖ g = Sumₖ ∙ f ∙ g

-- --------------------------------------------------------------------------------

-- ⟦_⟧ᴷ : Kind → Set₁
-- ⟦ U     ⟧ᴷ = Set
-- ⟦ a ⇒ b ⟧ᴷ = ⟦ a ⟧ᴷ → ⟦ b ⟧ᴷ

-- ⟦_⟧ᴷ' : Kind → Set₁
-- ⟦ U     ⟧ᴷ' = Lift L.⊤
-- ⟦ a ⇒ b ⟧ᴷ' = ⟦ a ⟧ᴷ × ⟦ b ⟧ᴷ'

-- uncurry : ∀ {k} → ⟦ k ⟧ᴷ → ⟦ k ⟧ᴷ' → Set
-- uncurry {U    } ⟦k⟧ args         = ⟦k⟧
-- uncurry {a ⇒ b} ⟦k⟧ (⟦a⟧ , args) = uncurry (⟦k⟧ ⟦a⟧) args

-- curry : ∀ {k} → (⟦ k ⟧ᴷ' → Set) → ⟦ k ⟧ᴷ
-- curry {U    } f = f (lift L.tt)
-- curry {a ⇒ b} f = λ ⟦a⟧ → curry (λ ⟦b⟧ → f (⟦a⟧ , ⟦b⟧))

-- mutual
--   ⟦_⟧ : ∀ {a} → Ty a → ⟦ a ⟧ᴷ
--   ⟦ ⊤     ⟧ = L.⊤
--   ⟦ K     ⟧ = const
--   ⟦ S     ⟧ = _ˢ_
--   ⟦ A ∙ B ⟧ = ⟦ A ⟧ ⟦ B ⟧
--   ⟦ Prod  ⟧ = _×_
--   ⟦ Sum   ⟧ = _⊎_
--   ⟦ μ F   ⟧ = curry (Fix F)

--   data Fix {k}(F : Ty (k ⇒ k))(A : ⟦ k ⟧ᴷ') : Set where
--     ⟨_⟩ : uncurry (⟦ F ⟧ (curry (Fix F))) A → Fix F A






-- Kindᵀ : Kind → Set₁
-- Kindᵀ U       = Set → Set
-- Kindᵀ (a ⇒ b) = Kindᵀ a → Kindᵀ b

-- Kindᵀ' : Kind → Set₁
-- Kindᵀ' U       = Set
-- Kindᵀ' (a ⇒ b) = Kindᵀ a × Kindᵀ' b

-- uncurryᵀ : ∀ {k} → Kindᵀ k → Kindᵀ' k → Set
-- uncurryᵀ {U}     kᵀ args        = kᵀ args
-- uncurryᵀ {a ⇒ b} kᵀ (aᵀ , args) = uncurryᵀ (kᵀ aᵀ) args

-- curryᵀ : ∀ {k} → (Kindᵀ' k → Set) → Kindᵀ k
-- curryᵀ {U}     f = f
-- curryᵀ {a ⇒ b} f = λ aᵀ → curryᵀ {b} (λ args → f (aᵀ , args))

-- mutual
--   Tyᵀ : {k : Kind} → Ty k → Kindᵀ k
--   Tyᵀ ⊤       = id
--   Tyᵀ K       = const
--   Tyᵀ S       = _ˢ_
--   Tyᵀ (f ∙ a) = Tyᵀ f (Tyᵀ a)
--   Tyᵀ Prod    = λ A B X → A (B X)
--   Tyᵀ Sum     = λ A B X → A X × B X
--   Tyᵀ (μ a)   = curryᵀ (μᵀ a)

--   record μᵀ {k}(a : Ty (k ⇒ k)) (A : Kindᵀ' k) : Set where
--     coinductive
--     field unfold : uncurryᵀ (Tyᵀ a (curryᵀ (μᵀ a))) A

-- lookup :
--   ∀ {k : Kind}{B : ⟦ k ⟧ᴷ' → Set}{a : Ty k}
--   → ∀ {args} → uncurryᵀ {k} (Tyᵀ a) {!!} → uncurry ⟦ a ⟧ args → B args
-- lookup = {!!}


-- mutual
--   lookup : ∀ a {B} → *ᵀ a B → (⟦ a ⟧ → B)
--   lookup ⊤     t i        = t
--   lookup (μ f) t (fold i) = lookupF f f (t .unfold) i 

--   lookupF : ∀ f g {B} → Fᵀ f (μ g) B → ⟦ f ⟧ᶠ (Fix g) → B
--   lookupF I       h t (fold i)  = lookupF h h (t .unfold) i 
--   lookupF (K a)   h t i         = lookup a t i
--   lookupF (f + g) h t (inl i)   = lookupF f h (t .proj₁) i
--   lookupF (f + g) h t (inr i)   = lookupF g h (t .proj₂) i  
--   lookupF (f × g) h t (i₁ , i₂) = lookupF g h (lookupF f h t i₁) i₂

-- mutual
--   tabulate : ∀ a {B} → (⟦ a ⟧ → B) → *ᵀ a B
--   tabulate ⊤     g = g tt
--   tabulate (μ f) g .unfold = tabulateF f f (g ∘ fold)

--   {-# TERMINATING #-} -- Agda plz
--   tabulateF : ∀ f g {B} → (⟦ f ⟧ᶠ (Fix g) → B) → Fᵀ f (μ g) B
--   tabulateF I       h j .unfold = tabulateF h h (j ∘ fold)
--   tabulateF (K a)   h j = tabulate a j
--   tabulateF (f + g) h j = tabulateF f h (j ∘ inl) , tabulateF g h (j ∘ inr)
--   tabulateF (f × g) h j = tabulateF f h λ i₁ → tabulateF g h λ i₂ → j (i₁ , i₂)



-- import Data.Unit as L
-- open import Data.Product hiding (curry; uncurry)
-- open import Data.Sum
-- open import Data.Empty
-- open import Level

-- data Kind : Set where
--   U : Kind
--   _⇒_ : Kind → Kind → Kind

-- infixr 4 _⇒_
-- infixl 7 _∙_

-- data Ty : Kind → Set where
--   ⊤   : Ty U
--   K   : ∀ {a b} → Ty (a ⇒ b ⇒ a)
--   S   : ∀ {a b c} → Ty ((c ⇒ a ⇒ b) ⇒ (c ⇒ a) ⇒ c ⇒ b)
--   _∙_ : ∀ {a b} → Ty (a ⇒ b) → Ty a → Ty b
--   _*_ : ∀ {a} → Ty (a ⇒ a ⇒ a)
--   _+_ : ∀ {a} → Ty (a ⇒ a ⇒ a)
--   μ   : ∀ {a} → Ty (a ⇒ a) → Ty a

-- infixr 6 _*_
-- infixr 5 _+_

-- I : ∀ {a} → Ty (a ⇒ a)
-- I {a} = S ∙ K ∙ K {b = a}

-- ⟦_⟧ᴷ : Kind → Set₁
-- ⟦ U     ⟧ᴷ = Set
-- ⟦ a ⇒ b ⟧ᴷ = ⟦ a ⟧ᴷ → ⟦ b ⟧ᴷ

-- ⟦_⟧ᴷ' : Kind → Set₁
-- ⟦ U     ⟧ᴷ' = Lift L.⊤
-- ⟦ a ⇒ b ⟧ᴷ' = ⟦ a ⟧ᴷ × ⟦ b ⟧ᴷ'

-- uncurry : ∀ {k} → ⟦ k ⟧ᴷ → ⟦ k ⟧ᴷ' → Set
-- uncurry {U    } ⟦k⟧ args         = ⟦k⟧
-- uncurry {a ⇒ b} ⟦k⟧ (⟦a⟧ , args) = uncurry (⟦k⟧ ⟦a⟧) args

-- curry : ∀ {k} → (⟦ k ⟧ᴷ' → Set) → ⟦ k ⟧ᴷ
-- curry {U    } f = f (lift L.tt)
-- curry {a ⇒ b} f = λ ⟦a⟧ → curry (λ ⟦b⟧ → f (⟦a⟧ , ⟦b⟧))

-- mutual
--   ⟦_⟧ : ∀ {a} → Ty a → ⟦ a ⟧ᴷ
--   ⟦ ⊤           ⟧ = L.⊤
--   ⟦ K           ⟧ = λ a b → a
--   ⟦ S           ⟧ = λ f g x → f x (g x)
--   ⟦ A ∙ B       ⟧ = ⟦ A ⟧ ⟦ B ⟧
--   ⟦ _*_ {U}     ⟧ = _×_
--   ⟦ _*_ {a ⇒ b} ⟧ = λ F G x → ⟦ _*_ ⟧ (F x) (G x)
--   ⟦ _+_ {U}     ⟧ = _⊎_
--   ⟦ _+_ {a ⇒ b} ⟧ = λ F G x → ⟦ _+_ ⟧ (F x) (G x)
--   ⟦ μ F         ⟧ = curry (Fix F)

--   data Fix {k}(F : Ty (k ⇒ k))(A : ⟦ k ⟧ᴷ') : Set where
--     ⟨_⟩ : uncurry (⟦ F ⟧ (curry (Fix F))) A → Fix F A

-- Kindᵀ : Kind → Set₁
-- Kindᵀ U       = Set → Set
-- Kindᵀ (a ⇒ b) = Kindᵀ a → Kindᵀ b

-- Kindᵀ' : Kind → Set₁
-- Kindᵀ' U       = Set
-- Kindᵀ' (a ⇒ b) = Kindᵀ a × Kindᵀ' b

-- uncurryᵀ : ∀ {k} → Kindᵀ k → Kindᵀ' k → Set
-- uncurryᵀ {U}     kᵀ args        = kᵀ args
-- uncurryᵀ {a ⇒ b} kᵀ (aᵀ , args) = uncurryᵀ (kᵀ aᵀ) args

-- curryᵀ : ∀ {k} → (Kindᵀ' k → Set) → Kindᵀ k
-- curryᵀ {U}     f = f
-- curryᵀ {a ⇒ b} f = λ aᵀ → curryᵀ {b} (λ args → f (aᵀ , args))

-- mutual
--   Tyᵀ : {k : Kind} → Ty k → Kindᵀ k
--   Tyᵀ ⊤             = λ A → A
--   Tyᵀ K             = λ A _ → A
--   Tyᵀ S             = λ F G X → F X (G X)
--   Tyᵀ (f ∙ a)       = Tyᵀ f (Tyᵀ a)
--   Tyᵀ (_*_ {U})     = λ A B X → A (B X)
--   Tyᵀ (_*_ {a ⇒ b}) = λ A B X → Tyᵀ (_*_ {b}) (A X) (B X)
--   Tyᵀ (_+_ {U})     = λ A B X → A X × B X
--   Tyᵀ (_+_ {a ⇒ b}) = λ A B X → Tyᵀ (_+_ {b}) (A X) (B X)
--   Tyᵀ (μ a)         = curryᵀ (μᵀ a)

--   record μᵀ {k}(a : Ty (k ⇒ k)) (A : Kindᵀ' k) : Set where
--     coinductive
--     field unfold : uncurryᵀ (Tyᵀ a (curryᵀ (μᵀ a))) A

-- lookup : ∀ {k : Kind}{a : Ty k} → ∀ args → uncurryᵀ {k} (Tyᵀ a) args → {!⟦ a ⟧!}
-- lookup = {!!}


-- -- mutual
-- --   lookup : ∀ a {B} → *ᵀ a B → (⟦ a ⟧ → B)
-- --   lookup ⊤     t i        = t
-- --   lookup (μ f) t (fold i) = lookupF f f (t .unfold) i 

-- --   lookupF : ∀ f g {B} → Fᵀ f (μ g) B → ⟦ f ⟧ᶠ (Fix g) → B
-- --   lookupF I       h t (fold i)  = lookupF h h (t .unfold) i 
-- --   lookupF (K a)   h t i         = lookup a t i
-- --   lookupF (f + g) h t (inl i)   = lookupF f h (t .proj₁) i
-- --   lookupF (f + g) h t (inr i)   = lookupF g h (t .proj₂) i  
-- --   lookupF (f × g) h t (i₁ , i₂) = lookupF g h (lookupF f h t i₁) i₂

-- -- mutual
-- --   tabulate : ∀ a {B} → (⟦ a ⟧ → B) → *ᵀ a B
-- --   tabulate ⊤     g = g tt
-- --   tabulate (μ f) g .unfold = tabulateF f f (g ∘ fold)

-- --   {-# TERMINATING #-} -- Agda plz
-- --   tabulateF : ∀ f g {B} → (⟦ f ⟧ᶠ (Fix g) → B) → Fᵀ f (μ g) B
-- --   tabulateF I       h j .unfold = tabulateF h h (j ∘ fold)
-- --   tabulateF (K a)   h j = tabulate a j
-- --   tabulateF (f + g) h j = tabulateF f h (j ∘ inl) , tabulateF g h (j ∘ inr)
-- --   tabulateF (f × g) h j = tabulateF f h λ i₁ → tabulateF g h λ i₂ → j (i₁ , i₂)


