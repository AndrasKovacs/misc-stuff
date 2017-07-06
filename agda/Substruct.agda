
open import Lib

------------------------------------------------------------
-- β reduction for ordered LC

data Ty : Set where
  ι : Ty
  _⊸_ : Ty → Ty → Ty
  -- _⊗_ : Ty → Ty → Ty  
infixr 4 _⊸_
-- infixr 5 _⊗_

data Con : Set where
  ∙   : Con
  _▷_ : Con → Ty → Con
infixl 5 _▷_

_++_ : Con → Con → Con
Γ ++ ∙       = Γ
Γ ++ (Δ ▷ A) = (Γ ++ Δ) ▷ A
infixr 5 _++_

∙++ : ∀ Γ → ∙ ++ Γ ≡ Γ
∙++ ∙       = refl
∙++ (Γ ▷ A) = (_▷ A) & ∙++ Γ

data Tm : Con → Ty → Set where
  var   : ∀ {A} → Tm (∙ ▷ A) A
  -- ⟨_,_⟩ : ∀ {Γ Δ A B} → Tm Γ A → Tm Δ B → Tm (Γ ++ Δ) (A ⊗ B)
  -- split : ∀ {Γ Δ A B C} → Tm Γ (A ⊗ B) → Tm (Δ ▷ A ▷ B) C → Tm (Γ ++ Δ) C
  lam   : ∀ {Γ A B} → Tm (Γ ▷ A) B → Tm Γ (A ⊸ B)
  app   : ∀ {Γ Δ A B} → Tm Γ (A ⊸ B) → Tm Δ A → Tm (Γ ++ Δ) B

test : Tm ∙ ((ι ⊸ ι ⊸ ι) ⊸ ι ⊸ ι ⊸ ι)
test = lam (lam (app var var))

▷-inj : ∀ {Γ Δ A B} → (Γ ▷ A) ≡ (Δ ▷ B) → (Γ ≡ Δ) × (A ≡ B)
▷-inj refl = refl , refl

data _∈_ A : Con → Set where
  vz : ∀ {Γ} → A ∈ (Γ ▷ A)
  vs : ∀ {Γ B} → A ∈ Γ → A ∈ (Γ ▷ B)

graft : ∀ Γ {A} → A ∈ Γ → Con → Con
graft ∙ () Δ
graft (Γ ▷ A) vz     Δ = Γ ++ Δ
graft (Γ ▷ A) (vs x) Δ = graft Γ x Δ ▷ A

instᵛ : ∀ {B Δ A} (x : A ∈ (∙ ▷ B))(t' : Tm Δ A) → Tm (graft (∙ ▷ B) x Δ) B
instᵛ {B}{Δ} vz t' = coe ((λ x → Tm x B) & (∙++ Δ ⁻¹)) t'
instᵛ (vs ()) t'

∈++ : ∀ {Γ A} Δ → A ∈ (Γ ++ Δ) → (A ∈ Γ) ⊎ (A ∈ Δ)
∈++ ∙     x = inl x
∈++ (Δ ▷ A) vz     = inr vz
∈++ (Δ ▷ A) (vs x) with ∈++ Δ x
... | inl x' = inl x'
... | inr x' = inr (vs x')

++assoc : ∀ Γ Δ Σ → (Γ ++ Δ) ++ Σ ≡ Γ ++ Δ ++ Σ
++assoc Γ Δ ∙       = refl
++assoc Γ Δ (Σ ▷ A) = (_▷ A) & ++assoc Γ Δ Σ

choose :
  ∀ {Γ A} Δ Σ (x : A ∈ (Γ ++ Δ))
  → graft (Γ ++ Δ) x Σ
  ≡ either (λ x' → graft Γ x' Σ ++ Δ)
           (λ x' → Γ ++ graft Δ x' Σ) (∈++ Δ x)
choose ∙ _ x = refl
choose {Γ}(Δ ▷ A) Σ vz = ++assoc Γ Δ Σ
choose {Γ}(Δ ▷ A) Σ (vs x) with ∈++ Δ x | choose Δ Σ x
... | inl x' | hyp = (_▷ A) & hyp
... | inr x' | hyp = (_▷ A) & hyp

inst : ∀ {Γ Δ A B}(x : A ∈ Γ) → Tm Δ A → Tm Γ B → Tm (graft Γ x Δ) B
inst {Δ = Δ} {A} {B} x t' var = instᵛ x t'
inst {Γ} {Δ} {A₁} x t' (lam {A = A} {B} t) = lam (inst (vs x) t' t)
inst {Δ = Σ} {A} {B} x t' (app {Γ} {Δ} {A₁} t u)
  with ∈++ Δ x | choose Δ Σ x
... | inl x' | p = coe ((λ x → Tm x B) & (p ⁻¹)) (app (inst x' t' t) u)
... | inr x' | p = coe ((λ x → Tm x B) & (p ⁻¹)) (app t (inst x' t' u))

data _~_ : ∀ {Γ A} → Tm Γ A → Tm Γ A → Set where
  β : ∀ {Γ Δ A B}(t : Tm (Γ ▷ A) B) (u : Tm Δ A) → app (lam t) u ~ inst vz u t


-- inst : ∀ {Γ Δ A B} → Tm Γ A → Δ ≡ (Γ ▷ A) → Tm Δ B → Tm Γ B
-- inst = {!!}

-- inst t' p var       = coe (Tm _ & (proj₂ (▷-inj p) ⁻¹)) t'
-- inst {Γ} {A = A} t' refl (lam {A = A₁} {B} t) = {!!}
-- inst {Γ} t' p (app {Δ} {Σ} t u) = {!!}

-- data Sub Γ : Con → Set where
--   ∙   : Sub Γ ∙
--   _▷_ : ∀ {A Δ} → Sub Γ Δ → Tm Γ A → Sub Γ (Δ ▷ A)

-- π₂ : ∀ {Γ Δ A} → Sub Γ (Δ ▷ A) → Tm Γ A
-- π₂ (σ ▷ t) = t

-- splitˢ : ∀ {Γ Δ Σ} → Sub Γ (Δ ++ Σ) → Sub Γ Δ × Sub Γ Σ
-- splitˢ         {Σ = ∙} σ       = σ , ∙
-- splitˢ {Γ} {Δ} {Σ ▷ A} (σ ▷ t) = let a , b = splitˢ {Γ}{Δ}{Σ} σ in a , (b ▷ t)

-- Tmₛ : ∀ {Γ Δ A} → Sub Γ Δ → Tm Δ A → Tm Γ A
-- Tmₛ σ var       = π₂ σ
-- Tmₛ σ (lam t)   = lam (Tmₛ ({!!} ▷ {!!}) t)
-- Tmₛ {Γ} σ (app {Δ} {Σ} t u) = let σ₁ , σ₂ = splitˢ {Γ}{Δ}{Σ} σ in {!Tmₛ σ₁ t!}


-- data OPE : Con → Con → Set where
--   ∙    : OPE ∙ ∙
--   keep : ∀ {Γ Δ A} → OPE Γ Δ → OPE (Γ ▷ A) (Δ ▷ A)
--   drop : ∀ {Γ Δ A} → OPE Γ Δ → OPE (Γ ▷ A) Δ

-- Tmₑ : ∀ {Γ Δ A} → OPE Γ Δ → Tm Δ A → Tm Γ A
-- Tmₑ σ var       = {!!}
-- Tmₑ σ (lam t)   = {!!}
-- Tmₑ σ (app t u) = {!!}
  
-- data _~>_ : ∀ {Γ A} → Tm Γ A → Tm Γ A → Set where
--   β : ∀ {Γ Δ A B}{t : Tm (Γ ▷ A) B}{a : Tm Δ A} → app (lam t) a ~> {!!}

-- mutual
--   data Nf Γ : Ty → Set where
--     lam : ∀ {A B} → Nf (Γ ▷ A) B → Nf Γ (A ⊸ B)
--     ne  : Ne Γ ι → Nf Γ ι

--   data Ne : Con → Ty → Set where
--     var : ∀ {A} → Ne (∙ ▷ A) A
--     app : ∀ {Γ Δ A B} → Ne Γ (A ⊸ B) → Nf Δ A → Ne (Γ ++ Δ) B

-- std model
------------------------------------------------------------

⟦_⟧ : Ty → Set
⟦ ι     ⟧ = ⊥
⟦ A ⊸ B ⟧ = ⟦ A ⟧ → ⟦ B ⟧
-- ⟦ A ⊗ B ⟧ = ⟦ A ⟧ × ⟦ B ⟧

⟦_⟧ᶜ : Con → Set
⟦ ∙     ⟧ᶜ = ⊤
⟦ Γ ▷ A ⟧ᶜ = ⟦ Γ ⟧ᶜ × ⟦ A ⟧

⟦++⟧ : ∀ {Γ Δ} → ⟦ Γ ++ Δ ⟧ᶜ → ⟦ Γ ⟧ᶜ × ⟦ Δ ⟧ᶜ
⟦++⟧ {Γ} {∙}     γ = γ , tt
⟦++⟧ {Γ} {Δ ▷ A} γ =
  let a , b = ⟦++⟧ (proj₁ γ) in a , b , proj₂ γ

⟦_⟧ᵗ : ∀ {Γ A} → Tm Γ A → ⟦ Γ ⟧ᶜ → ⟦ A ⟧
⟦ var       ⟧ᵗ ⟦Γ⟧  = proj₂ ⟦Γ⟧
⟦ lam t     ⟧ᵗ ⟦Γ⟧  = λ ⟦a⟧ → ⟦ t ⟧ᵗ (⟦Γ⟧ , ⟦a⟧)
-- ⟦ split t u ⟧ᵗ ⟦ΓΔ⟧ =
--   let ⟦Γ⟧ , ⟦Δ⟧ = ⟦++⟧ ⟦ΓΔ⟧; ⟦A⟧ , ⟦B⟧ = ⟦ t ⟧ᵗ ⟦Γ⟧ in ⟦ u ⟧ᵗ ((⟦Δ⟧ , ⟦A⟧) , ⟦B⟧)
-- ⟦ ⟨ t , u ⟩ ⟧ᵗ ⟦ΓΔ⟧ =
--   let ⟦Γ⟧ , ⟦Δ⟧ = ⟦++⟧ ⟦ΓΔ⟧ in (⟦ t ⟧ᵗ ⟦Γ⟧) , ⟦ u ⟧ᵗ ⟦Δ⟧
⟦ app t u   ⟧ᵗ ⟦ΓΔ⟧ =
  let ⟦Γ⟧ , ⟦Δ⟧ = ⟦++⟧ ⟦ΓΔ⟧ in ⟦ t ⟧ᵗ ⟦Γ⟧ (⟦ u ⟧ᵗ ⟦Δ⟧) 

--------------------------------------------------------------------------------
-- Simply Typed Rig

-- data Mult : Set where -- multiplicity
--   ₀ ₁ ω : Mult

-- _*_ : Mult → Mult → Mult
-- ₀ * n = ₀
-- ₁ * n = n
-- ω * ₀ = ₀
-- ω * ₁ = ω
-- ω * ω = ω

-- _+_ : Mult → Mult → Mult
-- ₀ + n = n
-- ₁ + ₀ = ₁
-- ₁ + ₁ = ω
-- ₁ + ω = ω
-- ω + n = ω

-- data Ty : Set where
--   ι : Ty
--   _,_⇒_ : Mult → Ty → Ty → Ty
-- infixr 4 _,_⇒_

-- infixl 4 _▷ₚ_
-- infixl 4 _▷_,_

-- data PreCon : Set where
--   ∙    : PreCon
--   _▷ₚ_ : PreCon → Ty → PreCon

-- data Con : PreCon → Set where
--   ∙     : Con ∙
--   _▷_,_ : ∀ {Γ} → Con Γ → Mult → ∀ A → Con (Γ ▷ₚ A)
  
-- _+ᶜ_ : ∀ {Γ} → Con Γ → Con Γ → Con Γ
-- ∙            +ᶜ ∙            = ∙
-- (Γ' ▷ m , _) +ᶜ (Δ' ▷ n , _) = (Γ' +ᶜ Δ') ▷ m + n , _

-- _*ᶜ_ : ∀ {Γ} → Con Γ → Mult → Con Γ
-- ∙            *ᶜ n = ∙
-- (Γ' ▷ m , A) *ᶜ n = (Γ' *ᶜ n) ▷ m * n , _

-- Is₀ : Mult → Set
-- Is₀ ₀ = ⊤
-- Is₀ ₁ = ⊥
-- Is₀ ω = ⊥

-- Is₀ᶜ : ∀ {Γ} → Con Γ → Set
-- Is₀ᶜ ∙            = ⊤
-- Is₀ᶜ (Γ' ▷ m , A) = Is₀ᶜ Γ' × Is₀ m

-- data Var (m : Mult)(A : Ty) : ∀ {Γ} → Con Γ → Set where
--   vz : ∀ {Γ}{Γ' : Con Γ}{_ : Is₀ᶜ Γ'} → Var m A (Γ' ▷ m , A)
--   vs : ∀ {Γ Γ' B} → Var m A {Γ} Γ' → Var m A (Γ' ▷ ₀ , B)

-- data Tm {Γ} : Con Γ → Mult → Ty → Set where
--   var :
--     ∀ {Γ' m A}
--     → Var m A Γ'
--     → Tm Γ' m A
  
--   lam :
--     ∀ {Γ' m n A B}
--     → Tm (Γ' ▷ (m * n) , A) m B
--     → Tm Γ' m (n , A ⇒ B)
  
--   app :
--     ∀ {Γ' Δ' m n A B}
--     → Tm Γ' m (n , A ⇒ B)
--     → Tm Δ' (m * n) A
--     → Tm (Γ' +ᶜ Δ') m B

-- test1 : Tm ∙ ₁ (₁ , ι ⇒ ι)
-- test1 = lam (var vz)

-- test2 : Tm ∙ ₁ (₁ , ι ⇒ ω , ι ⇒ ι)
-- test2 = lam (lam (var {!!}))

-- -- I can't write this, though I think I followed the paper.
-- test3 : Tm ∙ ₁ (ω , ι ⇒ ι)
-- test3 = lam {!!}

------------------------------------------------------------

-- data Mult : Set where -- multiplicity
--   ₀ ₁ ω : Mult

-- _*_ : Mult → Mult → Mult
-- ₀ * n = ₀
-- ₁ * n = n
-- ω * ₀ = ₀
-- ω * ₁ = ω
-- ω * ω = ω

-- _≤_ : Mult → Mult → Set
-- ₀ ≤ n = ⊤
-- ₁ ≤ ₀ = ⊥
-- ₁ ≤ ₁ = ⊤
-- ₁ ≤ ω = ⊤
-- ω ≤ ₀ = ⊥
-- ω ≤ ₁ = ⊥
-- ω ≤ ω = ⊤

-- infixl 6 _-_
-- _-_ : Mult → Mult → Mult
-- ₀ - n = ₀
-- ₁ - ₀ = ₁
-- ₁ - ₁ = ₀
-- ₁ - ω = ₀
-- ω - n = ω

-- infix 6 _*_

-- data Ty : Set where
--   ι : Ty
--   _,_⇒_ : Mult → Ty → Ty → Ty
-- infixr 4 _,_⇒_

-- data Con : Set where
--   ∙ : Con
--   _▷_,_ : Con → Mult → Ty → Con
-- infixl 4 _▷_,_

-- data _∈_ (A : Ty) : Con → Set where
--   vz : ∀ {Γ m} → A ∈ (Γ ▷ m , A)
--   vs : ∀ {Γ m B} → A ∈ Γ → A ∈ (Γ ▷ m , B)
-- infix 3 _∈_

-- Var : ∀ {Γ A} → Mult → A ∈ Γ → Set
-- Var m (vz {m = m'}) = m ≤ m'
-- Var m (vs x)        = Var m x

-- upd : ∀ {Γ A m} x → Var {Γ}{A} m x → Con
-- upd {A = A} {m} (vz {Γ} {m'}) p = Γ ▷ (m' - m) , A
-- upd (vs x) p = upd x p

-- -- kind of shitty still
-- data Tm (Γ : Con)(m : Mult) : Ty → Con → Set where
--   var : ∀ {A}(x : A ∈ Γ){p : Var {Γ}{A} m x} → Tm Γ m A (upd x p)
--   app : ∀ {A B Δ Σ n} → Tm Γ m (n , A ⇒ B) Δ → Tm Δ (m * n) A Σ → Tm Γ m B Σ

--   -- ??
--   lam : ∀ {A B Δ n k} → Tm (Γ ▷ n , A) m B (Δ ▷ k , A) → Tm Γ m (n , A ⇒ B) Δ

-- _ᶜ-_ : Con → Mult → Con
-- ∙           ᶜ- m  = ∙
-- (Γ ▷ m , A) ᶜ- m' = (Γ ᶜ- m') ▷ m - m' , A

-- _⊢_ : Con → Ty → Set
-- Γ ⊢ A = Tm Γ ₁ A (Γ ᶜ- ₁)

-- ex1 : ∙ ⊢ (₁ , ι ⇒ ι)
-- ex1 = lam (var vz)



------------------------------------------------------------

-- data Mult : Set where
--   ₀ ₁ ω : Mult

-- _-_ : Mult → Mult → Mult
-- ₀ - n = ₀
-- ₁ - ₀ = ₁
-- ₁ - ₁ = ₀
-- ₁ - ω = ₀
-- ω - ₀ = ω
-- ω - ₁ = ω
-- ω - ω = ω

-- _*_ : Mult → Mult → Mult
-- ₀ * n = ₀
-- ₁ * n = n
-- ω * ₀ = ₀
-- ω * ₁ = ω
-- ω * ω = ω

-- infix 6 _*_

-- data Ty : Set where
--   ι : Ty
--   _,_⇒_ : Mult → Ty → Ty → Ty
-- infixr 4 _,_⇒_

-- data Con : Set where
--   ∙ : Con
--   _▷_,_ : Con → Mult → Ty → Con
-- infixl 4 _▷_,_

-- data _∈_ (A : Ty) : Con → Set where
--   vz : ∀ {Γ m} → A ∈ (Γ ▷ m , A)
--   vs : ∀ {Γ m B} → A ∈ Γ → A ∈ (Γ ▷ m , B)
-- infix 3 _∈_

-- Var : ∀ {Γ A} → A ∈ Γ → Set
-- Var (vz {m = ₀}) = ⊥
-- Var (vz {m = ₁}) = ⊤
-- Var (vz {m = ω}) = ⊤
-- Var (vs x)       = Var x

-- _*ᶜ_ : Con → Mult → Con
-- ∙           *ᶜ m  = ∙
-- (Γ ▷ m , A) *ᶜ m' = Γ ▷ m * m' , A
-- infix 7 _*ᶜ_

-- consume : ∀ {Γ A}(x : A ∈ Γ) → Var x → Con
-- consume (vz {m = ₀})         ()
-- consume {A = A} (vz {Γ} {₁}) p = Γ ▷ ₀ , A
-- consume {A = A} (vz {Γ} {ω}) p = Γ ▷ ω , A
-- consume (vs {m = m} {B} x)   p = consume x p ▷ m , B

-- data Tm (Γ : Con) : Ty → Con → Set where
--   var : ∀ {A}(x : A ∈ Γ){p : Var x} → Tm Γ A (consume x p)
--   app : ∀ {A B Δ Σ m} → Tm Γ (m , A ⇒ B) Δ → Tm Δ A Σ → Tm Γ B Σ
--   lam : ∀ {A B Δ m} → Tm (Γ ▷ m , A) B Δ → Tm Γ (m , A ⇒ B) Δ

------------------------------------------------------------

-- data Ty : Set where
--   ι : Ty
--   _⊸_ : Ty → Ty → Ty
-- infixr 5 _⊸_

-- data Con : Set where
--   ∙   : Con
--   _▷_ : Con → Ty → Con
-- infixl 4 _▷_

-- data _∈_ (A : Ty) : Con → Set where
--   vz : ∀ {Γ} → A ∈ (Γ ▷ A)
--   vs : ∀ {B Γ} → A ∈ Γ → A ∈ (Γ ▷ B)

-- _-_ : ∀ Γ {A} → A ∈ Γ → Con
-- ∙ - ()
-- (Γ ▷ A) - vz   = Γ
-- (Γ ▷ A) - vs x = (Γ - x) ▷ A
-- infix 5 _-_

-- data Tm (Γ : Con) : Ty → Con → Set where
--   var : ∀ {A}(x : A ∈ Γ) → Tm Γ A (Γ - x)
--   app : ∀ {A B Δ Σ} → Tm Γ (A ⊸ B) Δ → Tm Δ A Σ → Tm Γ B Σ
--   lam : ∀ {A B Δ} → Tm (Γ ▷ A) B Δ → Tm Γ (A ⊸ B) Δ

-- infix 3 _⊢_
-- _⊢_ : Con → Ty → Set
-- Γ ⊢ A = Tm Γ A ∙

-- test : ∙ ▷ (ι ⊸ ι) ▷ ι ⊢ ι
-- test = app (var (vs vz)) (var vz)

