
{-

Intrinsically typed normal forms of dependent type theory in type theory
are generally believed to be not possible for reasonably featureful
type theories.

I don't challenge that position; the best I could do was
the following super small TT with only variables. The other
files contain depvelopments that don't work.

-}

infixl 5 _,_
infix 3 _∋_
infix 4 _⊢_

data Con : Set
data Ty Γ : Set
data _∋_ : (Γ : Con) → Ty Γ → Set
data _⊢_ (Γ : Con) : Ty Γ → Set

data Con where
  ∙   : Con
  _,_ : (Γ : Con) (A : Ty Γ) → Con

data Ty Γ where
  U  : Ty Γ
  El : (t : Γ ⊢ U) → Ty Γ

wkTy : ∀ {Γ B} → Ty Γ → Ty (Γ , B)
wkTm : ∀ {Γ A B} → Γ ⊢ A → (Γ , B) ⊢ wkTy A

data _∋_ where
  zero : ∀{Γ}{A : Ty Γ} → Γ , A ∋ wkTy A
  suc  : ∀{Γ}{A B : Ty Γ} → Γ ∋ A → Γ , B ∋ wkTy A

data _⊢_ Γ where
  var : ∀ {A} → Γ ∋ A → Γ ⊢ A

wkTm (var x) = var (suc x)
wkTy U       = U
wkTy (El t)  = El (wkTm t)

-- example
p : (∙ , U , El (var zero) , El (var (suc zero))) ⊢ El (var (suc (suc zero)))
p = var zero

