
-- Written by: András Kovács

data Con : Set
data Ty  : Con → Set
data Var : (Γ : Con) → Ty Γ → Set

data Con where
  ∙   : Con
  _▷_ : (Γ : Con) → Ty Γ → Con

data Ty where
  ★   : ∀ {Γ} → Ty Γ
  Ar  : ∀ {Γ}(A : Ty Γ) → Var Γ A → Var Γ A → Ty Γ

wk    : ∀ {Γ : Con} → (B : Ty Γ) → Ty Γ → Ty (Γ ▷ B)
wkVar : ∀ {Γ : Con} → (B : Ty Γ) → ∀ {A} → Var Γ A → Var (Γ ▷ B) (wk B A)

data Var where
  vz : ∀ {Γ : Con}{A : Ty Γ}   → Var (Γ ▷ A) (wk A A)
  vs : ∀ {Γ : Con}{A B : Ty Γ} → Var Γ A → Var (Γ ▷ B) (wk B A)

wk B ★          = ★
wk B (Ar A x y) = Ar (wk B A) (wkVar B x) (wkVar B y)

wkVar B vz                 = vs vz
wkVar B (vs {Γ} {A} {C} x) = vs {B = B} (wkVar C x)

-- Pasting schemes
--------------------------------------------------------------------------------

infixl 4 _▷_

data _⊢ : Con → Set
data _⊢_∋_ : (Γ : Con)(A : Ty Γ) → Var Γ A → Set

data _⊢ where
  stop : ∀ {Γ x} → Γ ⊢ ★ ∋ x → Γ ⊢

data _⊢_∋_ where
  sing : (∙ ▷ ★) ⊢ ★ ∋ vz
  ext  : ∀ {Γ A x} → Γ ⊢ A ∋ x → (Γ ▷ A ▷ Ar (wk A A) (wkVar A x) vz)
                                 ⊢ Ar (wk (Ar (wk A A) (wkVar A x) vz) (wk A A))
                                      (wkVar (Ar (wk A A) (wkVar A x) vz) (wkVar A x))
                                      (vs vz)
                                 ∋ vz

  down : ∀ {Γ A x y f} → Γ ⊢ Ar A x y ∋ f → Γ ⊢ A ∋ y

-- sc1 : _ ⊢
-- sc1 = stop (down (down (ext (ext sing))))

-- -- (∙ ▷ ★ ▷ ★ ▷ Ar ★ (vs vz) vz ▷ Ar ★ (vs (vs vz)) (vs vz)
-- --    ▷ Ar (Ar ★ (vs (vs (vs vz))) (vs (vs vz))) (vs vz) vz)
