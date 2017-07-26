
open import Lib
open import SysT

-- Evaluation
--------------------------------------------------------------------------------

data _~>_ : ∀ {A} → Tm ∙ A → Tm ∙ A → Set where
  β    : ∀ {A B}(t : Tm (∙ , A) B) t'     →  app (lam t) t' ~> t [ idₛ , t' ]
  app₁ : ∀ {A B}{f}{f' : Tm ∙ (A ⇒ B)}{a} → f ~> f' →  app f a ~> app f' a
  
  suc       : ∀ {n n'} → n ~> n' → suc n ~> suc n'
  iter-suc  : ∀ {A}{n}{s}{z : Tm ∙ A} → iter (suc n) s z ~> app (app s n) (iter n s z)
  iter-zero : ∀ {A}{s}{z : Tm ∙ A}    → iter zero s z    ~> z
  iter₁     : ∀ {A}{n n' : Tm ∙ Nat}{s}{z : Tm ∙ A} → n ~> n' → iter n s z ~> iter n' s z

infix 3 _~>_

-- ~>ₛ : ∀ {Γ Δ A}{t t' : Tm Γ A}(σ : Tms Δ Γ) → t ~> t' → t [ σ ] ~> t' [ σ ]
-- ~>ₛ σ (β t t') =
--   coe ((app (lam (t [ keepₛ σ ])) (t' [ σ ]) ~>_)
--       & (∘ₛTm t (keepₛ σ) (idₛ , (t' [ σ ]))
--       ◾ (t [_]) & ((_, (t' [ σ ])) &
--           (assₛₑₛ σ wk (idₛ , (t' [ σ ]))
--         ◾ (σ ∘ₛ_) & (idlₑₛ idₛ) ◾ idrₛ σ ◾ idlₛ σ ⁻¹))
--       ◾ ∘ₛTm t (idₛ , t') σ ⁻¹))
--   (β (t [ keepₛ σ ]) (t' [ σ ]))  
-- ~>ₛ σ (app₁ t~>t') = app₁ (~>ₛ σ t~>t')
-- ~>ₛ σ (suc t~>t') = suc (~>ₛ σ t~>t')
-- ~>ₛ σ iter-suc = iter-suc
-- ~>ₛ σ iter-zero = iter-zero
-- ~>ₛ σ (iter₃ t~>t') = iter₃ (~>ₛ σ t~>t')

-- ~>ₑ : ∀ {Γ Δ A}{t t' : Tm Γ A}(σ : OPE Δ Γ) → t ~> t' → t [ σ ]ₑ ~> t' [ σ ]ₑ
-- ~>ₑ σ (β t t') =
--   coe ((app (lam (t [ keep σ ]ₑ)) (t' [ σ ]ₑ) ~>_) &
--       (ₑ∘ₛTm t (keep σ) (idₛ , (t' [ σ ]ₑ))
--     ◾ (t [_]) & ((_, (t' [ σ ]ₑ)) & (idrₑₛ σ ◾ idlₛₑ σ ⁻¹))
--     ◾ ₛ∘ₑTm t (idₛ , t') σ ⁻¹))
--   (β (t [ keep σ ]ₑ) (t' [ σ ]ₑ))
-- ~>ₑ σ (app₁ t~>t') = app₁ (~>ₑ σ t~>t')
-- ~>ₑ σ (suc t~>t') = suc (~>ₑ σ t~>t')
-- ~>ₑ σ iter-suc = iter-suc
-- ~>ₑ σ iter-zero = iter-zero
-- ~>ₑ σ (iter₃ t~>t') = iter₃ (~>ₑ σ t~>t')

data _~>*_ {A} : Tm ∙ A → Tm ∙ A → Set where
  []    : ∀ {t} → t ~>* t
  _∷_   : ∀ {t t' t''} → t ~> t' → t' ~>* t'' → t ~>* t''
infixr 4 _∷_
infix 3 _~>*_

trans~>* : ∀ {A}{t t' t'' : Tm ∙ A} → t ~>* t' → t' ~>* t'' → t ~>* t''
trans~>* []       qs = qs
trans~>* (p ∷ ps) qs = p ∷ trans~>* ps qs

Numeral : Tm ∙ Nat → Set
Numeral (var _)      = ⊥
Numeral (app _ _)    = ⊥
Numeral zero         = ⊤
Numeral (suc t)      = Numeral t
Numeral (iter _ _ _) = ⊥

Good : ∀ {A} → Tm ∙ A → Set
Good {Nat}   t = Σ _ λ t' → Numeral t' × (t ~>* t') 
Good {A ⇒ B} t =
  Σ _ λ t' → (t ~>* lam t') × (((a : Tm ∙ A) → Good a → Good (t' [ idₛ , a ])))

data Goodˢ : ∀ {Γ} → Tms ∙ Γ → Set where
  ∙   : Goodˢ ∙
  _,_ : ∀ {Γ A}{t : Tm ∙ A}{σ : Tms ∙ Γ} → Goodˢ σ → Good t → Goodˢ (σ , t)

Good~>⁻¹ : ∀ {A}{t t' : Tm ∙ A} → t ~> t' → Good t' → Good t
Good~>⁻¹ {Nat}   t~>t' (n , q , r)   = n , q , (t~>t' ∷ r)
Good~>⁻¹ {A ⇒ B} t~>t' (t'' , p , q) = t'' , (t~>t' ∷ p) , q

Good~>*⁻¹ : ∀ {A}{t t' : Tm ∙ A} → t ~>* t' → Good t' → Good t
Good~>*⁻¹ []           pt' = pt'
Good~>*⁻¹ (p ∷ t~>*t') pt' = Good~>⁻¹ p (Good~>*⁻¹ t~>*t' pt')

app₁* : ∀ {A B}{t t' : Tm ∙ (A ⇒ B)}{u} → t ~>* t' → app t u ~>* app t' u
app₁* []           = []
app₁* (p ∷ t~>*t') = app₁ p ∷ app₁* t~>*t'

suc* : ∀ {t t' : Tm ∙ Nat} → t ~>* t' → suc t ~>* suc t'
suc* []       = []
suc* (p ∷ ps) = suc p ∷ suc* ps

iter₁* : ∀ {A}{n n' : Tm ∙ Nat}{s}{z : Tm ∙ A} → n ~>* n' → iter n s z ~>* iter n' s z
iter₁* [] = []
iter₁* (p ∷ ps) = iter₁ p ∷ iter₁* ps

q : ∀ {A}{t : Tm ∙ A} → Good t → Σ _ λ t' → t ~>* t'
q {Nat}   tᴳ = {!!}
q {A ⇒ B} tᴳ = {!!}

eval : ∀ {Γ A}(t : Tm Γ A){σ : Tms ∙ Γ} → Goodˢ σ → Good (t [ σ ])
eval (var vz)     (_  , x) = x
eval (var (vs x)) (σᴳ , _) = eval (var x) σᴳ

eval (lam t) {σ} σᴳ = 
  t [ keepₛ σ ] , [] ,
  (λ a aᴳ →
    coe {!!}
    (eval t {σ , a} (σᴳ , aᴳ)))
    
    -- coe
    --   (Good &
    --     ((λ x → t [ x ]) & ((_, a) & ?)))
    --       -- (idrₛ σ ⁻¹ ◾ assₛₑₛ σ (drop ∙) (∙ , a) ⁻¹)) ◾ Tm-∘ₛ (keepₛ σ) (∙ , a) t))
    -- (eval t {σ , a} (σᴳ , aᴳ)))

eval (app t u) {σ} σᴳ with eval t σᴳ
... | t' , p , q =
  Good~>*⁻¹ (trans~>* (app₁* p) (β t' (u [ σ ]) ∷ [])) (q (u [ σ ]) (eval u σᴳ) )

eval zero {σ} σᴳ         = zero , tt , []

eval (suc t) {σ} σᴳ  with eval t σᴳ
... | t' , p , q = suc t' , p , suc* q

eval (iter n s z) {σ} σᴳ with eval n σᴳ
... | var x , () , q
... | app n' n'' , () , q
... | iter n' n'' n''' , () , q
... | zero , p , q =
  let reduce : iter (n [ σ ]) (s [ σ ]) (z [ σ ]) ~>* z [ σ ]
      reduce = trans~>* (iter₁* q) (iter-zero ∷ [])
  in Good~>*⁻¹ reduce (eval z σᴳ)


... | suc n' , pn' , qn' = {!!}

-- with eval s σᴳ
-- ... | s' , p' , q' with q' n' (n' , p , []) | eval z σᴳ
-- ... | sn' , psn , qsn | foo = {!iter n' (lam s')!}
  -- let reduce :
  --      iter (n [ σ ]) (s [ σ ]) (z [ σ ]) ~>* {!!}

  --     reduce = {!q'!}
  -- in {!q' n' ?!}

-- eval (var vz)     (σᴹ , pt) = pt
-- eval (var (vs x)) (σᴹ , _ ) = eval (var x) σᴹ
-- eval (lam t) {σ} σᴳ =
--   Tmₛ (keepₛ σ) t , [] ,
--   (λ a aᴳ →
--     coe
--       (Good &
--         ((λ x → Tmₛ x t) & ((_, a) &
--           (idrₛ σ ⁻¹ ◾ assₛₑₛ σ (drop ∙) (∙ , a) ⁻¹)) ◾ Tm-∘ₛ (keepₛ σ) (∙ , a) t))
--     (eval t {σ , a} (σᴳ , aᴳ)))
-- eval (app t u) {σ} σᴳ with eval t σᴳ
-- ... | t' , p , q =
--   Good~>*⁻¹ (trans~>* (app₁* p) (β t' (Tmₛ σ u) ∷ [])) (q (Tmₛ σ u) (eval u σᴳ) )

-- Val : ∀ {A} → Tm ∙ A → Set
-- Val (var _)   = ⊥
-- Val (lam _)   = ⊤
-- Val (app _ _) = ⊥

-- Reducible : ∀ {A} → Tm ∙ A → Set
-- Reducible t = Σ _ λ t' → Val t' → t ~>* t'

-- Quote : ∀ {A}{t : Tm ∙ A} → Good t → Reducible t
-- Quote {ι} ()
-- Quote {A ⇒ B}{t} (t' , p , q) = lam t' , (λ _ → p)

-- whnf : ∀ {A}(t : Tm ∙ A) → Reducible t
-- whnf t = coe (Reducible & Tm-idₛ t) (Quote (eval t ∙))









