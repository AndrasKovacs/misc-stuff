
-- Predicative polymorphic System F

open import Function
open import Data.Nat hiding (_⊔_)
open import Data.Fin renaming (_+_ to _f+_)
open import Data.Unit
open import Relation.Binary.PropositionalEquality
open import Data.Product
open import Data.Sum
open import Data.Vec
open import Data.Vec.Properties
import Level as L

--------------------------------- Helpers --------------------------------------------

fromℕ' : ∀ n → Fin (n + 1)
fromℕ' zero    = zero
fromℕ' (suc n) = suc (fromℕ' n)

_⊔_ : ∀ {n} → Fin n → Fin n → Fin n
zero ⊔ b = b
suc a ⊔ zero = suc a
suc a ⊔ suc b = suc (a ⊔ b)

veclast : 
  ∀ {a}{A : Set a} n x (xs : Vec A n)
  → lookup (fromℕ' n) (xs ++ x ∷ []) ≡ x
veclast zero x [] = refl
veclast (suc n) x (y ∷ ys) = veclast n x ys

tighten : ∀ {n}(i : Fin (n + 1)) → (i ≡ fromℕ' n) ⊎ (∃ λ (i' : Fin n) → i ≡ inject+ 1 i')
tighten {zero} zero = inj₁ refl
tighten {zero} (suc ())
tighten {suc n} zero = inj₂ (zero , refl)
tighten {suc n} (suc i) with tighten {n} i
tighten {suc n} (suc .(fromℕ' n)) | inj₁ refl = inj₁ refl
tighten {suc n} (suc .(inject+ 1 proj₁)) | inj₂ (proj₁ , refl) = inj₂ (suc proj₁ , refl)

------------------------------------- Types -------------------------------------------

infixr 5 _⇒_
data Type (f b : ℕ) : (level : Fin 2) → Set  where 
  free   : Fin f → Type f b zero
  bound  : Fin b → Type f b zero 
  unit   : Type f b zero
  _⇒_    : ∀ {l1 l2} → Type f b l1 → Type f b l2 → Type f b (l1 ⊔ l2) 
  ∀'     : ∀ {l} → Type f (suc b) l → Type f b (suc zero ⊔ l)

relaxBound : ∀ {f b l} n → Type f b l → Type f (b + n) l
relaxBound n (free x)   = free x
relaxBound n (bound x)  = bound  (inject+ n x)
relaxBound n unit       = unit
relaxBound n (a ⇒ b)    = relaxBound n a ⇒ relaxBound n b
relaxBound n (∀' t)     = ∀' (relaxBound n t)

raiseFree : ∀ {f b l} n → Type f b l → Type (n + f) b l
raiseFree n (free x)   = free (raise n x)
raiseFree n (bound x)  = bound x
raiseFree n unit       = unit
raiseFree n (a ⇒ b)    = raiseFree n a ⇒ raiseFree n b
raiseFree n (∀' x)     = ∀' (raiseFree n x)

inst : ∀ {f b l} → Type f 0 zero → Type f (b + 1) l → Type f b l
inst t' (free x)         = free x
inst {_}{b} t' (bound x) = [ const (relaxBound b t') , bound ∘ proj₁ ]′ (tighten x)
inst t' unit             = unit
inst t' (a ⇒ b)          = inst t' a ⇒ inst t' b
inst t' (∀' x)           = ∀' (inst t' x)

abst : ∀ {f b l} → Type (suc f) b l → Type f (b + 1) l
abst {_}{b}(free zero) = bound (fromℕ' b)
abst (free (suc x))    = free x
abst (bound x)         = bound (inject+ 1 x)
abst unit              = unit
abst (a ⇒ b)           = abst a ⇒ abst b
abst (∀' x)            = ∀' (abst x)

-- ----------------------------------- Language -----------------------------------------------

data Context : ℕ → Set where
  []   : Context 0 
  term : ∀ {f l} → Type f 0 l → Context f → Context f
  type : ∀ {f}   → Context f → Context (suc f)

data Var {l : Fin 2} : ∀ {f} → Context f → Type f 0 l → Set where
  here : ∀ {f cxt t}       → Var {f = f}(term t cxt) t
  term : ∀ {f cxt t l' t'} → Var {l} cxt t → Var {f = f} (term {l = l'} t' cxt) t
  type : ∀ {f cxt t}       → Var cxt t → Var {f = suc f} (type cxt) (raiseFree 1 t)

infixl 5 _$'_

data Term {f : ℕ} (cxt : Context f) : ∀ {l} → Type f 0 l → Set where
  unit  :                  Term cxt unit
  var   : ∀ {l t}        → Var {l} cxt t → Term cxt {l} t
  λ'    : ∀ {l1 l2 b} a  → Term (term {l = l1} a cxt) {l2} b → Term cxt {l1 ⊔ l2} (a ⇒ b)
  _$'_  : ∀ {l1 l2 a b}  → Term cxt {l1 ⊔ l2} (a ⇒ b) → Term cxt {l1} a → Term cxt {l2} b 
  Λ     : ∀ {l t}        → Term (type cxt) {l} t → Term cxt {suc zero ⊔ l}(∀' (abst t))
  _$*_  : ∀ {l t}        → Term cxt (∀' {l = l} t) → (t' : Type f 0 zero) → Term cxt (inst t' t)

-- ------------------------------------ Levels -----------------------------------------------

getLevel : ∀ {f b l} → Type f b l → L.Level 
getLevel (free x)  = L.zero 
getLevel (bound x) = L.zero 
getLevel unit      = L.zero
getLevel (a ⇒ b)   = getLevel a L.⊔ getLevel b
getLevel (∀' t)    = L.suc L.zero L.⊔ getLevel t 

level : ∀ {n} → Fin n → L.Level
level zero = L.zero
level (suc n) = L.suc (level n)

level-⊔ : ∀ {n} l1 l2 → level {n} l1 L.⊔ level l2 ≡ level (l1 ⊔ l2)
level-⊔ zero zero         = refl
level-⊔ zero (suc r2)     = refl
level-⊔ (suc r1) zero     = refl
level-⊔ (suc r1) (suc r2) = cong L.suc (level-⊔ r1 r2)

level-subst : ∀ {l l'} → l ≡ l' → Set l → Set l'
level-subst refl x = x

level-subst-remove : ∀ {l l' x} p  → level-subst{l}{l'} p x → x
level-subst-remove refl x₁ = x₁

level-subst-add : ∀ {l l' x} p → x → level-subst{l}{l'} p x
level-subst-add refl x₁ = x₁

level-cong : ∀ {f b l} → (t : Type f b l) → getLevel t ≡ level l
level-cong (free x) = refl
level-cong (bound x) = refl
level-cong unit = refl
level-cong (_⇒_ {la}{lb} a b) rewrite level-cong a | level-cong b = level-⊔ la lb
level-cong (∀' {l} t) rewrite level-cong t = level-⊔ (suc zero) l 

-- ----------------------------------- Interpretation ------------------------------------------

interp : ∀ {f b l} → Vec Set f → Vec Set b → (t : Type f b l) → Set (getLevel t)
interp fs bs (free x)   = lookup x fs
interp fs bs (bound x)  = lookup x bs
interp fs bs unit       = ⊤
interp fs bs (a ⇒ b)    = interp fs bs a → interp fs bs b
interp fs bs (∀' t)     = ∀ (A : Set) → interp fs (A ∷ bs) t

_⟦_⟧ : ∀ {f} fs → Type f 0 zero → Set
_⟦_⟧ fs t = level-subst (level-cong t) (interp fs [] t) 

iRaiseFree :
  ∀ {f b l bs fs x} t 
  → interp{f}{b}{l} fs bs t 
  → interp (x ∷ fs) bs (raiseFree 1 t)

iRaiseFree' :
  ∀ {f b l bs fs x} t 
  → interp (x ∷ fs) bs (raiseFree 1 t) 
  → interp{f}{b}{l} fs bs t 

iRaiseFree (free x₁) y = y
iRaiseFree (bound x₁) y = y
iRaiseFree unit y = tt
iRaiseFree (a ⇒ b) f y = iRaiseFree b $ f $ iRaiseFree' a y
iRaiseFree (∀' t) g A = iRaiseFree t $ g A

iRaiseFree' (free x₁) y = y
iRaiseFree' (bound x₁) y = y
iRaiseFree' unit y = tt
iRaiseFree' (a ⇒ b) f y = iRaiseFree' b $ f $ iRaiseFree a y
iRaiseFree' (∀' t) g A = iRaiseFree' t $ g A

iRelaxBound :
  ∀ {b b' bs bs' f fs l} t
  → interp {f}{b}{l} fs bs t 
  → interp fs (bs ++ bs') (relaxBound b' t)

iRelaxBound' :
  ∀ {b b' bs bs' f fs l} t
  → interp fs (bs ++ bs') (relaxBound b' t)
  → interp {f}{b}{l} fs bs t 

iRelaxBound (free x) y = y
iRelaxBound {bs = bs}{bs' = bs'}(bound x) y rewrite lookup-++-inject+ bs bs' x = y
iRelaxBound unit y = y
iRelaxBound (a ⇒ b) f y = iRelaxBound b $ f $ iRelaxBound' a y
iRelaxBound (∀' t) g A = iRelaxBound t $ g A

iRelaxBound' (free x) y = y
iRelaxBound' {bs = bs}{bs' = bs'}(bound x) y rewrite lookup-++-inject+ bs bs' x = y
iRelaxBound' unit y = y
iRelaxBound' (a ⇒ b) f y = iRelaxBound' b $ f $ iRelaxBound a y
iRelaxBound' (∀' t) g A = iRelaxBound' t $ g A

iAbst : 
  ∀ {f b l bs fs A} t
  → interp{suc f}{b}{l} (A ∷ fs) bs t
  → interp{f}{b + 1}{l} fs (bs ++ A ∷ []) (abst t)

iAbst' : 
  ∀ {f b l bs fs A} t
  → interp{f}{b + 1}{l} fs (bs ++ A ∷ []) (abst t)
  → interp{suc f}{b}{l} (A ∷ fs) bs t

iAbst {f}{b}{bs = bs}{A = A}(free zero) y rewrite veclast b A bs = y
iAbst (free (suc x)) y = y
iAbst {bs = bs}{fs = fs}{A = A}(bound x) y rewrite lookup-++-inject+ bs (A ∷ []) x = y
iAbst unit y = y
iAbst (a ⇒ b) f y = iAbst b $ f $ iAbst' a y
iAbst (∀' t) g A = iAbst t $ g A

iAbst' {f}{b}{bs = bs}{A = A}(free zero) y rewrite veclast b A bs = y
iAbst' (free (suc x)) y = y
iAbst' {bs = bs}{fs = fs}{A = A}(bound x) y rewrite lookup-++-inject+ bs (A ∷ []) x = y
iAbst' unit y = y
iAbst' (a ⇒ b) f y = iAbst' b $ f $ iAbst a y
iAbst' (∀' t) g A = iAbst' t $ g A

iInst :
  ∀ {f b l fs bs t'} t
  → interp fs (bs ++ (fs ⟦ t' ⟧) ∷ []) t
  → interp {f}{b}{l} fs bs (inst t' t)

iInst' :
  ∀ {f b l fs bs t'} t
  → interp {f}{b}{l} fs bs (inst t' t)
  → interp fs (bs ++ (fs ⟦ t' ⟧) ∷ []) t

iInst (free x) y = y
iInst {b = b}(bound x) y with tighten{b} x
iInst {fs = fs}{bs = bs}{t' = t'}(bound ._) y | inj₁ refl 
  rewrite veclast _ (fs ⟦ t' ⟧) bs = iRelaxBound t' (level-subst-remove (level-cong t') y)
iInst {fs = fs}{bs = bs}{t' = t'}(bound .(inject+ 1 i)) y | inj₂ (i , refl)
  rewrite lookup-++-inject+ bs (fs ⟦ t' ⟧ ∷ []) i = y
iInst unit y = y
iInst {f}{b'}(a ⇒ b) g y = iInst{f}{b'} b $ g $ iInst'{f}{b'} a y
iInst {f}{b}(∀' t) g A = iInst {f} {suc b} t (g A)

iInst' (free x) y = y
iInst' {b = b}(bound x) y with tighten {b} x
iInst' {fs = fs}{bs = bs}{t' = t'}(bound ._) y | inj₁ refl 
  rewrite veclast _ (fs ⟦ t' ⟧) bs = level-subst-add (level-cong t') $ iRelaxBound' t' y
iInst' {fs = fs}{bs = bs}{t' = t'}(bound .(inject+ 1 i)) y | inj₂ (i , refl)
  rewrite lookup-++-inject+ bs (fs ⟦ t' ⟧ ∷ []) i = y
iInst' unit y = y
iInst' {f}{b'}(a ⇒ b) g y = iInst'{f}{b'} b $ g $ iInst{f}{b'} a y
iInst' {f}{b}(∀' t) g A = iInst' {f} {suc b} t (g A)

-- ------------------------------------- Evaluation -----------------------------------------------

data Env : ∀ {f} → Vec Set f → Context f → Set₁ where
  []   : Env [] []
  term : ∀ {f l ts cxt t} → interp {f}{0}{l} ts [] t → Env ts cxt → Env ts (term t cxt)
  type : ∀ {f ts cxt t} → Env {f} ts cxt → Env (t ∷ ts) (type cxt)

lookupTerm : ∀ {l f fs cxt t} → Var {l} {f} cxt t → Env fs cxt → interp fs [] t 
lookupTerm here             (term x env) = x
lookupTerm (term v)         (term x env) = lookupTerm v env
lookupTerm (type {t = t} v) (type env)   = iRaiseFree t $ lookupTerm v env

eval : ∀ {f l cxt fs t} → Env fs cxt → Term {f} cxt {l} t → interp fs [] t 
eval env unit       = tt
eval env (var x)    = lookupTerm x env
eval env (λ' _ e) x = eval (term x env) e
eval env (f $' x)   = eval env f (eval env x)
eval env (Λ {t = t} e) A = iAbst t $ eval (type env) e
eval {fs = fs} env (_$*_ {t = t} f t') = iInst {b = 0} t $ eval env f (fs ⟦ t' ⟧)

-- examples

levelof : ∀ {l}{t : Type 0 0 l} → Term [] t → Fin 2
levelof {l} _ = l 

-- Λ a. λ (x : a). x
ID : Term [] _
ID = Λ (λ' (free zero) (var here))

-- Λ a b. λ (x : a) (y : b). x
CONST : Term [] _
CONST = Λ (Λ (λ' (free (suc zero)) (λ' (free zero) (var (term here)))))

-- Λ a. λ (x : a). Λ b. λ (y : b). x 
CONST' : Term [] _
CONST' = Λ (λ' (free zero) (Λ (λ' (free zero) (var (term (type here))))))

-- Λ a. λ (id : Λ a. a → a) (x : a). id [a] x   
IDAPP : Term [] _
IDAPP = Λ (λ' (∀' (bound zero ⇒ bound zero)) (λ' (free zero) (var (term here) $* free zero  $' var here)))

evaltest : eval [] IDAPP ℕ (eval [] ID) 10 ≡ 10
evaltest = refl
