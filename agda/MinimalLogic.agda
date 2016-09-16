-- (stolen from Ambrus Kaposi)

module MinimalLogic (PropVar : Set) where

-- minimal propositional logic, Kripke models, soundness and completeness

-- from: Altenkirch et al: Categorical reconstruction of a
-- reduction-free normalisation proof, very beginning

-- also: www.cs.nott.ac.uk/~txa/talks/nbe09.pdf (Normalisation by Completeness)

open import library

-- syntax

data Ty : Set where
  pv : (X : PropVar) → Ty
  _⇒_ : (A : Ty)(B : Ty) → Ty
infixr 5 _⇒_ 

data Con : Set where
  ∅ : Con
  _,_ : (Γ : Con)(A : Ty) → Con
infixl 7 _,_

data Var : Con → Ty → Set where
  zero : {Γ : Con}{A : Ty} → Var (Γ , A) A
  suc  : {Γ : Con}{A B : Ty} → Var Γ A → Var (Γ , B) A

data _⊢_ : Con → Ty → Set where
  var : {Γ : Con}{A : Ty} → Var Γ A → Γ ⊢ A
  lam : {Γ : Con}{A B : Ty} → Γ , A ⊢ B → Γ ⊢ A ⇒ B
  app : {Γ : Con}{A B : Ty} → Γ ⊢ A ⇒ B → Γ ⊢ A → Γ ⊢ B
infix 4 _⊢_

-- some weakening lemmas

_++_ : Con → Con → Con
Γ ++ ∅ = Γ
Γ ++ (Δ , A) = (Γ ++ Δ) , A
infixl 6 _++_

left-unit : {Γ : Con} → ∅ ++ Γ ≡ Γ
left-unit {∅} = refl
left-unit {Γ , A} = ap (λ Δ → Δ , A) (left-unit {Γ})

wkvar : {Γ Δ : Con}{A B : Ty} → Var (Γ ++ Δ) A → Var (Γ , B ++ Δ) A
wkvar {Δ = ∅} X = suc X
wkvar {Δ = Δ , A} zero = zero
wkvar {Γ}{Δ = Δ , C}{A}{B} (suc X) = suc (wkvar {Γ}{Δ}{A}{B} X)

wklemma : {Γ Δ : Con}{A B : Ty} → Γ ++ Δ ⊢ A → Γ , B ++ Δ ⊢ A
wklemma {Δ = ∅} (var X) = var (suc X)
wklemma {Δ = Δ , C} (var zero) = var zero
wklemma {Γ}{Δ , C}{A}{B} (var (suc X)) = var (suc (wkvar {Γ}{Δ}{A}{B} X))
wklemma {Γ}{Δ}{A ⇒ B}{C}(lam p) = lam (wklemma {Γ}{Δ , A}{B}{C} p)
wklemma {Γ}{Δ}{A}{B}(app {.(Γ ++ Δ)}{C}{.A} p q) = app (wklemma {Γ}{Δ}{C ⇒ A}{B} p) (wklemma {Γ}{Δ}{C}{B} q)

wk1 : {Γ : Con}{A B : Ty} → Γ ⊢ A → Γ , B ⊢ A
wk1 {Γ}{A}{B} P = wklemma {Γ}{∅}{A}{B} P

wkmany : {Γ Δ : Con}{A : Ty} → Γ ⊢ A → Γ ++ Δ ⊢ A
wkmany {Δ = ∅} p = p
wkmany {Δ = Δ , A} p = wk1 (wkmany {Δ = Δ} p)

module other_formulation where

  -- an equivalent formulation with weakening rule

  data _⊢'_ : Con → Ty → Set where
    ass : {Γ : Con}{A : Ty} → Γ , A ⊢' A
    wk  : {Γ : Con}{A B : Ty} → Γ ⊢' A → Γ , B ⊢' A
    lam : {Γ : Con}{A B : Ty} → Γ , A ⊢' B → Γ ⊢' A ⇒ B
    app : {Γ : Con}{A B : Ty} → Γ ⊢' A ⇒ B → Γ ⊢' A → Γ ⊢' B
  infix 4 _⊢'_

  right : {Γ : Con}{A : Ty} → Γ ⊢ A → Γ ⊢' A
  right (var zero) = ass
  right (var (suc X)) = wk (right (var X))
  right (lam p) = lam (right p)
  right (app p q) = app (right p) (right q)

  left : {Γ : Con}{A : Ty} → Γ ⊢' A → Γ ⊢ A
  left ass = var zero
  left (wk p) = wk1 (left p)
  left (lam p) = lam (left p)
  left (app p q) = app (left p) (left q)

module truth_table (lem : {A : Set} → A + ¬ A) where

  -- truth table semantics is only sound if the metatheory is classical
  -- (or if ρ is decidable, which is just the same)

  record TTModel : Set₁ where
    field
      ρ : PropVar → Set

    ⟦_⟧ty : Ty → Set
    ⟦ pv X  ⟧ty = ρ X
    ⟦ A ⇒ B ⟧ty = ⟦ B ⟧ty + (¬ ⟦ A ⟧ty)

    ⟦_⟧con : Con → Set
    ⟦ ∅     ⟧con = One
    ⟦ Γ , A ⟧con = ⟦ Γ ⟧con × ⟦ A ⟧ty

    _⊩_ : Con → Ty → Set
    Γ ⊩ A = ⟦ Γ ⟧con → ⟦ A ⟧ty

  sound : {Γ : Con}{A : Ty} → Γ ⊢ A → (M : TTModel) → let open TTModel M in Γ ⊩ A
  sound (var zero) M (p , q) = q
  sound (var (suc X)) M (p , q) = sound (var X) M p
  sound (lam {Γ}{A}{B} p) M q = let open TTModel M in
    case {C = λ _ → ⟦ B ⟧ty + (¬ ⟦ A ⟧ty)}
         inl
         (λ ¬b → case {C = λ _ → ⟦ B ⟧ty + (¬ ⟦ A ⟧ty)}
                      (λ a → inl (sound p M (q , a)))
                      inr
                      (lem {⟦ A ⟧ty}))
         (lem {⟦ B ⟧ty})
  sound (app {Γ}{A}{B} p q) M r = let open TTModel M in
    case {C = λ _ → (⟦ B ⟧ty)}
         (λ a → case {C = λ _ → ⟦ B ⟧ty}
                     (λ b → b)
                     (λ ¬a → exfalso (¬a a) )
                     (sound p M r))
         (λ ¬a → exfalso (¬a (sound q M r)))
         (lem {⟦ A ⟧ty})

-- notion of Kripke model

record Model : Set₁ where
  field
    W : Set
    _≤_ : W → W → Set
    ≤-refl : {w : W} → w ≤ w
    ≤-trans : {w v v' : W} → w ≤ v → v ≤ v' → w ≤ v'
    _⊩pv_ : W → PropVar → Set
    mon-pv : {w v : W}{X : PropVar} → w ≤ v → w ⊩pv X → v ⊩pv X

  infix 4 _≤_
  infix 4 _⊩pv_

  _⊩ty_ : W → Ty → Set
  w ⊩ty pv X = w ⊩pv X
  w ⊩ty (A ⇒ B) = (v : W) → w ≤ v → v ⊩ty A → v ⊩ty B
  infix 4 _⊩ty_

  _⊩con_ : W → Con → Set
  w ⊩con ∅ = One
  w ⊩con (Γ , A) = w ⊩con Γ × w ⊩ty A
  infix 4 _⊩con_

  _⊩_ : Con → Ty → Set
  Γ ⊩ A = (w : W) → w ⊩con Γ → w ⊩ty A
  infix 4 _⊩_

  mon-ty : {A : Ty}{w v : W} → w ≤ v → w ⊩ty A → v ⊩ty A
  mon-ty {pv X} f p = mon-pv f p
  mon-ty {A ⇒ B} f p v' g q = p v' (≤-trans f g) q

  mon-con : {Γ : Con}{w v : W} → w ≤ v → w ⊩con Γ → v ⊩con Γ
  mon-con {∅} f p = *
  mon-con {Γ , A} f (p , q) = mon-con {Γ} f p , mon-ty {A} f q

-- soundness of Kripke semantics

sound : {Γ : Con}{A : Ty} → Γ ⊢ A → ((M : Model) → let open Model M in Γ ⊩ A)
sound (var zero)    M w (p , q) = q
sound (var (suc X)) M w (p , q) = sound (var X) M w p
sound (lam P)       M w p v f q = let open Model M in
                                  sound P M v ((mon-con f p) , q)
sound (app P Q)     M w p       = let open Model M in
                                  sound P M w p w (≤-refl) (sound Q M w p)

module example (P Q : PropVar)(P≠Q : P ≡ Q → Zero) where

  -- example usage of a Kripke models and soundness:
  -- show that ⊬ ((P→Q)→P)→P (if P,Q:PropVar)

  -- note that P ≠ Q because:
  ex : {P : Set} → ((P → P) → P) → P
  ex f = f (λ x → x)

  -- the countermodel: ff ≤ tt, tt ⊩ P
  M : Model
  M = record
        { W = Two
        ; _≤_ = λ { ff tt → One ; ff ff → One ; tt tt → One ; tt ff → Zero }
        ; ≤-refl  = λ { {ff} → * ; {tt} → * }
        ; ≤-trans = λ { {ff}{ff}{ff} p q → *
                      ; {ff}{ff}{tt} p q → *
                      ; {ff}{tt}{tt} p q → *
                      ; {tt}{tt}{tt} p q → *
                      ; {ff}{tt}{ff} p q → *
                      ; {tt}{ff}{ff} p q → p
                      ; {tt}{ff}{tt} p q → *
                      ; {tt}{tt}{ff} p q → q
                      }
        ; _⊩pv_ = λ { ff _ → Zero ; tt R → P ≡ R }
        ; mon-pv = λ { {ff}{ff} _ ()
                     ; {ff}{tt} _ ()
                     ; {tt}{ff} ()
                     ; {tt}{tt} _ p → p
                     }
        }

  open Model M

  -- we show that in this model ⊮ ((P→Q)→P)→P
  counter : ff ⊩ty (((pv P ⇒ pv Q) ⇒ pv P) ⇒ pv P) → Zero
  counter p = p ff (≤-refl {ff}) (λ { ff _ q → exfalso (P≠Q (q tt * refl)) 
                                    ; tt _ _ → refl
                                    })

  -- we use soundness to show that this is not derivable
  result : ∅ ⊢ (((pv P ⇒ pv Q) ⇒ pv P) ⇒ pv P) → Zero
  result p = counter (sound p M ff *)

-- completeness

complete : {Γ : Con}(A : Ty) → ((M : Model) → let open Model M in Γ ⊩ A) → Γ ⊢ A
complete {Γ} A σ = Quote (σ U Γ ⊩con-refl)
  where
    _⊢*_ : Con → Con → Set
    Γ ⊢* ∅ = One
    Γ ⊢* (Δ , A) = Γ ⊢* Δ × Γ ⊢ A
    infix 5 _⊢*_

    wk⊢* : {Γ Δ : Con}{A : Ty} → Γ ⊢* Δ → Γ , A ⊢* Δ
    wk⊢* {Δ = ∅} p = *
    wk⊢* {Γ}{Δ , A}{B} (p , q) = wk⊢* {Γ}{Δ}{B} p , wk1 q

    ⊢*-refl : {Γ : Con} → Γ ⊢* Γ
    ⊢*-refl {∅} = *
    ⊢*-refl {Γ , A} =  wk⊢* (⊢*-refl {Γ})  , var zero

    -- this is stronger than what is needed for mon-pv, but we'll need it later
    ⊢*-mon : {Γ Δ : Con}{A : Ty} → Γ ⊢* Δ → Δ ⊢ A → Γ ⊢ A
    ⊢*-mon {Γ}{∅}{A} f p = transport (λ Θ → Θ ⊢ A) left-unit (wkmany {∅}{Γ} p)
    ⊢*-mon {Γ}{Δ , B}{A} (f , p) q = app (⊢*-mon f (lam q)) p

    ⊢*-trans : {Γ Δ Θ : Con} → Γ ⊢* Δ → Δ ⊢* Θ → Γ ⊢* Θ
    ⊢*-trans {Θ = ∅} f g = *
    ⊢*-trans {Γ}{Δ}{Θ , A} f (g , p) = ⊢*-trans f g , ⊢*-mon f p

    -- the universal syntactic model
    U : Model
    U = record
          { W = Con
          ; _≤_ = λ Γ Δ → Δ ⊢* Γ
          ; ≤-refl = λ {Γ} → ⊢*-refl {Γ}
          ; ≤-trans = λ f g → ⊢*-trans g f
          ; _⊩pv_ = λ Γ X → Γ ⊢ pv X
          ; mon-pv = ⊢*-mon
          }

    open Model U

    Quote   : {Γ : Con}{A : Ty} → Γ ⊩ty A → Γ ⊢   A
    Unquote : {Γ : Con}{A : Ty} → Γ ⊢   A → Γ ⊩ty A

    Quote {Γ}{pv X} p = p
    Quote {Γ}{A ⇒ B} p = lam (Quote (p (Γ , A) (wk⊢* ⊢*-refl) (Unquote {Γ , A} (var zero))))

    Unquote {Γ}{pv X} p = p
    Unquote {Γ}{A ⇒ B} p Δ f q = Unquote (app (⊢*-mon f p) (Quote {Δ}{A} q))

    ⊩con-refl : {Γ : Con} → Γ ⊩con Γ
    ⊩con-refl {∅} = *
    ⊩con-refl {Γ , A} = mon-con (wk⊢* ⊢*-refl) (⊩con-refl {Γ})
                      , Unquote {Γ , A} (var zero) 

module NBC where

  -- normalisation by completeness
  -- we shrink the universal model to only contain normal forms

  -- the only interesting change will be ⊢*-mon

  data Nf : Con → Ty → Set

  data Neu : Con → Ty → Set where
    var : {Γ : Con}{A : Ty} → Var Γ A → Neu Γ A
    app : {Γ : Con}{A B : Ty} → Neu Γ (A ⇒ B) → Nf Γ A → Neu Γ B

  data Nf where
    neu : {Γ : Con}{A : Ty} → Neu Γ A → Nf Γ A
    lam : {Γ : Con}{A B : Ty} → Nf (Γ , A) B → Nf Γ (A ⇒ B)

  wkNeu : {Γ Δ : Con}{A B : Ty} → Neu (Γ ++ Δ) A → Neu (Γ , B ++ Δ) A
  wkNf : {Γ Δ : Con}{A B : Ty} → Nf (Γ ++ Δ) A → Nf (Γ , B ++ Δ) A

  wkNeu {Δ = ∅} (var X) = var (suc X)
  wkNeu {Γ}{Δ , C}{A}{B} (var X) = var (wkvar {Γ}{Δ , C}{A}{B} X)
  wkNeu {Γ}{Δ}{A}{B}(app {.(Γ ++ Δ)}{C}{.A} p q) = app {Γ , B ++ Δ}{C}{A}
                                                       (wkNeu {Γ}{Δ}{C ⇒ A}{B} p)
                                                       (wkNf {Γ}{Δ}{C}{B} q)

  wkNf {Γ}{Δ}{A}{B}(neu n) = neu (wkNeu {Γ}{Δ}{A}{B} n)
  wkNf {Γ}{Δ}{A ⇒ B}{C} (lam p) = lam (wkNf {Γ}{Δ , A}{B}{C} p)

  wkNf1 : {Γ : Con}{A B : Ty} → Nf Γ A → Nf (Γ , B) A
  wkNf1 {Γ}{A}{B} = wkNf {Γ}{∅}{A}{B}

  wkNfmany : {Γ Δ : Con}{A : Ty} → Nf Γ A → Nf (Γ ++ Δ) A
  wkNfmany {Δ = ∅} p = p
  wkNfmany {Δ = Δ , A} p = wkNf1 (wkNfmany {Δ = Δ} p)

  wkNeumany : {Γ Δ : Con}{A : Ty} → Neu Γ A → Neu (Γ ++ Δ) A
  wkNeumany {Δ = ∅} p = p
  wkNeumany {Γ}{Δ , B}{A} p = wkNeu {Γ ++ Δ}{∅}{A}{B} (wkNeumany {Γ}{Δ} p)

  wkVarmany : {Γ Δ : Con}{A : Ty} → Var Γ A → Var (Γ ++ Δ) A
  wkVarmany {Δ = ∅} p = p
  wkVarmany {Γ}{Δ , B}{A} p = wkvar {Γ ++ Δ}{∅}{A}{B} (wkVarmany {Γ}{Δ} p)

  complete' : {Γ : Con}(A : Ty) → ((M : Model) → let open Model M in Γ ⊩ A) → Nf Γ A
  complete' {Γ} A σ = Quote (σ U Γ ⊩con-refl)
    where
      -- the subset relation
      _⊢*_ : Con → Con → Set
      Γ ⊢* ∅ = One
      Γ ⊢* (Δ , A) = Γ ⊢* Δ × Var Γ A
      infix 5 _⊢*_

      wk⊢* : {Γ Δ : Con}{A : Ty} → Γ ⊢* Δ → Γ , A ⊢* Δ
      wk⊢* {Δ = ∅} p = *
      wk⊢* {Γ}{Δ , A}{B} (p , q) = wk⊢* {Γ}{Δ}{B} p , suc q

      ⊢*-refl : {Γ : Con} → Γ ⊢* Γ
      ⊢*-refl {∅} = *
      ⊢*-refl {Γ , A} =  wk⊢* (⊢*-refl {Γ}) , zero

      ⊢*-mon-var : {Γ Δ : Con}{A : Ty} → Γ ⊢* Δ → Var Δ A → Var Γ A
      ⊢*-mon-var {Δ = ∅} f ()
      ⊢*-mon-var {Γ}{Δ , A}{.A} (f , p) zero = p
      ⊢*-mon-var {Γ}{Δ , B}{A} (f , p) (suc x) = ⊢*-mon-var {Γ}{Δ}{A} f x

      ⊢*-mon-neu : {Γ Δ : Con}{A : Ty} → Γ ⊢* Δ → Neu Δ A → Neu Γ A
      ⊢*-mon-nf  : {Γ Δ : Con}{A : Ty} → Γ ⊢* Δ → Nf Δ A → Nf Γ A

      -- the main idea here is for the following case:
      --
      --    (f , x) : Γ ⊢* Δ , B     ≡  Γ ⊢* Δ × Var Γ B
      --    n       : Neu (Δ , B) A
      --    ------------------------
      --    ?       : Neu Γ A
      --
      -- we get ? by replacing all references in n to B by the reference
      -- given by x

      ⊢*-mon-neu {Γ}{∅}{A} f n = transport (λ Θ → Neu Θ A) left-unit (wkNeumany {∅}{Γ}{A} n)
      ⊢*-mon-neu {Γ}{Δ , B}{.B} (f , x) (var zero) = var x
      ⊢*-mon-neu {Γ}{Δ , B}{A} (f , x) (var (suc y)) = ⊢*-mon-neu {Γ}{Δ}{A} f (var y)
      ⊢*-mon-neu {Γ}{Δ , B}{A} (f , x) (app n t) = app (⊢*-mon-neu (f , x) n) (⊢*-mon-nf (f , x) t)

      ⊢*-mon-nf f (neu n) = neu (⊢*-mon-neu f n)
      ⊢*-mon-nf f (lam t) = lam (⊢*-mon-nf (wk⊢* f , zero) t)

      ⊢*-trans : {Γ Δ Θ : Con} → Γ ⊢* Δ → Δ ⊢* Θ → Γ ⊢* Θ
      ⊢*-trans {Θ = ∅} f g = *
      ⊢*-trans {Γ}{Δ}{Θ , A} f (g , p) = ⊢*-trans f g , ⊢*-mon-var f p

      U : Model
      U = record
            { W = Con
            ; _≤_ = λ Γ Δ → Δ ⊢* Γ
            ; ≤-refl = λ {Γ} → ⊢*-refl {Γ}
            ; ≤-trans = λ f g → ⊢*-trans g f
            ; _⊩pv_ = λ Γ X → Neu Γ (pv X)
            ; mon-pv = ⊢*-mon-neu
            }

      open Model U

      Quote   : {Γ : Con}{A : Ty} → Γ ⊩ty A → Nf Γ A
      Unquote : {Γ : Con}{A : Ty} → Neu Γ A → Γ ⊩ty A

      Quote {Γ}{pv X} p = neu p
      Quote {Γ}{A ⇒ B} p = lam (Quote (p (Γ , A) (wk⊢* ⊢*-refl) (Unquote {Γ , A} (var zero))))

      Unquote {Γ}{pv X} p = p
      Unquote {Γ}{A ⇒ B} p Δ f q = Unquote (app (⊢*-mon-neu f p) (Quote {Δ}{A} q))

      ⊩con-refl : {Γ : Con} → Γ ⊩con Γ
      ⊩con-refl {∅} = *
      ⊩con-refl {Γ , A} = mon-con (wk⊢* ⊢*-refl) (⊩con-refl {Γ})
                        , Unquote {Γ , A} (var zero) 

  nf : {Γ : Con}{A : Ty} → Γ ⊢ A → Nf Γ A
  nf {Γ}{A} t = complete' A (sound t)

  module normalisation_example (X : PropVar) where

    -- (λx.x) (λx.x)
    t : ∅ ⊢ pv X ⇒ pv X
    t = app (lam (var zero)) (lam (var zero))

    t' : Nf ∅ (pv X ⇒ pv X)
    t' =  {! nf t!}
