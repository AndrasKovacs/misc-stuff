
module DTDT where

open import Function

module Chapter01 where

  open import Data.Vec hiding (_>>=_; map; _⊛_)
  open import Data.Nat renaming (_+_ to _+ℕ_; _*_ to _*ℕ_)
  open import Data.Unit
  open import Data.Product hiding (map; swap)
  open import Data.Bool
  open import Data.Fin hiding (_+_)
  open import Relation.Binary.PropositionalEquality
  
  open import HeteroIndexed using ([_]_≅_)
  import HeteroIndexed as HI
  
  record EndoFunctor (F : Set → Set) : Set₁ where
    constructor rec  
    field
      map : ∀ {S T} → (S → T) → F S → F T
  open EndoFunctor ⦃...⦄ public

  record Applicative (F : Set → Set) : Set₁ where
    constructor rec
    infixl 2 _⊛_ 
    field
       pure : ∀ {X} → X → F X
       _⊛_  : ∀ {S T} → F (S → T) → F S → F T
    applicativeEndoFunctor : EndoFunctor F
    applicativeEndoFunctor = record {map = _⊛_ ∘ pure}
  open Applicative ⦃...⦄ public

  instance
    applicativeVec : ∀ {n} → Applicative (flip Vec n)
    applicativeVec = record { pure = replicate ; _⊛_ = Data.Vec._⊛_ }

    applicativeFun : ∀ {S} → Applicative λ X → S → X
    applicativeFun = record { pure = const ; _⊛_ = _ˢ_ }

  record Monad (F : Set → Set) : Set₁ where
    constructor rec  
    field
      return : ∀ {X} → X → F X
      _>>=_  : ∀ {S T} → F S → (S → F T) → F T
    monadApplicative : Applicative F
    monadApplicative = record {
        pure = return
      ; _⊛_ = λ mf mx → mf >>= λ f → mx >>= λ x → return (f x)
      }
  open Monad ⦃...⦄

  module _ where
    open import Data.Nat
    instance
      monadVec : ∀ {n} → Monad (flip Vec n)
      monadVec {zero}  = record { return = pure ; _>>=_ = λ _ _ → [] }
      monadVec {suc n} = record { return = pure ; _>>=_ = λ ma f → Data.Vec.map (head ∘ f) ma }

  instance
    applicativeId : Applicative id
    applicativeId = record { pure = id ; _⊛_ = id }

    applicativeComp : ∀ {F G} → Applicative F → Applicative G → Applicative (F ∘ G)
    applicativeComp apF apG = record {
      pure = Applicative.pure apF ∘ Applicative.pure apG  ;
      _⊛_ = liftA2 apF (Applicative._⊛_ apG) }
      where liftA2 : ∀ {A B C F} → Applicative F → (A → B → C) → F A → F B → F C
            liftA2 ap f a b = (ap Applicative.⊛ (ap Applicative.⊛ Applicative.pure ap f) a) b

  record Monoid (X : Set) : Set where
    constructor rec
    infixr 4 _∙_
    field
      ε   : X
      _∙_ : X → X → X
    monoidApplicative : Applicative (const X)
    monoidApplicative = rec (const ε) _∙_
  open Monoid ⦃...⦄ public
    
  instance
    applicative-× : ∀ {F G} → Applicative F → Applicative G → Applicative (λ X → F X × G X)
    applicative-× apF apG = rec
      (λ x → (Applicative.pure apF x) , Applicative.pure apG x)
      (λ {(ff , gf) (fx , gx) → ((apF Applicative.⊛ ff) fx) , ((apG Applicative.⊛ gf) gx) })

  record Traversable (F : Set → Set) : Set₁ where
    constructor rec
    field
      traverse : ∀ {G S T} ⦃ AG : Applicative G ⦄ → (S → G T) → F S → G (F T)
    traversableEndoFunctor : EndoFunctor F
    traversableEndoFunctor = rec traverse -- identity applicative
    
  open Traversable ⦃...⦄ public

  instance
    traversableVec : ∀ {n} → Traversable (flip Vec n)
    traversableVec = rec vtr
      where
        vtr : ∀ {A : Set}{n B F}⦃ _ : Applicative F ⦄ → (A → F B) → Vec A n → F (Vec B n)
        vtr f []               = pure []
        vtr ⦃ aF ⦄ f (a ∷ as) = pure ⦃ aF ⦄ _∷_ ⊛ f a ⊛ vtr ⦃ aF ⦄ f as
        
    endoFunctorVec : ∀ {n} → EndoFunctor (flip Vec n)
    endoFunctorVec = traversableEndoFunctor {{traversableVec}}


  transpose : ∀ {n m}{X : Set} → Vec (Vec X n) m → Vec (Vec X m) n
  transpose = traverse id

  crush : ∀ {A M F} ⦃ _ : Traversable F ⦄ ⦃ _ : Monoid M ⦄ → (A → M) → F A → M
  crush {{_}}{{m}} = traverse {T = ⊤} {{monoidApplicative {{m}}}}

  _⟨?⟩_ : ∀ {ℓ} {P : Bool → Set ℓ} → P true → P false → ∀ b → P b
  (t ⟨?⟩ f) true  = t
  (t ⟨?⟩ f) false = f

  _+_ : Set → Set → Set
  S + T = Σ Bool (S ⟨?⟩ T)

  record Normal : Set₁ where
    constructor _/_
    field
      Shape : Set
      size  : Shape → ℕ
    ⟦_⟧ₙ : Set → Set
    ⟦ X ⟧ₙ = Σ Shape (Vec X ∘ size)
  open Normal public
  infixr 0 _/_

  VecN : ℕ → Normal
  VecN n = ⊤ / const n

  ListN : Normal
  ListN = ℕ / id

  Kₙ : Set → Normal
  Kₙ A = A / const 0

  IKₙ : Normal
  IKₙ = VecN 1

  ⱽ_ = uncurry
  infix 0 ⱽ_

  _+ₙ_ : Normal → Normal → Normal
  (sha / sa) +ₙ (shb / sb) = sha + shb / ⱽ sa ⟨?⟩ sb

  _×ₙ_ : Normal → Normal → Normal
  (sha / sa) ×ₙ (shb / sb) = sha × shb / ⱽ λ f g → sa f +ℕ sb g
  
  nInj : ∀ {X} F G → ⟦ F ⟧ₙ X + ⟦ G ⟧ₙ X → ⟦ F +ₙ G ⟧ₙ X
  nInj F G (true  , sh , xs) = (true  , sh) , xs
  nInj F G (false , sh , xs) = (false , sh) , xs

  data _⁻¹_ {S T : Set} (f : S → T) : T → Set where
    from : ∀ s → f ⁻¹ f s

  nCase : ∀ {X} F G (s : ⟦ F +ₙ G ⟧ₙ X) → nInj F G ⁻¹ s
  nCase F G ((true  , sh) , xs) = from (true  , sh , xs)
  nCase F G ((false , sh) , xs) = from (false , sh , xs)

  nOut : ∀ {X} F G → ⟦ F +ₙ G ⟧ₙ X → ⟦ F ⟧ₙ X + ⟦ G ⟧ₙ X
  nOut F G x with nCase F G x
  nOut F G .(nInj F G s) | from s = s

  nPair : ∀ {X} F G → ⟦ F ⟧ₙ X × ⟦ G ⟧ₙ X → ⟦ F ×ₙ G ⟧ₙ X
  nPair F G ((shx , xs), (shy , ys)) = (shx , shy) , xs ++ ys

  instance
    listNMonoid : ∀ {X} → Monoid (⟦ ListN ⟧ₙ X)
    listNMonoid = rec (zero , []) (λ {(sx , xs) (sy , ys) → sx +ℕ sy , xs ++ ys})

    sumMonoid : Monoid ℕ
    sumMonoid = rec 0 _+ℕ_

    normalTraversable : (F : Normal) → Traversable ⟦ F ⟧ₙ
    normalTraversable F =
      rec (λ { {{aG}} f (sh , xs) → pure {{aG}} (_,_ sh) ⊛ traverse f xs})

  _∘ₙ_ : Normal → Normal → Normal
  F ∘ₙ (shb / sb) = ⟦ F ⟧ₙ shb / crush {{normalTraversable F}} sb

  sizeT : ∀ {F}⦃ TF : Traversable F ⦄ {X} → F X → ℕ
  sizeT = crush (const 1)

  normalT : ∀ F ⦃ TF : Traversable F ⦄ → Normal
  normalT F = F ⊤ / sizeT

  shapeT : ∀ {F}⦃ TF : Traversable F ⦄{X} → F X → F ⊤
  shapeT = traverse (const tt)

  -- toNormal : ∀ {F}{{TF : Traversable F}}{X} → F X → ⟦ normalT F ⟧ₙ X
  -- toNormal fx = shapeT fx , {!!}

  _→ₙ_ : Normal → Normal → Set
  F →ₙ G = (s : Shape F) → ⟦ G ⟧ₙ (Fin (size F s))

  nMorph : ∀ {F G} → F →ₙ G → (∀ {X} → ⟦ F ⟧ₙ X → ⟦ G ⟧ₙ X)
  nMorph f (s , xs) with f s
  ... | s' , is = s' , map (flip lookup xs) is

  morphN : ∀ {F G} → (∀ {X} → ⟦ F ⟧ₙ X → ⟦ G ⟧ₙ X) → F →ₙ G
  morphN {F} f s = f (s , allFin (size F s))

  _⊗_ : Normal → Normal → Normal
  (sha / sa) ⊗ (shb / sb) = sha × shb / ⱽ λ f g → sa f *ℕ sb g

  open import Data.Nat.Properties.Simple

  -- just reshape matrix
  swap : (F G : Normal) → (F ⊗ G) →ₙ (G ⊗ F)
  swap F G (sha , shb) rewrite *-comm (size F sha) (size G shb) =
   (shb , sha) , allFin _

  chop : ∀ {n m}{A : Set} → Vec A (n *ℕ m) → Vec (Vec A m) n
  chop {zero}     as = []
  chop {suc n}{m} as = take m as ∷ chop (drop m as)

  -- transpose (the circuitous way)
  swap' : (F G : Normal) → (F ⊗ G) →ₙ (G ⊗ F)
  swap' F G = morphN
    (λ {((sa , sb) , xs)
    → (sb , sa) , concat (transpose (chop {size F sa}{size G sb} xs))})
    
  rep-sum : ∀ {A : Set}{f : A → ℕ}{x} n → n *ℕ f x ≡ crush f (replicate {n = n} x)
  rep-sum zero = refl
  rep-sum {A}{f}{x}(suc n) = cong (_+ℕ_ (f x)) (rep-sum {A} {f} {x} n)

  drop' : (F G : Normal) → (F ⊗ G) →ₙ (F ∘ₙ G)
  drop' F G (sha , shb) =
    (sha , replicate shb) ,
    subst (Vec (Fin (size F sha *ℕ size G shb))) (rep-sum (size F sha)) (allFin _)

  record MonoidOK X ⦃ M : Monoid X ⦄ : Set where
    constructor rec
    field
      absorbL : (x : X) → ε ∙ x ≡ x
      absorbR : (x : X) → x ∙ ε ≡ x
      assoc   : (x y z : X) → (x ∙ y) ∙ z ≡ x ∙ (y ∙ z)

  ++-[] : ∀ {α}{A : Set α} {n} (xs : Vec A n) → [ Vec A ] (xs ++ []) ≅ xs
  ++-[] []       = HI.refl
  ++-[] (x ∷ xs) = HI.cong (_∷_ x) (++-[] xs)

  ++-assoc :
    ∀ {α}{A : Set α} {n m k} (xs : Vec A n)(ys : Vec A m)(zs : Vec A k)
    → [ Vec A ] ((xs ++ ys) ++ zs) ≅ (xs ++ ys ++ zs)
  ++-assoc []       ys zs = HI.refl
  ++-assoc (x ∷ xs) ys zs = HI.cong (_∷_ x) (++-assoc xs ys zs)

  listNMonoidOK : ∀ {X} → MonoidOK (⟦ ListN ⟧ₙ X)
  listNMonoidOK {X} = record {
    absorbL = λ _ → refl ;
    absorbR = ⱽ λ s xs → HI.≅→Σ (++-[] xs) ;
    assoc   = λ {(sx , xs) (sy , ys) (sz , zs) → HI.≅→Σ (++-assoc xs ys zs)}
    }

  record MonoidHom {X} ⦃ MX : Monoid X ⦄{Y}⦃ MY : Monoid Y ⦄ (f : X → Y) : Set where
    field
      resp-ε : f ε ≡ ε
      resp-∙ : ∀ x x' → f (x ∙ x') ≡ f x ∙ f x'

  fstHom : ∀ {X} → MonoidHom {⟦ ListN ⟧ₙ X} {ℕ} proj₁
  fstHom {X} = record { resp-ε = refl ; resp-∙ = λ x x' → refl }

  _≐_ : ∀ {α β}{A : Set α}{B : A → Set β}(f g : ∀ x → B x) → Set _
  f ≐ g = ∀ x → f x ≡ g x
  infix 1 _≐_

  record EndoFunctorOKP F ⦃ FF : EndoFunctor F ⦄ : Set₁ where
    field
      endoFunctorId : ∀ {X} → map {{FF}} {X} id ≐ id
      endoFunctorCo : ∀ {R S T}(f : S → T)(g : R → S) → map {{FF}} f ∘ map g ≐ map (f ∘ g)

  record ApplicativeOKP F ⦃ AF : Applicative F ⦄ : Set₁ where
    field
      lawId : ∀ {X}(x : F X) → (pure {{AF}} id ⊛ x) ≡ x
      lawCo : ∀ {R S T} (f : F (S → T))(g : F (R → S))(r : F R) →
        (pure {{AF}} (λ f g → f ∘ g) ⊛ f ⊛ g ⊛ r) ≡ (f ⊛ (g ⊛ r))
      lawHom : ∀ {S T}(f : S → T)(s : S) → (pure {{AF}} f ⊛ pure s) ≡ pure (f s)
      lawCom : ∀ {S T}(f : F (S → T))(s : S) → (f ⊛ pure s) ≡ (pure {{AF}} (λ f → f s) ⊛ f)

    applicativeEndoFunctorOKP : EndoFunctorOKP F {{applicativeEndoFunctor}}
    applicativeEndoFunctorOKP = record {
      endoFunctorId = lawId ;
      endoFunctorCo = λ f g r →
        {!trans {i = pure {{AF}} f ⊛ (pure {{AF}} g ⊛ r)}
        
         

        !}

      }
      
