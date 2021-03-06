
module Chapter01 where

open import Function
open import Data.Vec hiding (_>>=_; map; _⊛_)
open import Data.Vec.Properties
open import Data.Nat renaming (_+_ to _+ℕ_; _*_ to _*ℕ_) hiding (eq?)
open import Data.Nat.Properties.Simple
open import Data.Unit
open import Data.Product hiding (map; swap)
open import Data.Bool
open import Data.Fin hiding (_+_)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary.Decidable hiding (map)
open import Relation.Nullary
open import Data.Empty
import Level as L

-- open import HeteroIndexed using ([_]_≅_)
-- import HeteroIndexed as HI


record EndoFunctor (F : Set → Set) : Set₁ where
  constructor rec  
  field
    map : ∀ {S T} → (S → T) → F S → F T
open EndoFunctor ⦃...⦄ public

record Applicative (F : Set → Set) : Set₁ where
  constructor rec
  infixl 4 _⊛_ 
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

one : ∀ {X} → X → ⟦ ListN ⟧ₙ X
one x = (1 , x ∷ [])

contentsT : ∀ {F}{{TF : Traversable F}}{X} → F X → ⟦ ListN ⟧ₙ X
contentsT = crush one

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
    absorbL : (x : X) → (ε ∙ x) ≡ x
    absorbR : (x : X) → (x ∙ ε) ≡ x
    assoc   : (x y z : X) → ((x ∙ y) ∙ z) ≡ (x ∙ (y ∙ z))

-- ++-[] : ∀ {α}{A : Set α} {n} (xs : Vec A n) → [ Vec A ] (xs ++ []) ≅ xs
-- ++-[] []       = HI.refl
-- ++-[] (x ∷ xs) = HI.cong (_∷_ x) (++-[] xs)

-- ++-assoc :
--   ∀ {α}{A : Set α} {n m k} (xs : Vec A n)(ys : Vec A m)(zs : Vec A k)
--   → [ Vec A ] ((xs ++ ys) ++ zs) ≅ (xs ++ ys ++ zs)
-- ++-assoc []       ys zs = HI.refl
-- ++-assoc (x ∷ xs) ys zs = HI.cong (_∷_ x) (++-assoc xs ys zs)

-- listNMonoidOK : ∀ {X} → MonoidOK (⟦ ListN ⟧ₙ X)
-- listNMonoidOK {X} = record {
--   absorbL = λ _ → refl ;
--   absorbR = ⱽ λ s xs → HI.≅→Σ (++-[] xs) ;
--   assoc   = λ {(sx , xs) (sy , ys) (sz , zs) → HI.≅→Σ (++-assoc xs ys zs)}
--   }

-- record MonoidHom {X} ⦃ MX : Monoid X ⦄{Y}⦃ MY : Monoid Y ⦄ (f : X → Y) : Set where
--   field
--     resp-ε : f ε ≡ ε
--     resp-∙ : ∀ x x' → (f (x ∙ x')) ≡ (f x ∙ f x')

-- fst : ∀ {X} → ⟦ ListN ⟧ₙ X → ℕ
-- fst (n , xs) = n

-- fstHom : ∀ {X} → MonoidHom {⟦ ListN ⟧ₙ X} {ℕ} fst
-- fstHom {X} = record { resp-ε = refl ; resp-∙ = λ x x' → refl }

-- _≐_ : ∀ {α β}{A : Set α}{B : A → Set β}(f g : ∀ x → B x) → Set _
-- f ≐ g = ∀ x → f x ≡ g x
-- infix 1 _≐_

-- record EndoFunctorOKP F ⦃ FF : EndoFunctor F ⦄ : Set₁ where
--   field
--     endoFunctorId : ∀ {X} → map {{FF}} {X} id ≐ id
--     endoFunctorCo : ∀ {R S T}(f : S → T)(g : R → S) → map {{FF}} f ∘ map g ≐ map (f ∘ g)

-- record ApplicativeOKP F ⦃ AF' : Applicative F ⦄ : Set₁ where
--   constructor rec
--   open module AF = Applicative AF' -- or else I'm going blind by the record noise
--   field
--     lawId : ∀ {X}(x : F X) → (AF.pure id AF.⊛ x) ≡ x
--     lawCo : ∀ {R S T} (f : F (S → T))(g : F (R → S))(r : F R) →
--       (AF.pure  (λ f g → f ∘ g) AF.⊛ f AF.⊛ g AF.⊛ r) ≡ (f AF.⊛ (g AF.⊛ r))
--     lawHom : ∀ {S T}(f : S → T)(s : S) → (AF.pure f AF.⊛ AF.pure s) ≡ AF.pure (f s)
--     lawCom : ∀ {S T}(f : F (S → T))(s : S) → (f AF.⊛ AF.pure s) ≡ (AF.pure (λ f → f s) AF.⊛ f)

--   applicativeEndoFunctorOKP : EndoFunctorOKP F {{AF.applicativeEndoFunctor}}
--   applicativeEndoFunctorOKP = 
--     record {
--       endoFunctorId = lawId ;
--       endoFunctorCo = co
--     } where
--     open module FF = EndoFunctor (AF.applicativeEndoFunctor)
--     open ≡-Reasoning

--     -- I'm crying right now. Goddammit, Agda.
--     co : ∀ {R S T}(f : S → T) (g : R → S) r → FF.map f (FF.map g r) ≡ FF.map (f ∘ g) r
--     co f g r =
--       begin
--         FF.map f (FF.map g r)
--       ≡⟨ sym (lawCo (AF.pure f) (AF.pure g) r) ⟩
--        AF._⊛_ (AF._⊛_ (FF.map (λ f₁ → _∘_ f₁) (AF.pure f)) (AF.pure g)) r
--       ≡⟨ cong (λ x → AF._⊛_ (AF._⊛_ x (AF.pure g)) r) (lawHom (λ f₁ g₁ → f₁ ∘ g₁) f) ⟩
--         (AF.pure (λ g₁ → f ∘ g₁) AF.⊛ AF.pure g AF.⊛ r)
--       ≡⟨ cong (λ x → AF._⊛_ x r) (lawHom (_∘_ f) g) ⟩
--         (AF.pure (f ∘ g) AF.⊛ r)
--       ∎

-- vecApplicativeOK : ∀ {n} → ApplicativeOKP (flip Vec n)
-- vecApplicativeOK = record {
--   lawId = lawId ;
--   lawCo = lawCo ;
--   lawHom = lawHom ;
--   lawCom = lawCom
--   }
--   where
--     lawId : ∀ {n}{X : Set}(xs : Vec X n) → (replicate id ⊛ xs) ≡ xs
--     lawId []       = refl
--     lawId (x ∷ xs) = cong (_∷_ x) (lawId xs)

--     lawCo :
--       ∀ {n R S T}(fs : Vec (S → T) n)(gs : Vec (R → S) n)(r : Vec R n)
--       → ((replicate (λ f g → f ∘ g) ⊛ fs) ⊛ gs ⊛ r) ≡ (fs ⊛ (gs ⊛ r))
--     lawCo [] gs r = refl
--     lawCo (f ∷ fs) (g ∷ gs) (r ∷ rs) = cong (_∷_ (f (g r))) (lawCo fs gs rs)

--     lawHom : ∀ {n}{S T}(f : S → T) s → (replicate {n = n} f ⊛ replicate s) ≡ replicate (f s)
--     lawHom {zero}   f s = refl
--     lawHom {suc n₁} f s = cong (_∷_ (f s)) (lawHom {n₁} f s)

--     lawCom : ∀ {n S T}(fs : Vec (S → T) n) s → (fs ⊛ replicate s) ≡ (replicate (λ f → f s) ⊛ fs)
--     lawCom []       s = refl
--     lawCom (f ∷ fs) s = cong (_∷_ (f s)) (lawCom fs s)

-- _~>_ : (F G : Set → Set) → Set₁
-- F ~> G = ∀ {X} → F X → G X

-- record AppHom {F}{{AF : Applicative F}}{G}{{ AG : Applicative G}}(k : F ~> G) : Set₁ where
--   constructor rec
--   field
--     respPure : ∀ {X} (x : X) → k (pure x) ≡ pure x
--     resp-⊛   : ∀ {S T}(f : F (S → T))(s : F S) → k (f ⊛ s) ≡ (k f ⊛ k s)

-- monoidApplicativeHom :
--   ∀ {X}{{MX : Monoid X}}{Y}{{MY : Monoid Y}}(f : X → Y){{hf : MonoidHom f}}
--   → AppHom {{monoidApplicative {{MX}}}}{{monoidApplicative {{MY}}}} f
-- monoidApplicativeHom f {{hf}} = record {
--   respPure = λ x → MonoidHom.resp-ε hf ;
--   resp-⊛ = MonoidHom.resp-∙ hf }

-- homSum :
--   ∀ {F G}{{AF : Applicative F}}{{AG : Applicative G}}(f : F ~> G)
--   → Applicative λ X → F X + G X
-- homSum {F}{G} k = rec
--   (λ x   → true , pure x)
--   (λ {(true  , ff)(true  , fx) → true  , (ff ⊛ fx);
--       (true  , ff)(false , gx) → false , (k ff ⊛ gx);
--       (false , gf)(true  , fx) → false , (gf ⊛ k fx);
--       (false , gf)(false , gx) → false , (gf ⊛ gx)})

-- homSumOKP :
--   ∀ {F G}{{AF : Applicative F}}{{AG : Applicative G}}
--   → ApplicativeOKP F → ApplicativeOKP G
--   → (k : F ~> G) → AppHom k
--   → ApplicativeOKP _ {{homSum k}}
-- homSumOKP {F}{G}{{AF}}{{AG}}
--  (rec lawId lawCo lawHom lawCom)
--  (rec lawId₁ lawCo₁ lawHom₁ lawCom₁) k
--  (rec respPure resp-⊛) = rec lawId' lawCo' lawHom' lawCom'
--  where
--    open module HS = Applicative (homSum k)
--    open module AG = Applicative AG
--    open module AF = Applicative AF

--    lawCom' : ∀ {S T}(f : F (S → T) + G (S → T)) s → (f HS.⊛ HS.pure s) ≡ (HS.pure (λ f → f s) HS.⊛ f)
--    lawCom' (true  , ff) s = cong (_,_ true) (lawCom ff s)
--    lawCom' {S}{T}(false , gf) s
--        rewrite
--        respPure s
--      | respPure {(S → T) → T} (λ f → f s)
--      | lawCom₁ gf s
--      = refl

--    lawHom' : ∀ {S T}(f : S → T) s → (HS.pure f HS.⊛ HS.pure s) ≡ HS.pure (f s)
--    lawHom' f s = cong (_,_ true) (lawHom f s)

--    lawId' : ∀ {X} (x : F X + G X) → (HS.pure id HS.⊛ x) ≡ x
--    lawId' (true  , fx) = cong (_,_ true) (lawId fx)
--    lawId' {X}(false , gx) rewrite respPure {X → X} id | lawId₁ gx = refl

--    lawCo' :
--      ∀ {R S T}(f : F (S → T) + G (S → T))
--      (g : F (R → S) + G (R → S)) (r : F R + G R)
--      → (HS.pure (λ f g → f ∘ g) HS.⊛ f HS.⊛ g HS.⊛ r) ≡ (f HS.⊛ (g HS.⊛ r))
     
--    lawCo' (true  , f') (true  , g') (true  , r) =
--      cong (_,_ true) (lawCo f' g' r)
   
--    lawCo'{R}{S}{T} (true  , f') (false , g') (true  , r)
--        rewrite
--        resp-⊛ {S → T}{(R → S) → (R → T)} (AF.pure (λ f g x → f (g x))) f'
--      | sym (lawCo₁ (k f') g' (k r))
--      | respPure (((S → T) → (R → S) → (R → T)) ∋ (λ f g → f ∘ g))
--      = refl
     
--    lawCo' {R}{S}{T}(false , f') (true  , g') (true  , r)
--        rewrite
--        respPure (((S → T) → (R → S) → (R → T)) ∋ (λ f g → f ∘ g))
--      | lawCo₁ f' (k g') (k r)
--      | resp-⊛ g' r
--      = refl
     
--    lawCo'{R}{S}{T}(false , f') (false , g') (true  , r)
--        rewrite
--        respPure (((S → T) → (R → S) → (R → T)) ∋ (λ f g → f ∘ g))
--      | lawCo₁ f' g' (k r)         
--      = refl
   
--    lawCo' {R}{S}{T}(true  , f') (true  , g') (false , r)
--        rewrite
--        resp-⊛ {R → S}{R → T} (AF.pure (λ f g x → f (g x)) AF.⊛ f') g'
--      | resp-⊛ {S → T}{(R → S) → (R → T)} (AF.pure (λ f g x → f (g x))) f'
--      | respPure (((S → T) → (R → S) → (R → T)) ∋ (λ f g → f ∘ g))
--      | lawCo₁ (k f') (k g') r
--      = refl

--    lawCo' {R}{S}{T}(true  , f') (false , g') (false , r)
--        rewrite
--        resp-⊛ {S → T}{(R → S) → (R → T)} (AF.pure (λ f g x → f (g x))) f'
--      | respPure (((S → T) → (R → S) → (R → T)) ∋ (λ f g → f ∘ g))
--      | lawCo₁ (k f') g' r
--      = refl
     
--    lawCo' {R}{S}{T}(false , f') (true  , g') (false , r)
--        rewrite
--        respPure (((S → T) → (R → S) → (R → T)) ∋ (λ f g → f ∘ g))
--      | lawCo₁ f' (k g') r
--      = refl

--    lawCo' {R}{S}{T}(false , f') (false , g') (false , r)
--        rewrite
--        respPure (((S → T) → (R → S) → (R → T)) ∋ (λ f g → f ∘ g))
--      | lawCo₁ f' g' r
--      = refl

-- record TraversableOKP F {{TF : Traversable F}} : Set₁ where
--   constructor rec
--   field
--     lawId : ∀ {X} (xs : F X) → traverse id xs ≡ xs
--     lawCo :
--       ∀ {G} {{AG : Applicative G}}{H}{{AH : Applicative H}}
--         {R S T} (g : S → G T)(h : R → H S)(rs : F R)
--       → let EH = EndoFunctor H ∋ applicativeEndoFunctor
--         in map {H} (traverse g) (traverse h rs)
--            ≡
--            traverse {{TF}} {{applicativeComp AH AG}} (map {H} g ∘ h) rs
--     lawHom :
--       ∀ {G}{{AG : Applicative G}}{H}{{AH : Applicative H}}
--         (h : G ~> H) {S T}(g : S → G T) 
--         → AppHom h → (ss : F S)
--         → traverse (h ∘ g) ss ≡ h (traverse g ss)

-- data Tree (N : Normal) : Set where
--   ⟨_⟩ : ⟦ N ⟧ₙ (Tree N) → Tree N

-- NatT : Normal
-- NatT = Bool / 0 ⟨?⟩ 1

-- zeroT : Tree NatT
-- zeroT = ⟨ true , [] ⟩

-- sucT : Tree NatT → Tree NatT
-- sucT n = ⟨ false , n ∷ [] ⟩

-- NatInd :
--   ∀ {α}(P : Tree NatT → Set α)
--   → P zeroT
--   → (∀ n → P n → P (sucT n))
--   → ∀ n → P n
-- NatInd P z f ⟨ true , [] ⟩      = z
-- NatInd P z f ⟨ false , x ∷ [] ⟩ = f x (NatInd P z f x)  

-- All : ∀ {α}{A : Set}(P : A → Set α) {n} → Vec A n → Set α
-- All P []       = L.Lift ⊤
-- All P (x ∷ xs) = P x × All P xs

-- induction :
--   ∀ {α} N (P : Tree N → Set α)
--   → (∀ s (ts : Vec (Tree N) (size N s)) → All P ts → P ⟨ s , ts ⟩)
--   → ∀ t → P t
-- induction N P f ⟨ s , ts ⟩ = f s ts (hyps ts) where
--   hyps : ∀ {n} (ts : Vec (Tree N) n) → All P ts
--   hyps []       = L.lift tt
--   hyps (t ∷ ts) = induction N P f t , hyps ts

-- eq? :
--   ∀ N (sheq? : (s s' : Shape N) → Dec (s ≡ s'))
--   → (t t' : Tree N) → Dec (t ≡ t')
-- eq? N sheq = induction N
--   (λ t → ∀ t' → Dec (t ≡ t'))
--   step
--   where

--     vecEq :
--       ∀ {n}{A : Set}(xs : Vec A n)
--       (pxs : All (λ x → ∀ x' → Dec (x ≡ x')) xs)
--       → ∀ xs' → Dec (xs ≡ xs')
--     vecEq [] (L.lift tt) [] = yes refl
--     vecEq (x ∷ xs) (px , pxs) (x' ∷ xs') with px x' | vecEq xs pxs xs'
--     vecEq (x' ∷ xs) (px , pxs) (.x' ∷ .xs) | yes refl | yes refl = yes refl
--     vecEq (x' ∷ xs) (px , pxs) (.x' ∷ xs') | yes refl | no ¬p =
--       no (λ x → ¬p (proj₂ (∷-injective x)))
--     vecEq (x ∷ xs) (px , pxs) (x' ∷ xs') | no ¬p | p =
--       no (λ x₁ → ¬p $ proj₁ $ ∷-injective x₁)

--     Tree-injₛ : ∀ {s s' ts ts'} → (Tree N ∋ ⟨ s , ts ⟩) ≡ ⟨ s' , ts' ⟩ → s ≡ s'
--     Tree-injₛ refl = refl

--     Tree-injₜ : ∀ {s ts ts'} → (Tree N ∋ ⟨ s , ts ⟩) ≡ ⟨ s , ts' ⟩ → ts ≡ ts'
--     Tree-injₜ refl = refl

--     step :
--       ∀ s (ts : Vec (Tree N) (size N s))
--       → All (λ t → (t' : Tree N) → Dec (t ≡ t')) ts
--       → ∀ t' → Dec (⟨ s , ts ⟩ ≡ t')
--     step s ts pts ⟨ s' , ts' ⟩ with sheq s s'
--     step s ts pts ⟨ .s , ts' ⟩ | yes refl with vecEq ts pts ts'
--     step s ts pts ⟨ .s , .ts ⟩ | yes refl | yes refl = yes refl
--     step s ts pts ⟨ .s , ts' ⟩ | yes refl | no ¬p = no (¬p ∘ Tree-injₜ)
--     step s ts pts ⟨ s' , ts' ⟩ | no ¬p = no (¬p ∘ Tree-injₛ)


