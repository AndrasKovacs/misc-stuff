


module Chapter01 where

-- NOTE: type classes removed because they drive me mad in proofs

open import Function
open import Data.Vec hiding (_>>=_; map; _⊛_; applicative)
open import Data.Nat renaming (_+_ to _+ℕ_; _*_ to _*ℕ_)
open import Data.Nat.Properties.Simple
open import Data.Unit
open import Data.Product hiding (map; swap)
open import Data.Bool
open import Data.Fin hiding (_+_)
open import Relation.Binary.PropositionalEquality

open import HeteroIndexed using ([_]_≅_)
import HeteroIndexed as HI

record Functor (F : Set → Set) : Set₁ where
  constructor rec  
  field
    map : ∀ {A B} → (A → B) → F A → F B
module F = Functor    

record Applicative (F : Set → Set) : Set₁ where
  constructor rec
  field
     pure : ∀ {A} → A → F A
     _⊛_  : ∀ {A B} → F (A → B) → F A → F B
  infixl 4 _⊛_ 
  functor : Functor F
  functor = record {map = _⊛_ ∘ pure}
module A = Applicative  

apVec : ∀ {n} → Applicative (flip Vec n)
apVec = record { pure = replicate ; _⊛_ = Data.Vec._⊛_ }

apFun : ∀ {S} → Applicative λ A → S → A
apFun = record { pure = const ; _⊛_ = _ˢ_ }

record Monad (M : Set → Set) : Set₁ where
  constructor rec  
  field
    return : ∀ {A} → A → M A
    _>>=_  : ∀ {A B} → M A → (A → M B) → M B
  applicative : Applicative M
  applicative = record {
      pure = return
    ; _⊛_ = λ mf mx → mf >>= λ f → mx >>= λ x → return (f x)
    }

monadVec : ∀ {n} → Monad (flip Vec n)
monadVec {zero}  = record { return = replicate ; _>>=_ = λ _ _ → [] }
monadVec {suc n} = record { return = replicate ; _>>=_ = λ ma f → Data.Vec.map (head ∘ f) ma }

apId : Applicative id
apId = record { pure = id ; _⊛_ = id }

apComp : ∀ {F G} → Applicative F → Applicative G → Applicative (F ∘ G)
apComp apF apG = record {
  pure = AF.pure ∘ AG.pure ;
  _⊛_ = λ a b → AF.pure AG._⊛_ AF.⊛ a AF.⊛ b }
  where
    open module AF = Applicative apF
    open module AG = Applicative apG

record Monoid (A : Set) : Set where
  constructor rec
  infixr 4 _∙_
  field
    ε   : A
    _∙_ : A → A → A
  applicative : Applicative (const A)
  applicative = rec (const ε) _∙_
module M = Monoid

applicative-× : ∀ {F G} → Applicative F → Applicative G → Applicative (λ X → F X × G X)
applicative-× apF apG = rec
  (λ x → (Applicative.pure apF x) , Applicative.pure apG x)
  (λ {(ff , gf) (fx , gx) → ((apF Applicative.⊛ ff) fx) , ((apG Applicative.⊛ gf) gx) })

record Traversable (T : Set → Set) : Set₁ where
  constructor rec
  field
    traverse : ∀ {A B F} → Applicative F → (A → F B) → T A → F (T B)
  functor : Functor T
  functor = rec (traverse apId)
module T = Traversable

vtr : ∀ {A : Set}{n B F} → Applicative F → (A → F B) → Vec A n → F (Vec B n)
vtr (rec pure _⊛_) f []       = pure []
vtr (rec pure _⊛_) f (a ∷ as) = ((pure _∷_) ⊛ f a) ⊛ vtr (rec pure _⊛_) f as
  
travVec : ∀ n → Traversable (flip Vec n)
travVec n = rec vtr
    
functorVec : ∀ {n} → Functor (flip Vec n)
functorVec = T.functor (travVec _)

transpose : ∀ {n m}{A : Set} → Vec (Vec A n) m → Vec (Vec A m) n
transpose {n}{m} = T.traverse (travVec _) apVec id

crush : ∀ {A M F} → Traversable F → Monoid M → (A → M) → F A → M
crush {A}{M}{F}(rec traverse) mon = traverse {A}{F M}{const M} (M.applicative mon)

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

listNMonoid : ∀ {X} → Monoid (⟦ ListN ⟧ₙ X)
listNMonoid = rec (zero , []) (λ {(sx , xs) (sy , ys) → sx +ℕ sy , xs ++ ys})

sumMonoid : Monoid ℕ
sumMonoid = rec 0 _+ℕ_

travNormal : (F : Normal) → Traversable ⟦ F ⟧ₙ
travNormal F = rec travNorm
  where
    travNorm : ∀ {A B G} → Applicative G → (A → G B) → ⟦ F ⟧ₙ A → G (⟦ F ⟧ₙ B)
    travNorm ap f (sh , as) = pure (_,_ sh) ⊛ traverse ap f as
      where open Applicative ap
            open Traversable (travVec $ size F sh)

_∘ₙ_ : Normal → Normal → Normal
F ∘ₙ (shb / sb) = ⟦ F ⟧ₙ shb / crush (travNormal F) sumMonoid sb

sizeT : ∀ {F} → Traversable F → ∀ {X} → F X → ℕ
sizeT trav = crush trav sumMonoid (const 1)

normalT : ∀ F → Traversable F → Normal
normalT F tr = F ⊤ / sizeT tr

shapeT : ∀ {F} → Traversable F → ∀ {X} → F X → F ⊤
shapeT (rec traverse) = traverse apId (const tt)

one : ∀ {X} → X → ⟦ ListN ⟧ₙ X
one x = (1 , x ∷ [])

contentsT : ∀ {F} → Traversable F → ∀ {X} → F X → ⟦ ListN ⟧ₙ X
contentsT tr = crush tr listNMonoid one

-- toNormal : ∀ {F}{{TF : Traversable F}}{X} → F X → ⟦ normalT F ⟧ₙ X
-- toNormal fx = shapeT fx , {!!}

_→ₙ_ : Normal → Normal → Set
F →ₙ G = (s : Shape F) → ⟦ G ⟧ₙ (Fin (size F s))

nMorph : ∀ {F G} → F →ₙ G → (∀ {X} → ⟦ F ⟧ₙ X → ⟦ G ⟧ₙ X)
nMorph f (s , xs) with f s
... | s' , is = s' , Data.Vec.map (flip lookup xs) is

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
  
rep-sum :
  ∀ {A : Set}{f : A → ℕ}{x} n
  → n *ℕ f x ≡ vtr {A}{n}{A} (M.applicative sumMonoid) f (replicate {n = n} x)
rep-sum zero = refl
rep-sum {A}{f}{x}(suc n) rewrite rep-sum {A}{f}{x} n = refl

drop' : (F G : Normal) → (F ⊗ G) →ₙ (F ∘ₙ G)
drop' F G (sha , shb) =
  (sha , replicate shb) , {!!}


-- -- record MonoidOK X ⦃ M : Monoid X ⦄ : Set where
-- --   constructor rec
-- --   field
-- --     absorbL : (x : X) → ε ∙ x ≡ x
-- --     absorbR : (x : X) → x ∙ ε ≡ x
-- --     assoc   : (x y z : X) → (x ∙ y) ∙ z ≡ x ∙ (y ∙ z)

-- -- ++-[] : ∀ {α}{A : Set α} {n} (xs : Vec A n) → [ Vec A ] (xs ++ []) ≅ xs
-- -- ++-[] []       = HI.refl
-- -- ++-[] (x ∷ xs) = HI.cong (_∷_ x) (++-[] xs)

-- -- ++-assoc :
-- --   ∀ {α}{A : Set α} {n m k} (xs : Vec A n)(ys : Vec A m)(zs : Vec A k)
-- --   → [ Vec A ] ((xs ++ ys) ++ zs) ≅ (xs ++ ys ++ zs)
-- -- ++-assoc []       ys zs = HI.refl
-- -- ++-assoc (x ∷ xs) ys zs = HI.cong (_∷_ x) (++-assoc xs ys zs)

-- -- listNMonoidOK : ∀ {X} → MonoidOK (⟦ ListN ⟧ₙ X)
-- -- listNMonoidOK {X} = record {
-- --   absorbL = λ _ → refl ;
-- --   absorbR = ⱽ λ s xs → HI.≅→Σ (++-[] xs) ;
-- --   assoc   = λ {(sx , xs) (sy , ys) (sz , zs) → HI.≅→Σ (++-assoc xs ys zs)}
-- --   }

-- record MonoidHom {X} ⦃ MX : Monoid X ⦄{Y}⦃ MY : Monoid Y ⦄ (f : X → Y) : Set where
--   field
--     resp-ε : f ε ≡ ε
--     resp-∙ : ∀ x x' → f (x ∙ x') ≡ f x ∙ f x'

-- fst : ∀ {X} → ⟦ ListN ⟧ₙ X → ℕ
-- fst (n , xs) = n

-- fstHom : ∀ {X} → MonoidHom {⟦ ListN ⟧ₙ X} {ℕ} fst
-- fstHom {X} = record { resp-ε = refl ; resp-∙ = λ x x' → refl }

-- -- _≐_ : ∀ {α β}{A : Set α}{B : A → Set β}(f g : ∀ x → B x) → Set _
-- -- f ≐ g = ∀ x → f x ≡ g x
-- -- infix 1 _≐_

-- -- record EndoFunctorOKP F ⦃ FF : EndoFunctor F ⦄ : Set₁ where
-- --   field
-- --     endoFunctorId : ∀ {X} → map {{FF}} {X} id ≐ id
-- --     endoFunctorCo : ∀ {R S T}(f : S → T)(g : R → S) → map {{FF}} f ∘ map g ≐ map (f ∘ g)

-- record ApplicativeOKP F ⦃ AF' : Applicative F ⦄ : Set₁ where
--   constructor rec
--   open module AF = Applicative AF' -- or else I'm going blind by the record noise
--   field
--     lawId : ∀ {X}(x : F X) → (AF.pure id AF.⊛ x) ≡ x
--     lawCo : ∀ {R S T} (f : F (S → T))(g : F (R → S))(r : F R) →
--       (AF.pure  (λ f g → f ∘ g) AF.⊛ f AF.⊛ g AF.⊛ r) ≡ (f AF.⊛ (g AF.⊛ r))
--     lawHom : ∀ {S T}(f : S → T)(s : S) → (AF.pure f AF.⊛ AF.pure s) ≡ AF.pure (f s)
--     lawCom : ∀ {S T}(f : F (S → T))(s : S) → (f AF.⊛ AF.pure s) ≡ (AF.pure (λ f → f s) AF.⊛ f)

-- --   applicativeEndoFunctorOKP : EndoFunctorOKP F {{AF.applicativeEndoFunctor}}
-- --   applicativeEndoFunctorOKP = 
-- --     record {
-- --       endoFunctorId = lawId ;
-- --       endoFunctorCo = co
-- --     } where
-- --     open module FF = EndoFunctor (AF.applicativeEndoFunctor)
-- --     open ≡-Reasoning

-- --     -- I'm crying right now. Goddammit, Agda.
-- --     co : ∀ {R S T}(f : S → T) (g : R → S) r → FF.map f (FF.map g r) ≡ FF.map (f ∘ g) r
-- --     co f g r =
-- --       begin
-- --         FF.map f (FF.map g r)
-- --       ≡⟨ sym (lawCo (AF.pure f) (AF.pure g) r) ⟩
-- --        AF._⊛_ (AF._⊛_ (FF.map (λ f₁ → _∘_ f₁) (AF.pure f)) (AF.pure g)) r
-- --       ≡⟨ cong (λ x → AF._⊛_ (AF._⊛_ x (AF.pure g)) r) (lawHom (λ f₁ g₁ → f₁ ∘ g₁) f) ⟩
-- --         (AF.pure (λ g₁ → f ∘ g₁) AF.⊛ AF.pure g AF.⊛ r)
-- --       ≡⟨ cong (λ x → AF._⊛_ x r) (lawHom (_∘_ f) g) ⟩
-- --         (AF.pure (f ∘ g) AF.⊛ r)
-- --       ∎

-- -- vecApplicativeOK : ∀ {n} → ApplicativeOKP (flip Vec n)
-- -- vecApplicativeOK = record {
-- --   lawId = lawId ;
-- --   lawCo = lawCo ;
-- --   lawHom = lawHom ;
-- --   lawCom = lawCom
-- --   }
-- --   where
-- --     lawId : ∀ {n}{X : Set}(xs : Vec X n) → (replicate id ⊛ xs) ≡ xs
-- --     lawId []       = refl
-- --     lawId (x ∷ xs) = cong (_∷_ x) (lawId xs)

-- --     lawCo :
-- --       ∀ {n R S T}(fs : Vec (S → T) n)(gs : Vec (R → S) n)(r : Vec R n)
-- --       → (replicate (λ f g → f ∘ g) ⊛ fs) ⊛ gs ⊛ r ≡ fs ⊛ (gs ⊛ r)
-- --     lawCo [] gs r = refl
-- --     lawCo (f ∷ fs) (g ∷ gs) (r ∷ rs) = cong (_∷_ (f (g r))) (lawCo fs gs rs)

-- --     lawHom : ∀ {n}{S T}(f : S → T) s → replicate {n = n} f ⊛ replicate s ≡ replicate (f s)
-- --     lawHom {zero}   f s = refl
-- --     lawHom {suc n₁} f s = cong (_∷_ (f s)) (lawHom {n₁} f s)

-- --     lawCom : ∀ {n S T}(fs : Vec (S → T) n) s → fs ⊛ replicate s ≡ replicate (λ f → f s) ⊛ fs
-- --     lawCom []       s = refl
-- --     lawCom (f ∷ fs) s = cong (_∷_ (f s)) (lawCom fs s)

-- _~>_ : (F G : Set → Set) → Set₁
-- F ~> G = ∀ {X} → F X → G X

-- record AppHom {F}{{AF : Applicative F}}{G}{{ AG : Applicative G}}(k : F ~> G) : Set₁ where
--   constructor rec
--   field
--     respPure : ∀ {X} (x : X) → k (pure x) ≡ pure x
--     resp-⊛   : ∀ {S T}(f : F (S → T))(s : F S) → k (f ⊛ s) ≡ k f ⊛ k s

-- monoidApplicativeHom :
--   ∀ {X}{{MX : Monoid X}}{Y}{{MY : Monoid Y}}(f : X → Y){{hf : MonoidHom f}}
--   → AppHom {{monoidApplicative {{MX}}}}{{monoidApplicative {{MY}}}} f
-- monoidApplicativeHom f {{hf}} = record {
--   respPure = λ x → MonoidHom.resp-ε hf ;
--   resp-⊛ = MonoidHom.resp-∙ hf }

-- -- homSum :
-- --   ∀ {F G}{{AF : Applicative F}}{{AG : Applicative G}}(f : F ~> G)
-- --   → Applicative λ X → F X + G X
-- -- homSum {F}{G} k = rec
-- --   (λ x   → true , pure x)
-- --   (λ {(true  , ff)(true  , fx) → true  , (ff ⊛ fx);
-- --       (true  , ff)(false , gx) → false , (k ff ⊛ gx);
-- --       (false , gf)(true  , fx) → false , (gf ⊛ k fx);
-- --       (false , gf)(false , gx) → false , (gf ⊛ gx)})

-- -- homSumOKP :
-- --   ∀ {F G}{{AF : Applicative F}}{{AG : Applicative G}}
-- --   → ApplicativeOKP F → ApplicativeOKP G
-- --   → (k : F ~> G) → AppHom k
-- --   → ApplicativeOKP _ {{homSum k}}
-- -- homSumOKP {F}{G}{{AF}}{{AG}}
-- --  (rec lawId lawCo lawHom lawCom)
-- --  (rec lawId₁ lawCo₁ lawHom₁ lawCom₁) k
-- --  (rec respPure resp-⊛) = rec lawId' lawCo' lawHom' lawCom'
-- --  where
-- --    open module HS = Applicative (homSum k)
-- --    open module AG = Applicative AG
-- --    open module AF = Applicative AF

-- --    lawCom' : ∀ {S T}(f : F (S → T) + G (S → T)) s → f HS.⊛ HS.pure s ≡ HS.pure (λ f → f s) HS.⊛ f
-- --    lawCom' (true  , ff) s = cong (_,_ true) (lawCom ff s)
-- --    lawCom' {S}{T}(false , gf) s
-- --        rewrite
-- --        respPure s
-- --      | respPure {(S → T) → T} (λ f → f s)
-- --      | lawCom₁ gf s
-- --      = refl

-- --    lawHom' : ∀ {S T}(f : S → T) s → HS.pure f HS.⊛ HS.pure s ≡ HS.pure (f s)
-- --    lawHom' f s = cong (_,_ true) (lawHom f s)

-- --    lawId' : ∀ {X} (x : F X + G X) → HS.pure id HS.⊛ x ≡ x
-- --    lawId' (true  , fx) = cong (_,_ true) (lawId fx)
-- --    lawId' {X}(false , gx) rewrite respPure {X → X} id | lawId₁ gx = refl

-- --    lawCo' :
-- --      ∀ {R S T}(f : F (S → T) + G (S → T))
-- --      (g : F (R → S) + G (R → S)) (r : F R + G R)
-- --      → HS.pure (λ f g → f ∘ g) HS.⊛ f HS.⊛ g HS.⊛ r ≡ f HS.⊛ (g HS.⊛ r)
     
-- --    lawCo' (true  , f') (true  , g') (true  , r) =
-- --      cong (_,_ true) (lawCo f' g' r)
   
-- --    lawCo'{R}{S}{T} (true  , f') (false , g') (true  , r)
-- --        rewrite
-- --        resp-⊛ {S → T}{(R → S) → (R → T)} (AF.pure (λ f g x → f (g x))) f'
-- --      | sym (lawCo₁ (k f') g' (k r))
-- --      | respPure (((S → T) → (R → S) → (R → T)) ∋ (λ f g → f ∘ g))
-- --      = refl
     
-- --    lawCo' {R}{S}{T}(false , f') (true  , g') (true  , r)
-- --        rewrite
-- --        respPure (((S → T) → (R → S) → (R → T)) ∋ (λ f g → f ∘ g))
-- --      | lawCo₁ f' (k g') (k r)
-- --      | resp-⊛ g' r
-- --      = refl
     
-- --    lawCo'{R}{S}{T}(false , f') (false , g') (true  , r)
-- --        rewrite
-- --        respPure (((S → T) → (R → S) → (R → T)) ∋ (λ f g → f ∘ g))
-- --      | lawCo₁ f' g' (k r)         
-- --      = refl
   
-- --    lawCo' {R}{S}{T}(true  , f') (true  , g') (false , r)
-- --        rewrite
-- --        resp-⊛ {R → S}{R → T} (AF.pure (λ f g x → f (g x)) AF.⊛ f') g'
-- --      | resp-⊛ {S → T}{(R → S) → (R → T)} (AF.pure (λ f g x → f (g x))) f'
-- --      | respPure (((S → T) → (R → S) → (R → T)) ∋ (λ f g → f ∘ g))
-- --      | lawCo₁ (k f') (k g') r
-- --      = refl

-- --    lawCo' {R}{S}{T}(true  , f') (false , g') (false , r)
-- --        rewrite
-- --        resp-⊛ {S → T}{(R → S) → (R → T)} (AF.pure (λ f g x → f (g x))) f'
-- --      | respPure (((S → T) → (R → S) → (R → T)) ∋ (λ f g → f ∘ g))
-- --      | lawCo₁ (k f') g' r
-- --      = refl
     
-- --    lawCo' {R}{S}{T}(false , f') (true  , g') (false , r)
-- --        rewrite
-- --        respPure (((S → T) → (R → S) → (R → T)) ∋ (λ f g → f ∘ g))
-- --      | lawCo₁ f' (k g') r
-- --      = refl

-- --    lawCo' {R}{S}{T}(false , f') (false , g') (false , r)
-- --        rewrite
-- --        respPure (((S → T) → (R → S) → (R → T)) ∋ (λ f g → f ∘ g))
-- --      | lawCo₁ f' g' r
-- --      = refl

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

-- -- TODO : NO CLASS VERSION 
      
