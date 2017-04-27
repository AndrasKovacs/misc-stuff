
open import Algebra
open import Data.Bool
open import Data.Empty
open import Data.List
open import Data.Nat
open import Data.Product
open import Data.Unit
open import Function
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Relation.Nullary.Decidable

module LM {A : Set} = Monoid (Data.List.monoid A)

-- A universe for types which can be put into STRef.
-- STRefs themselves can be put there, but no "ST s" actions.
--------------------------------------------------------------------------------

data U : Set where
  ℕ'  : U
  ref : U → U
  _⇒_ : U → U → U

⟦_⟧ : U → (U → Set) → Set
⟦ ℕ'    ⟧ S = ℕ
⟦ ref A ⟧ S = S A
⟦ A ⇒ B ⟧ S = ⟦ A ⟧ S → ⟦ B ⟧ S

-- We need decidable equality in order to bypass the postulated free theorem
-- during computation.
_U≟_ : (A B : U) → Dec (A ≡ B)
ℕ'      U≟ ℕ'        = yes refl
ℕ'      U≟ ref B     = no (λ ())
ℕ'      U≟ (A ⇒ B)   = no (λ ())
ref A   U≟ ℕ'        = no (λ ())
ref A   U≟ ref B     with A U≟ B
... | yes refl = yes refl
... | no ¬p = no (λ {refl → ¬p refl})
ref A   U≟ (A' ⇒ B)  = no (λ ())
(A ⇒ B) U≟ ℕ'        = no (λ ())
(A ⇒ B) U≟ ref B'    = no (λ ())
(A ⇒ B) U≟ (A' ⇒ B') with A U≟ A' | B U≟ B'
... | yes refl | (yes refl) = yes refl
... | yes p    | (no ¬p)    = no (λ {refl → ¬p refl})
... | no ¬p    | bar        = no (λ {refl → ¬p refl})

--------------------------------------------------------------------------------

-- concrete types in U
⟦_⟧' : U → Set
⟦ A ⟧' = ⟦ A ⟧ (λ _ → ℕ)

data Heap : List U → Set where
  []  : Heap []
  _∷_ : ∀ {A As} → ⟦ A ⟧' → Heap As → Heap (A ∷ As)

SafeRef : List U → U → ℕ → Set
SafeRef []       A n       = ⊥
SafeRef (B ∷ As) A zero    = True (B U≟ A)
SafeRef (_ ∷ As) A (suc n) = SafeRef As A n

readHp : ∀ {A As n} → Heap As → SafeRef As A n → ⟦ A ⟧'
readHp {As = []}     {n}     hp     ()
readHp {As = A ∷ As} {zero} (a ∷ hp) p = subst (λ A → ⟦ A ⟧ _) (toWitness p) a
readHp {As = A ∷ As} {suc n}(_ ∷ hp) p = readHp hp p

writeHp : ∀ {A As n} → Heap As → SafeRef As A n → ⟦ A ⟧' → Heap As
writeHp {As = []} {n}         hp       () a
writeHp {As = A ∷ As} {zero}  (_  ∷ hp) p a = subst (λ A → ⟦ A ⟧ _) (sym (toWitness p)) a ∷ hp
writeHp {As = A ∷ As} {suc n} (a' ∷ hp) p a = a' ∷ writeHp hp p a

alloc : ∀ {As} → Heap As → ∀ {A} → ⟦ A ⟧' → Heap (As ++ A ∷ [])
alloc []        a = a  ∷ []
alloc (a' ∷ hp) a = a' ∷ alloc hp a

newRef : List U → ℕ
newRef = length

safeNewRef : ∀ As Bs B → SafeRef (As ++ B ∷ Bs) B (newRef As)
safeNewRef []       Bs B = fromWitness refl
safeNewRef (A ∷ As) Bs B = safeNewRef As Bs B

--------------------------------------------------------------------------------

-- abstract ST action
data ST (S : U → Set)(A : Set) : Set where
  ret   : A → ST S A
  new   : ∀ B → ⟦ B ⟧ S → (S B → ST S A) → ST S A
  read  : ∀ B → S B → (⟦ B ⟧ S → ST S A) → ST S A
  write : ∀ B → S B → ⟦ B ⟧ S → ST S A → ST S A

-- concrete ST action
ST' : Set → Set
ST' = ST (λ _ → ℕ)

-- Logical predicate interpretation for ST (we omit ⊤ witnesses for U)
--------------------------------------------------------------------------------

⟦⟧ᴾ : ∀ A {S}(Sᴾ : ∀ {A} → S A → Set) → ⟦ A ⟧ S → Set
⟦⟧ᴾ ℕ'      {S} Sᴾ sa = ⊤
⟦⟧ᴾ (ref A) {S} Sᴾ sa = Sᴾ sa
⟦⟧ᴾ (A ⇒ B) {S} Sᴾ sa = {a : ⟦ A ⟧ S}(aᴾ : ⟦⟧ᴾ A Sᴾ a) → ⟦⟧ᴾ B Sᴾ (sa a)

STᴾ : ∀{S}(Sᴾ : ∀ {A} → S A → Set){A}(Aᴾ : A → Set) → ST S A → Set
STᴾ Sᴾ Aᴾ (ret a)          = Aᴾ a
STᴾ Sᴾ Aᴾ (new B b k)      = ⟦⟧ᴾ B Sᴾ b × (∀ sb → Sᴾ sb → STᴾ Sᴾ Aᴾ (k sb))
STᴾ Sᴾ Aᴾ (read B sb k)    = Sᴾ sb × (∀ b → ⟦⟧ᴾ B Sᴾ b → STᴾ Sᴾ Aᴾ (k b))
STᴾ Sᴾ Aᴾ (write B sb b k) = Sᴾ sb × ⟦⟧ᴾ B Sᴾ b × STᴾ Sᴾ Aᴾ k

--------------------------------------------------------------------------------

Safe⟦⟧' : List U → ∀ A → ⟦ A ⟧' → Set
Safe⟦⟧' As A = ⟦⟧ᴾ A (λ {B} n → SafeRef As B n)

Safe⟦⟧'+ : List U → ∀ A → ⟦ A ⟧' → Set
Safe⟦⟧'+ As A a = ∀ Bs → Safe⟦⟧' (As ++ Bs) A a

SafeHeap : ∀ {As} → List U → Heap As → Set
SafeHeap        Bs []       = ⊤
SafeHeap {A ∷ _}Bs (a ∷ hp) = Safe⟦⟧'+ Bs A a × SafeHeap Bs hp

wkSafe⟦⟧'+ : ∀ As Bs A (a : ⟦ A ⟧') → Safe⟦⟧'+ As A a → Safe⟦⟧'+ (As ++ Bs) A a
wkSafe⟦⟧'+ As Bs A a sa Bs' rewrite LM.assoc As Bs Bs' = sa (Bs ++ Bs')

safeAlloc :
  ∀ {As Bs A}
  → (a : ⟦ A ⟧')(hp : Heap As)
  → Safe⟦⟧'+ Bs A a → SafeHeap Bs hp → SafeHeap (Bs ++ A ∷ []) (alloc hp {A} a)
safeAlloc {[]    }{Bs}{A} a []       sa shp        = wkSafe⟦⟧'+ Bs (A ∷ []) A a sa , tt
safeAlloc {B ∷ As}{Bs}{A} a (b ∷ hp) sa (sb , shp) =
  wkSafe⟦⟧'+ Bs (A ∷ []) B b sb , safeAlloc {As}{Bs}{A} a hp sa shp

safeRead :
  ∀ {As Bs A n}(hp : Heap As)
  → SafeHeap Bs hp → (p : SafeRef As A n) → Safe⟦⟧'+ Bs A (readHp hp p)
safeRead [] shp ()
safeRead {n = zero}  (x ∷ hp) (sx , shp) p rewrite toWitness p = sx
safeRead {n = suc n} (x ∷ hp) (sx , shp) p = safeRead hp shp p

safeWrite :
  ∀ {As Bs B n}(b : ⟦ B ⟧')(sb : Safe⟦⟧'+ Bs B b)(hp : Heap As)
  → SafeHeap Bs hp → (p : SafeRef As B n) → SafeHeap Bs (writeHp hp p b)
safeWrite b sb [] shp ()
safeWrite {n = zero}  b sb (x ∷ hp) (sx , shp) p with sym (toWitness p)
... | refl = sb , shp
safeWrite {n = suc n} b sb (x ∷ hp) (sx , shp) p = sx , safeWrite b sb hp shp p

SafeST' : List U → ∀ {A} → ST' A → Set
SafeST' As (ret _)         = ⊤
SafeST' As (new B b k)     = Safe⟦⟧'+ As B b × SafeST' (As ++ B ∷ []) (k (newRef As))
SafeST' As (read B n k)    = SafeRef As B n × (∀ b → Safe⟦⟧'+ As B b → SafeST' As (k b))
SafeST' As (write B n b k) = SafeRef As B n × Safe⟦⟧'+ As B b × SafeST' As k

runST' : ∀ {A As}(m : ST' A) → SafeST' As m → (hp : Heap As) → SafeHeap As hp → A
runST' (ret a)         p           hp shp = a
runST' (new B b k)     (p , q)     hp shp = runST' (k _) q (alloc hp b) (safeAlloc b hp p shp )
runST' (read _ n k)    (p , q)     hp shp = runST' (k _) (q (readHp hp p) (safeRead hp shp p)) hp shp
runST' (write _ n b k) (p , q , r) hp shp = runST' k r (writeHp hp p b) (safeWrite b q hp shp p)

--------------------------------------------------------------------------------

SafeSTᴾ : List U → ∀ {A} → ST' A → Set
SafeSTᴾ As = STᴾ (λ {A} n → SafeRef As A n) (λ _ → ⊤)

SafeSTᴾ+ : List U → ∀ {A} → ST' A → Set
SafeSTᴾ+ As m = ∀ Bs → SafeSTᴾ (As ++ Bs) m

SafeSTᴾ+[] : ∀ {As A m} → SafeSTᴾ+ As {A} m → SafeSTᴾ As m
SafeSTᴾ+[] {As}{A}{m} safe+ = subst (λ x → SafeSTᴾ x {A} m)(proj₂ LM.identity As) (safe+ [])

SafeSTᴾ+⇒SafeST' : ∀ {As A}(m : ST' A) → SafeSTᴾ+ As m → SafeST' As m
SafeSTᴾ+⇒SafeST' {As}(ret _) safe'+ = tt

SafeSTᴾ+⇒SafeST' {As}(new B b k) safe'+ =
  (proj₁ ∘ safe'+) ,
  SafeSTᴾ+⇒SafeST'
       (k (newRef As))
       (λ Bs → subst (λ x → SafeSTᴾ x (k (newRef As)))
           (sym (LM.assoc As (B ∷ []) Bs))
           (safe'+ (B ∷ Bs) .proj₂ _ (safeNewRef As Bs B)))

SafeSTᴾ+⇒SafeST' {As}(read B n k) safe'+ =
  proj₁ (SafeSTᴾ+[] {As}{m = read B n k} safe'+) ,
  (λ b sb → SafeSTᴾ+⇒SafeST' (k b) (λ Bs → safe'+ Bs .proj₂ b (sb Bs)))

SafeSTᴾ+⇒SafeST' {As}(write B n b k) safe'+ =
  (SafeSTᴾ+[] {As}{m = write B n b k} safe'+ .proj₁) ,
  (proj₁ ∘ proj₂ ∘ safe'+) ,
  SafeSTᴾ+⇒SafeST' k (proj₂ ∘ proj₂ ∘ safe'+)

--------------------------------------------------------------------------------

postulate
  -- free theorem for (∀ S → ST S A)
  free-theorem : ∀ {A}(m : ∀ S → ST S A) → ∀ Aᴾ S (Sᴾ : ∀ {A} → S A → Set) → STᴾ Sᴾ Aᴾ (m S)

manifest : ∀ {A} → (∀ S → ST S A) → ST' A
manifest m = m (λ _ → ℕ)

safeManifest : ∀ {A As}(m : ∀ S → ST S A) → SafeST' As (manifest m)
safeManifest m = SafeSTᴾ+⇒SafeST' (manifest m) (λ Bs → free-theorem m (λ _ → ⊤) _ _)

runST : ∀ {A} → (∀ S → ST S A) → A
runST m = runST' (manifest m) (safeManifest m) [] tt

--------------------------------------------------------------------------------

ex1 : ∀ S → ST S ℕ
ex1 S =
  new ℕ' 0 λ x →
  read _ x λ b →
  write _ x (b + 10) $
  read _ x λ b →
  ret b

computes : runST ex1 ≡ 10
computes = refl

