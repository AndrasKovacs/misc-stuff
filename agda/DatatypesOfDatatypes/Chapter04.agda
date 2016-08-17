
module Chapter04 where

open import Data.Product
open import Level renaming (suc to lsuc; zero to lzero)
open import Function
open import Data.Unit
open import Data.Bool
open import Data.Empty
open import Relation.Binary.PropositionalEquality
open import Data.Sum
open import Level renaming (suc to lsuc; zero to lzero)

record _▹_ (I J : Set) : Set₁ where
  constructor _◃_$_
  field
    Sh : J → Set
    Po : ∀ j → Sh j → Set
    ri : ∀ j (s : Sh j)(p : Po j s) → I
  ⟦_⟧ : (I → Set) → (J → Set)
  ⟦_⟧ X j = Σ (Sh j) λ s → (p : Po j s) → X (ri j s p)
open _▹_ public

_∸>_ : ∀ {k l}{I : Set k} → (I → Set l) → (I → Set l) → Set (l ⊔ k)
X ∸> Y = ∀ {i} → X i → Y i

imap : ∀ {I J}{C : I ▹ J}{X Y} → (X ∸> Y) → ⟦ C ⟧ X ∸> ⟦ C ⟧ Y
imap f (s , k) = s , f ∘ k

data ITree {J : Set}(C : J ▹ J)(j : J) : Set where
  ⟨_⟩ : ⟦ C ⟧ (ITree C) j → ITree C j

Natᶜ : ⊤ ▹ ⊤
Natᶜ = const Bool ◃ const (λ { true → ⊥ ; false → ⊥ }) $ _

zeroᶜ : ITree Natᶜ tt
zeroᶜ = ⟨ true , (λ ()) ⟩

sucᶜ :  ITree Natᶜ tt → ITree Natᶜ tt
sucᶜ n = ⟨ false , const n ⟩

open import Data.Nat hiding (_⊔_)

VecC : Set → ℕ ▹ ℕ
VecC A = VS ◃ VP $ Vr where
  VS : ℕ → Set
  VS zero    = ⊤
  VS (suc _) = A

  VP : ∀ j → VS j → Set
  VP zero    s = ⊥
  VP (suc j) s = ⊤

  Vr : ∀ n s → VP n s → ℕ
  Vr zero    s ()
  Vr (suc n) s p = n

data Tree {J}(C : J ▹ J) j : Set where
  ⟨_⟩ : ⟦ C ⟧ (Tree C) j → Tree C j

Vec = Tree ∘ VecC

nil : ∀ {A} → Vec A zero
nil {A} = ⟨ (tt , λ ()) ⟩

cons : ∀ {A n} → A → Vec A n → Vec A (suc n)
cons x xs = ⟨ (x , (λ _ → xs)) ⟩

-- Ex 4.2
data ★ : Set where
  ι   : ★
  _⇒_ : ★ → ★ → ★

data Cx : Set where
  ε   : Cx
  _▷_ : Cx → ★ → Cx

Var : (Cx × ★) ▹ (Cx × ★)
Var = S ◃ P $ r where
  S : Cx × ★ → Set
  S (ε       , A) = ⊥
  S ((Γ ▷ B) , A) = A ≡ B ⊎ S (Γ , A)

  P : (j : Cx × ★) → S j → Set
  P (ε , A) ()
  P ((Γ ▷ B) , A) (inj₁ _) = ⊥
  P ((Γ ▷ B) , A) (inj₂ _) = ⊤

  r : (j : Cx × ★) (s : S j) → P j s → Cx × ★
  r (ε , A) () p
  r ((Γ ▷ B) , A) (inj₁ _) ()
  r ((Γ ▷ B) , A) (inj₂ _) p = Γ , A

STLC : (Cx × ★) ▹ (Cx × ★)
STLC = S ◃ P $ r where
  S : Cx × ★ → Set
  S (Γ , A) = Tree Var (Γ , A) ⊎ (∃₂ λ B C → A ≡ B ⇒ C) ⊎ ★

  P : (j : Cx × ★) → S j → Set
  P j (inj₁ _)        = ⊥
  P j (inj₂ (inj₁ _)) = ⊤
  P j (inj₂ (inj₂ _)) = Bool

  r : (j : Cx × ★) (s : S j) → P j s → Cx × ★
  r j       (inj₁ x) ()
  r (Γ , A) (inj₂ (inj₁ (B , C , p))) _ = (Γ ▷ B) , C
  r (Γ , A) (inj₂ (inj₂ B)) false       = Γ , B ⇒ A
  r (Γ , A) (inj₂ (inj₂ B)) true        = Γ , B

var' : ∀ {Γ A} → Tree Var (Γ , A) → Tree STLC (Γ , A)
var' v = ⟨ ((inj₁ v) , λ () ) ⟩

lam : ∀ {Γ A B} → Tree STLC (Γ ▷ A , B) → Tree STLC (Γ , A ⇒ B)
lam {Γ}{A}{B} t = ⟨ (inj₂ (inj₁ (A , B , refl)) , (λ _ → t)) ⟩

app : ∀ {Γ A B} → Tree STLC (Γ , A ⇒ B) → Tree STLC (Γ , A) → Tree STLC (Γ , B)
app {Γ}{A}{B} f x = ⟨ (inj₂ (inj₂ A) , (λ {true → x; false → f})) ⟩

-- ex 4.3
_~_ : ∀ {α β} → Set α → Set β → Set _
A ~ B = ∃₂ λ (f : A → B)(g : B → A) → (∀ a → g (f a) ≡ a) × (∀ b → f (g b) ≡ b)

Id : ∀ {I} → I ▹ I
Id = (λ _ → ⊤) ◃ (λ _ _ → ⊤) $ (λ j _ _ → j)

Idp : ∀ {I X}{i : I} → ⟦ Id ⟧ X i ~ X i
Idp {I}{X}{i} = f , g , gf , fg where
  f : ⟦ Id ⟧ X i → X i
  f (s , p) = p tt

  g : X i → ⟦ Id ⟧ X i
  g = λ z → tt , (λ x → z)

  gf : ∀ a → g (f a) ≡ a
  gf (s , p) = refl 

  fg : ∀ b → f (g b) ≡ b
  fg b = refl

_∘ᶜ_ : ∀ {I J K} → J ▹ K → I ▹ J → I ▹ K
(S ◃ P $ R) ∘ᶜ (S' ◃ P' $ R') =
  (λ k → ∃ λ s → ∀ p → S' (R k s p)) ◃
  (λ {k (s , ps') → ∃ λ p → P' (R k s p) (ps' p)}) $
  (λ {k (s , ps') (p , p') → R' (R k s p) (ps' p) p'})

--------------------------------------------------------------------------------

data Desc {α}(I : Set α) : Set (lsuc α) where
  var  : I → Desc I
  σ π  : (A : Set α)(D : A → Desc I) → Desc I
  _×ᵈ_ : Desc I → Desc I → Desc I
  κ    : Set α → Desc I
infixr 4 _×ᵈ_

⟦_⟧ᵈ : ∀ {α}{I : Set α} → Desc I → (I → Set α) → Set α
⟦ var i    ⟧ᵈ X = X i
⟦ σ A D    ⟧ᵈ X = ∃ λ a → ⟦ D a ⟧ᵈ X
⟦ π A D    ⟧ᵈ X = ∀ a → ⟦ D a ⟧ᵈ X
⟦ D₁ ×ᵈ D₂ ⟧ᵈ X = ⟦ D₁ ⟧ᵈ X × ⟦ D₂ ⟧ᵈ X
⟦ κ A      ⟧ᵈ X = A

ConDesc : ∀ {I J} → I ▹ J → J → Desc I
ConDesc (S ◃ P $ R) j = σ (S j) λ s → π (P j s) λ p → var (R j s p)

-- ex 4.4

DSh : ∀ {I : Set} → Desc I → Set
DSh (var i)    = ⊤
DSh (σ A D)    = ∃ λ a → DSh (D a)
DSh (π A D)    = ∀ a → DSh (D a)
DSh (d₁ ×ᵈ d₂) = DSh d₁ × DSh d₂
DSh (κ A)      = A

DPo : ∀ {I : Set}(d : Desc I) → DSh d → Set
DPo (var i)    s         = ⊤
DPo (σ A D)    (a , d)   = DPo (D a) d
DPo (π A D)    s         = ∃ λ (a : A) → DPo (D a) (s a)
DPo (d₁ ×ᵈ d₂) (s₁ , s₂) = DPo d₁ s₁ ⊎ DPo d₂ s₂
DPo (κ x)      s         = ⊥

Dri : ∀ {I : Set}(d : Desc I)(s : DSh d)(p : DPo d s) → I
Dri (var i)    s         p        = i
Dri (σ A D)    (a , d)   p        = Dri (D a) d p
Dri (π A D)    s         (a , p)  = Dri (D a) (s a) p
Dri (d₁ ×ᵈ d₂) (s₁ , s₂) (inj₁ p) = Dri d₁ s₁ p
Dri (d₁ ×ᵈ d₂) (s₁ , s₂) (inj₂ p) = Dri d₂ s₂ p
Dri (κ x) s ()

DescCon : ∀ {I J} → (J → Desc I) → I ▹ J
DescCon {I}{J} d = (DSh ∘ d) ◃ DPo ∘ d $ (Dri ∘ d)

DescCon~ : ∀ {I J} F X j → ⟦ DescCon {I}{J} F ⟧ X j ~ ⟦ F j ⟧ᵈ X
DescCon~ {I}{J} F X j =
  f F (F j) refl , g F (F j) refl , gf F (F j) refl , fg F (F j) refl where

  f : ∀ F d → d ≡ F j → ⟦ DescCon {I}{J} F ⟧ X j → ⟦ d ⟧ᵈ X 
  f F d eq  (s , p) with F j
  f F _ refl (s , p)         | var i    = p tt
  f F _ refl (s , p)         | κ _      = s  
  f F _ refl ((a , s) , p)   | σ A D    =
    a , f (const (D a)) (D a) refl (s , p)
  f F _ refl (s , p)         | π A D    =
    λ a → f (const (D a)) (D a) refl ((s a) , (λ x → p (a , x)))
  f F _ refl ((s₁ , s₂) , p) | d₁ ×ᵈ d₂ =
    f (const d₁) d₁ refl (s₁ , (p ∘ inj₁)) , f (const d₂) d₂ refl (s₂ , (p ∘ inj₂))

  g : ∀ F d → d ≡ F j → ⟦ d ⟧ᵈ X  → ⟦ DescCon {I}{J} F ⟧ X j
  g F d eq x with F j
  g F _ refl x | var i = tt , const x
  g F _ refl (a , da) | σ A D with g (const (D a)) (D a) refl da
  ... | sh , pos = (a , sh) , pos
  g F _ refl x | π A D = (proj₁ ∘ rec) , (λ {(a , p) → proj₂ (rec a) p})
   where rec = λ a → g (const (D a)) (D a) refl (x a)    
  g F _ refl (x₁ , x₂) | d₁ ×ᵈ d₂ with g (const d₁) d₁ refl x₁ | g (const d₂) d₂ refl x₂
  ... | sh₁ , pos₁ | sh₂ , pos₂ = (sh₁ , sh₂) , λ {(inj₁ p) → pos₁ p; (inj₂ p) → pos₂ p}
  g F _ refl x | κ a = x , λ ()

  -- tedious and needs funext
  fg : ∀ F d (eq : d ≡ F j) x → f F d eq (g F d eq x) ≡ x 
  fg = {!!} 

  gf : ∀ F d (eq : d ≡ F j) x → g F d eq (f F d eq x) ≡ x
  gf = {!!}

