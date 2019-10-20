{-# OPTIONS --without-K --postfix-projections #-}

{-
  Deriving Frobenius J from J.
  We (conceptually) only use strict J beta, but no functions, Σ-types or universes.
-}

open import Data.Nat
open import Data.Product renaming (proj₁ to ₁; proj₂ to ₂)
open import Data.Unit
open import Level renaming (zero to lzero; suc to lsuc)
open import Relation.Binary.PropositionalEquality public using (_≡_; refl)


--------------------------------------------------------------------------------

J :
  ∀ {A : Set} {x : A}(B : ∀ y → x ≡ y → Set)
  → {y : A} → (e : x ≡ y) → B x refl → B y e
J {A} {x} B {y} refl pr = pr

tr : {A : Set}(P : A → Set){x y : A} → x ≡ y → P x → P y
-- tr P refl px = px
tr P e px = J (λ y _ → P y) e px

infixr 5 _◾_
_◾_ : {A : Set}{x y z : A} → x ≡ y → y ≡ z → x ≡ z
-- p ◾ refl = p
_◾_ {A} {x} {y} {z} p q = tr (λ z → x ≡ z) q p

tr◾ : {A : Set}(B : A → Set)
       {a₀ a₁ a₂ : A}
       (a₀₁ : a₀ ≡ a₁)
       (a₁₂ : a₁ ≡ a₂)
       (b : B a₀)
     → tr B a₁₂ (tr B a₀₁ b) ≡ tr B (a₀₁ ◾ a₁₂) b
-- tr◾ B a₀₁ refl b = refl
tr◾ B a₀₁ a₁₂ b = J (λ _ a₁₂ → tr B a₁₂ (tr B a₀₁ b) ≡ tr B (a₀₁ ◾ a₁₂) b) a₁₂ refl

refl◾ : {A : Set}{x y : A}(e : x ≡ y) → refl ◾ e ≡ e
refl◾ e = J (λ _ e → refl ◾ e ≡ e) e refl
-- refl◾ refl = refl

tr≡◾ : {A : Set}{x y z : A}(e₁ : y ≡ z)(e₂ : x ≡ y) → tr (x ≡_) e₁ e₂ ≡ e₂ ◾ e₁
tr≡◾ e₁ e₂ = J (λ _ e₁ → tr (_≡_ _) e₁ e₂ ≡ e₂ ◾ e₁) e₁ refl
-- tr≡◾ refl e₂ = refl

tr2 :
  ∀ {A : Set}{B : A → Set}(C : ∀ a → B a → Set)
    {a₀ : A}{a₁ : A}(a₂ : a₀ ≡ a₁)
    {b₀ : B a₀}{b₁ : B a₁}(b₂ : tr B a₂ b₀ ≡ b₁)
  → C a₀ b₀ → C a₁ b₁
-- tr2 C refl refl c₀ = c₀
tr2 {A} {B} C {a₀} {a₁} a₂ {b₀} {b₁} b₂ c₀ =
  tr (C a₁) b₂ (J (λ a₁ a₂ → C a₁ (tr B a₂ b₀)) a₂ c₀)

infix 6 _⁻¹
_⁻¹ : {A : Set}{x y : A} → x ≡ y → y ≡ x
_⁻¹ {A} {x} {y} p = tr (λ y → y ≡ x) p refl
-- refl ⁻¹ = refl

ap : ∀{A B : Set}(f : A → B){x y} → x ≡ y → f x ≡ f y
ap f {x} {y} e = tr (λ y → f x ≡ f y) e refl
-- ap f refl = refl

tr2◾ : {A : Set}{B : A → Set}(C : ∀ a → B a → Set)
       {a₀ a₁ a₂ : A}
       (a₀₁ : a₀ ≡ a₁)
       (a₁₂ : a₁ ≡ a₂)
       {b₀  : B a₀}{b₁ : B a₁}{b₂ : B a₂}
       (b₀₁ : tr B a₀₁ b₀ ≡ b₁)
       (b₁₂ : tr B a₁₂ b₁ ≡ b₂)
       (c   : C a₀ b₀)
       → tr2 C a₁₂ b₁₂ (tr2 C a₀₁ b₀₁ c)
       ≡ tr2 C (a₀₁ ◾ a₁₂) (tr◾ B a₀₁ a₁₂ b₀ ⁻¹ ◾ ap (tr B a₁₂) b₀₁ ◾ b₁₂) c
tr2◾ {A} {B} C {a₀} {a₁} {a₂} a₀₁ a₁₂ {b₀} {b₁} {b₂} b₀₁ b₁₂ c =
  J (λ _ b₁₂ → tr2 C a₁₂ b₁₂ (tr2 C a₀₁ b₀₁ c)
             ≡ tr2 C (a₀₁ ◾ a₁₂) (tr◾ B a₀₁ a₁₂ b₀ ⁻¹ ◾ ap (tr B a₁₂) b₀₁ ◾ b₁₂) c)
     b₁₂
     (J (λ _ b₀₁ → tr2 C a₁₂ refl (tr2 C a₀₁ b₀₁ c)
                 ≡ tr2 C (a₀₁ ◾ a₁₂) (tr◾ B a₀₁ a₁₂ b₀ ⁻¹ ◾ ap (tr B a₁₂) b₀₁) c)
        b₀₁
        (J (λ _ a₁₂ → tr2 C a₁₂ refl (tr2 C a₀₁ refl c)
                    ≡ tr2 C (a₀₁ ◾ a₁₂) (tr◾ B a₀₁ a₁₂ b₀ ⁻¹) c)
           a₁₂
           refl))

inv : {A : Set}{x y : A}(e : x ≡ y) → e ◾ e ⁻¹ ≡ refl
-- inv {A} {x} {y} refl = refl
inv e = J (λ _ e → e ◾ e ⁻¹ ≡ refl) e refl

inv⁻¹ : {A : Set}{x y : A}(e : x ≡ y) → e ⁻¹ ◾ e ≡ refl
-- inv⁻¹ {A} {x} {y} refl = refl
inv⁻¹ e = J (λ _ e → e ⁻¹ ◾ e ≡ refl) e refl

J⁻¹ :
  ∀ {A : Set} {x : A}(B : ∀ y → x ≡ y → Set)
    {y : A}(e : x ≡ y) → B y e → B x refl
-- J⁻¹ {A} {x} B {y} refl pe = pe
J⁻¹ {A} {x} B {y} e be = tr2 B (e ⁻¹) (tr≡◾ (e ⁻¹) e ◾ inv e) be

-- We use this J here, because the composition law for tr2 makes
-- Jinv much easier to prove.
J' :
  ∀ {A : Set} {x : A}(B : ∀ y → x ≡ y → Set)
  → {y : A} → (e : x ≡ y) → B x refl → B y e
J' {A} {x} B {y} e pr = tr2 B e (tr≡◾ e refl ◾ refl◾ e) pr

Jinv :
  ∀ {A}{x : A}(B : ∀ y → x ≡ y → Set){y}(e : x ≡ y)(be : B y e)
  → J' B e (J⁻¹ B e be) ≡ be
Jinv {A} {x} B {y} e be =

    tr2◾ B (e ⁻¹) e (tr≡◾ (e ⁻¹) e ◾ inv e) (tr≡◾ e refl ◾ refl◾ e) be
  ◾ tr (λ x → tr2 B (e ⁻¹ ◾ e) x be ≡ be)

       (J (λ _ e → ap (λ p → tr (x ≡_) p e) (inv⁻¹ e ⁻¹) ⁻¹
                 ≡ tr◾ (λ z → x ≡ z) (e ⁻¹) e e ⁻¹
                 ◾ ap (tr (λ z → x ≡ z) e) (tr≡◾ (e ⁻¹) e ◾ inv e)
                 ◾ tr≡◾ e refl ◾ refl◾ e)
           e refl)

       (J (λ e⁻¹◾e inv⁻¹e⁻¹ → tr2 B (e⁻¹◾e) (ap (λ p → tr (x ≡_) p e) (inv⁻¹e⁻¹) ⁻¹) be
                            ≡ be)
          (inv⁻¹ e ⁻¹)
          refl)

--------------------------------------------------------------------------------

Tel : ℕ → Set₁
Tel zero    = Lift _ ⊤
Tel (suc n) = Σ Set λ A → A → Tel n

-- family over a telescope
TFam : ∀ {n} → Tel n → Set₁
TFam {zero}  Δ       = Set
TFam {suc n} (A , Δ) = ∀ x → TFam (Δ x)

-- function from telescope
TPi : ∀ {n}{Δ : Tel n}(B : TFam Δ) → Set
TPi {zero}  {Δ}     B = B
TPi {suc n} {A , Δ} B = ∀ x → TPi (B x)

-- pointwise equality
TPiEq : ∀ {n}{Δ : Tel n}{B : TFam Δ}(f g : TPi B) → Set
TPiEq {zero}  {Δ}     f g = f ≡ g
TPiEq {suc n} {A , Δ} f g = ∀ x → TPiEq {n} (f x) (g x)

--------------------------------------------------------------------------------

-- eliminator + β rule
JFrobeniusTy : ℕ → Set₁
JFrobeniusTy n =
    (A  : Set)
    (x  : A)
    (B  : ∀ y → x ≡ y → Tel n)
    (C  : ∀ y (e : x ≡ y) → TFam (B y e))
    (c  : TPi (C x refl))
  → Σ (∀ y e → TPi (C y e)) λ f → TPiEq {n} (f x refl) c

JFrobenius : ∀ n → JFrobeniusTy n
JFrobenius zero    A x B C c = (λ y e → J C e c) , refl
JFrobenius (suc n) A x B C c =
  (λ y e b →
    let open M y e b in
    tr (λ x → TPi (C y e x))
       (Jinv (λ y e → B y e .₁) e b)
       (JFrobenius n A x B' C' c' .₁ y e))
  ,
  (λ b →
    let open M x refl b in
    JFrobenius n A x B' C' c' .₂)
  where
    module M (y : A)(e : x ≡ y)(b : B y e .₁) where
      b' : ∀ y' e' → B y' e' .₁
      b' y' e' = J' (λ y e → B y e .₁) e' (J⁻¹ (λ y e → B y e .₁) e b)

      B' : ∀ y' e' → Tel n
      B' y' e' = B y' e' .₂ (b' y' e')

      C' : ∀ y' e' → TFam (B' y' e')
      C' y' e' = C y' e' (b' y' e')

      c' : TPi (C' x refl)
      c' = c (b' x refl)

-- β rule is strict for all concrete n
--------------------------------------------------------------------------------

strict0 : ∀ A x B C c → JFrobenius 0 A x B C c .₂ ≡ refl
strict0 A x B C c = refl

strict1 : ∀ A x B C c → JFrobenius 1 A x B C c .₂ ≡ λ _ → refl
strict1 A x B C c = refl

strict2 : ∀ A x B C c → JFrobenius 2 A x B C c .₂ ≡ λ _ _ → refl
strict2 A x B C c = refl

strict3 : ∀ A x B C c → JFrobenius 3 A x B C c .₂ ≡ λ _ _ _ → refl
strict3 A x B C c = refl
