
module StrictLib where

open import Lib public
open import Level renaming (suc to lsuc; zero to lzero)

UIP : ∀ {α}{A : Set α}{x y : A}(p q : x ≡ y) → p ≡ q
UIP refl refl = refl

coe-refl :
  ∀ {i}{A : Set i}(p : A ≡ A)(x : A)
  → coe p x ≡ x
coe-refl refl x = refl

coe-coe : ∀ {i}{A B : Set i}(p q : A ≡ B)(x : A) → coe p x ≡ coe q x
coe-coe refl refl x = refl

tr-refl :
  ∀ {i j}{A : Set i}(B : A → Set j){a₀ : A}{a₁ : A}(a₂ : a₀ ≡ a₁)
    (p : B a₀ ≡ B a₁)(b₀ : B a₀) → tr B a₂ b₀ ≡ tr (λ x → x) p b₀
tr-refl B refl refl b₀ = refl

-- heterogeneous equality
------------------------------------------------------------

infix 4 _≃_
record _≃_ {α}{A B : Set α}(a : A)(b : B) : Set (lsuc α) where
  constructor con
  field
    ty : A ≡ B
    tm : coe ty a ≡ b
open _≃_ public

infix 5 _~
pattern _~ p = record {ty = refl; tm = p}
pattern refl̃ = refl ~

uncoe : ∀ {α}{A B : Set α}(p : B ≡ A) (b : B) → coe p b ≃ b
uncoe refl a = refl̃

untr :
  ∀ {i j}{A : Set i}(B : A → Set j){a₀ : A}{a₁ : A}(a₂ : a₀ ≡ a₁)(ba₀ : B a₀)
  → tr B a₂ ba₀ ≃ ba₀
untr B refl x = refl ~

infix 6 _⁻¹̃
_⁻¹̃ : ∀ {α}{A B : Set α}{a : A}{b : B} → a ≃ b → b ≃ a
refl̃ ⁻¹̃ = refl̃

infixr 5 _◾̃_
_◾̃_ : ∀ {α}{A B C : Set α}{a : A}{b : B}{c : C} → a ≃ b → b ≃ c → a ≃ c
refl̃ ◾̃ q = q

ap̃̃ :
  ∀ {α β}{A : Set α}{B : A → Set β}
  (f : ∀ a → B a){a₀ a₁ : A}(a₂ : a₀ ≡ a₁) → f a₀ ≃ f a₁
ap̃̃ f refl = refl̃

ap2̃̃ :
  ∀ {α β γ}
  {A : Set α}{B : A → Set β}{C : ∀ a → B a → Set γ}
  (f : ∀ a → (b : B a) → C a b)
  {a₀ a₁ : A}(a₂ : a₀ ≡ a₁){b₀ : B a₀}{b₁ : B a₁}(b₂ : b₀ ≃ b₁) → f a₀ b₀ ≃ f a₁ b₁
ap2̃̃ f refl refl̃ = refl̃

ap3̃̃ :
  ∀ {α β γ δ}
  {A : Set α}{B : A → Set β}{C : ∀ a (b : B a) → Set γ}{D : ∀ a (b : B a)(c : C a b) → Set δ}
  (f : ∀ a b c → D a b c)
  {a₀ a₁ : A}(a₂ : a₀ ≡ a₁)
  {b₀ : B a₀}{b₁ : B a₁}(b₂ : b₀ ≃ b₁)
  {c₀ : C a₀ b₀}{c₁ : C a₁ b₁}(c₂ : c₀ ≃ c₁)
  → f a₀ b₀ c₀ ≃ f a₁ b₁ c₁
ap3̃̃ f refl refl̃ refl̃ = refl̃

ap4̃̃ :
  ∀ {α β γ δ ε}
  {A : Set α}{B : A → Set β}{C : ∀ a (b : B a) → Set γ}
    {D : ∀ a b (c : C a b) → Set δ}{E : ∀ a b c (d : D a b c) → Set ε}
  (f : ∀ a b c d → E a b c d)
  {a₀ a₁ : A}                        (a₂ : a₀ ≡ a₁)
  {b₀ : B a₀}      {b₁ : B a₁}       (b₂ : b₀ ≃ b₁)
  {c₀ : C a₀ b₀}   {c₁ : C a₁ b₁}    (c₂ : c₀ ≃ c₁)
  {d₀ : D a₀ b₀ c₀}{d₁ : D a₁ b₁ c₁} (d₂ : d₀ ≃ d₁)
  → f a₀ b₀ c₀ d₀ ≃ f a₁ b₁ c₁ d₁
ap4̃̃ f refl refl̃ refl̃ refl̃ = refl̃

ap5̃̃ :
  ∀ {α β γ δ ε ζ}
  {A : Set α}{B : A → Set β}{C : ∀ a (b : B a) → Set γ}
    {D : ∀ a b (c : C a b) → Set δ}{E : ∀ a b c (d : D a b c) → Set ε}
      {F : ∀ a b c d (e : E a b c d) → Set ζ}
  (f : ∀ a b c d e → F a b c d e)
  {a₀ a₁ : A}                              (a₂ : a₀ ≡ a₁)
  {b₀ : B a₀}         {b₁ : B a₁}          (b₂ : b₀ ≃ b₁)
  {c₀ : C a₀ b₀}      {c₁ : C a₁ b₁}       (c₂ : c₀ ≃ c₁)
  {d₀ : D a₀ b₀ c₀}   {d₁ : D a₁ b₁ c₁}    (d₂ : d₀ ≃ d₁)
  {e₀ : E a₀ b₀ c₀ d₀}{e₁ : E a₁ b₁ c₁ d₁} (e₂ : e₀ ≃ e₁)
  → f a₀ b₀ c₀ d₀ e₀ ≃ f a₁ b₁ c₁ d₁ e₁
ap5̃̃ f refl refl̃ refl̃ refl̃ refl̃ = refl̃

ap6̃̃ :
  ∀ {α β γ δ ε ζ η}
  {A : Set α}{B : A → Set β}{C : ∀ a (b : B a) → Set γ}
    {D : ∀ a b (c : C a b) → Set δ}{E : ∀ a b c (d : D a b c) → Set ε}
      {F : ∀ a b c d (e : E a b c d) → Set ζ}
        {G : ∀ a b c d e (f : F a b c d e) → Set η}
  (f : ∀ a b c d e f → G a b c d e f)
  {a₀ a₁ : A}                              (a₂ : a₀ ≡ a₁)
  {b₀ : B a₀}         {b₁ : B a₁}          (b₂ : b₀ ≃ b₁)
  {c₀ : C a₀ b₀}      {c₁ : C a₁ b₁}       (c₂ : c₀ ≃ c₁)
  {d₀ : D a₀ b₀ c₀}   {d₁ : D a₁ b₁ c₁}    (d₂ : d₀ ≃ d₁)
  {e₀ : E a₀ b₀ c₀ d₀}{e₁ : E a₁ b₁ c₁ d₁} (e₂ : e₀ ≃ e₁)
  {f₀ : F a₀ b₀ c₀ d₀ e₀}{f₁ : F a₁ b₁ c₁ d₁ e₁} (f₂ : f₀ ≃ f₁)
  → f a₀ b₀ c₀ d₀ e₀ f₀ ≃ f a₁ b₁ c₁ d₁ e₁ f₁
ap6̃̃ f refl refl̃ refl̃ refl̃ refl̃ refl̃ = refl̃

uñ : ∀ {α}{A : Set α}{a b : A} → a ≃ b → a ≡ b
uñ refl̃ = refl

ap2̃ :
  ∀{α β γ}{A : Set α}{B : A → Set β}{C : Set γ}
  (f : ∀ a → B a → C)
  {a₀ a₁ : A}(a₂ : a₀ ≡ a₁)
  {b₀ : B a₀}{b₁ : B a₁}(b₂ : b₀ ≃ b₁)
  → f a₀ b₀ ≡ f a₁ b₁
ap2̃ f refl refl̃ = refl

ap3̃ :
  ∀ {α β γ δ}
  {A : Set α}{B : A → Set β}{C : ∀ a (b : B a) → Set γ}{D : Set δ}
  (f : ∀ a b (c : C a b) → D)
  {a₀ a₁ : A}(a₂ : a₀ ≡ a₁)
  {b₀ : B a₀}{b₁ : B a₁}(b₂ : b₀ ≃ b₁)
  {c₀ : C a₀ b₀}{c₁ : C a₁ b₁}(c₂ : c₀ ≃ c₁)
  → f a₀ b₀ c₀ ≡ f a₁ b₁ c₁
ap3̃ f refl refl̃ refl̃ = refl

Πi-≡ :
  ∀ {α β}{A : Set α}{B₀ B₁ : A → Set β}
  → (B₂ : ∀ a → B₀ a ≡ B₁ a)
  → (∀ {a} → B₀ a) ≡ (∀ {a} → B₁ a)
Πi-≡ B₂ = (λ B → ∀ {a} → B a) & (ext B₂)

ext̃ :
  ∀ {α β}
    {A : Set α}
    {B₀ B₁ : A → Set β}
    {f₀ : ∀ a → B₀ a}{f₁ : ∀ a → B₁ a}
  → (∀ a → f₀ a ≃ f₁ a)
  → f₀ ≃ f₁
ext̃ {A = A} {B₀} {B₁} {f₀} {f₁} f₂ =
  J (λ B₁ (B₂ : B₀ ≡ B₁) →
          {f₀ : ∀ a → B₀ a}{f₁ : ∀ a → B₁ a}
        → (∀ a → f₀ a ≃ f₁ a)
        → f₀ ≃ f₁)
     (λ {f₀}{f₁} f₂ → ext (λ a → uñ (f₂ a)) ~)
     (ext (λ a → f₂ a .ty)) f₂

ext̃' :
  ∀ {α β}
    {A₀ A₁ : Set α}
    {B₀ : A₀ → Set β}{B₁ : A₁ → Set β}
    {f₀ : ∀ a → B₀ a}{f₁ : ∀ a → B₁ a}
  → A₀ ≡ A₁
  → (∀ a₀ a₁ (a₂ : a₀ ≃ a₁) → f₀ a₀ ≃ f₁ a₁)
  → f₀ ≃ f₁
ext̃' {A₀ = A} {.A} {B₀} {B₁} {f₀} {f₁} refl f₂ = ext̃ (λ a → f₂ a a refl̃)

extĩ :
  ∀ {α β}
    {A : Set α}
    {B₀ B₁ : A → Set β}
    {f₀ : ∀ {a} → B₀ a}{f₁ : ∀ {a} → B₁ a}
  → (∀ a → f₀ {a} ≃ f₁ {a})
  → (λ {a} → f₀ {a}) ≃ (λ {a} → f₁ {a})
extĩ {A = A} {B₀} {B₁} {f₀} {f₁} f₂ =
  J (λ B₁ (B₂ : B₀ ≡ B₁) → {f₀ : ∀ {a} → B₀ a}{f₁ : ∀ {a} → B₁ a}
      → (∀ a → f₀ {a} ≃ f₁ {a})
      → (λ {a} → f₀ {a}) ≃ (λ {a} → f₁ {a}))
    (λ {f₀}{f₁} f₂ → exti (λ a → uñ (f₂ a)) ~)
    (ext (λ a → f₂ a .ty)) f₂

extĩ' :
  ∀ {α β}
    {A₀ A₁ : Set α}
    {B₀ : A₀ → Set β}{B₁ : A₁ → Set β}
    {f₀ : ∀ {a} → B₀ a}{f₁ : ∀ {a} → B₁ a}
  → A₀ ≡ A₁
  → (∀ a₀ a₁ (a₂ : a₀ ≃ a₁) → f₀ {a₀} ≃ f₁ {a₁})
  → (λ {a} → f₀ {a}) ≃ (λ {a} → f₁ {a})
extĩ' {A₀ = A}{A₁ = .A} {B₀} {B₁} {f₀} {f₁} refl f₂ =
  extĩ (λ a → f₂ a a refl̃ )
