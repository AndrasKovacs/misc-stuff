{-# OPTIONS --without-K #-}

module Sanity where

open import Lib
open import Syntax
open import SyntaxSet
open import Embedding
open import Substitution
open import Conversion
open import Typing
open import PropTrunc

--  Embedding
--------------------------------------------------------------------------------

data OPE⊢ : ∀ {n m} → Con n → Con m → OPE n m → Set where
  ∙    : OPE⊢ ∙ ∙ ∙
  drop : ∀ {n m Γ Δ A σ} → OPE⊢ {n}{m} Γ Δ σ → OPE⊢ (Γ ▷ A) Δ (drop σ)
  keep : ∀ {n m Γ Δ A σ} → OPE⊢ {n}{m} Γ Δ σ → OPE⊢ (Γ ▷ Tyₑ σ A) (Δ ▷ A) (keep σ)

idₑ⊢ : ∀ {n Γ} → OPE⊢ {n} Γ Γ idₑ
idₑ⊢ {Γ = ∙}     = ∙
idₑ⊢ {Γ = Γ ▷ A} =
  coe ((λ x → OPE⊢ (Γ ▷ x) (Γ ▷ A) (keep idₑ)) & Ty-idₑ A)
      (keep idₑ⊢)

wk⊢ : ∀ {n Γ A} → OPE⊢ {suc n}{n}(Γ ▷ A) Γ wk
wk⊢ = drop idₑ⊢

lookupₑ : ∀ {n m Γ Δ σ} → OPE⊢ {n}{m} Γ Δ σ → ∀ x → lookup (∈ₑ σ x) Γ ≡ Tyₑ σ (lookup x Δ)
lookupₑ {Δ = Δ ▷ A} (drop {Γ = Γ} {σ = σ} σw) zero
  rewrite lookupₑ σw zero = Ty-∘ₑ σ wk (Tyₑ wk A) ⁻¹
        ◾ Ty-∘ₑ wk (drop (σ ∘ₑ idₑ)) A ⁻¹
        ◾ (λ x → Tyₑ (drop x) A) & (assₑ wk σ idₑ ⁻¹ ◾ idrₑ _)
        ◾ Ty-∘ₑ wk (drop σ) A
lookupₑ {Δ = Δ ▷ A} (keep {σ = σ} σw) zero =
  Ty-∘ₑ σ wk A ⁻¹ ◾ (λ x → Tyₑ (drop x) A) & (idrₑ σ ◾ idlₑ σ ⁻¹) ◾ Ty-∘ₑ wk (keep σ) A
lookupₑ {Δ = Δ ▷ _} (drop {Γ = Γ} {σ = σ} σw) (suc x)
  rewrite lookupₑ σw (suc x) =
       Ty-∘ₑ σ wk (Tyₑ wk (lookup x Δ)) ⁻¹
     ◾ Ty-∘ₑ wk (drop (σ ∘ₑ idₑ)) (lookup x Δ) ⁻¹
     ◾ (λ y → Tyₑ (drop y) (lookup x Δ)) &
         (assₑ wk σ idₑ ⁻¹ ◾ idrₑ (wk ∘ₑ σ)) ◾ Ty-∘ₑ wk (drop σ) (lookup x Δ)
lookupₑ (keep {Γ = Γ} {Δ} {σ = σ} σw) (suc x)
  rewrite lookupₑ σw x =
      Ty-∘ₑ σ wk (lookup x Δ) ⁻¹
    ◾ (λ y → Tyₑ (drop y) (lookup x Δ)) & (idrₑ σ ◾ idlₑ σ ⁻¹)
    ◾ Ty-∘ₑ wk (keep σ) (lookup x Δ)

mutual
  Γ⊢Aₑ :
    ∀ {n m Γ Δ A σ} → OPE⊢ {n}{m} Γ Δ σ → Δ ⊢ A → Γ ⊢ Tyₑ σ A
  Γ⊢Aₑ σ U       = U
  Γ⊢Aₑ σ (El t)  = El (Γ⊢t⇓Aₑ σ t)
  Γ⊢Aₑ σ (Π A B) =
    Π (Γ⊢Aₑ σ A) (Γ⊢Aₑ (keep σ) B)

  Γ⊢t⇓Aₑ :
    ∀ {n m Γ Δ t A σ} → OPE⊢ {n}{m} Γ Δ σ → Δ ⊢ t ⇓ A → Γ ⊢ Tmₑ σ t ⇓ Tyₑ σ A
  Γ⊢t⇓Aₑ {σ = σ} σw (A' , tw , p) = Tyₑ σ A' , Γ⊢t⇑Aₑ σw tw , ~ₜₑ σ ∣&∣ p

  Γ⊢t⇑Aₑ :
    ∀ {n m Γ Δ t A σ} → OPE⊢ {n}{m} Γ Δ σ → Δ ⊢ t ⇑ A → Γ ⊢ Tmₑ σ t ⇑ Tyₑ σ A
  Γ⊢t⇑Aₑ {Γ = Γ} {Δ} {σ = σ} σw (var x) =
    coe ((Γ ⊢ var (∈ₑ σ x) ⇑_) & lookupₑ σw x)
        (var (∈ₑ σ x))
  Γ⊢t⇑Aₑ σ (lam A t) =
    lam (Γ⊢Aₑ σ A) (Γ⊢t⇑Aₑ (keep σ) t)
  Γ⊢t⇑Aₑ {Γ = Γ} {σ = σ} σw (app {t} {u} {B = B} tw uw) =
    coe
      ((Γ ⊢ app (Tmₑ σ t) (Tmₑ σ u) ⇑_) &
            (Ty-ₑ∘ₛ (keep σ) (idₛ , Tmₑ σ u) B ⁻¹
          ◾ (λ x → Tyₛ (x , Tmₑ σ u) B) & (idrₑₛ σ ◾ idlₛₑ σ ⁻¹)
          ◾ Ty-ₛ∘ₑ (idₛ , u) σ B))
      (app (Γ⊢t⇑Aₑ σw tw) (Γ⊢t⇓Aₑ σw uw))

-- Propositionality
--------------------------------------------------------------------------------

Π-inj : ∀ {n A A' B B'} → Ty.Π {n} A B ≡ Π A' B' → A ≡ A' × B ≡ B'
Π-inj refl = refl , refl

mutual
  Γ⊢prop : ∀ {n}{Γ : Con n} → Prop (Γ ⊢)
  Γ⊢prop ∙         ∙           = refl
  Γ⊢prop (Γw ▷ Aw) (Γw' ▷ Aw') = _▷_ & Γ⊢prop Γw Γw' ⊗ Γ⊢Aprop Aw Aw'

  Γ⊢Aprop : ∀ {n}{Γ : Con n}{A} → Prop (Γ ⊢ A)
  Γ⊢Aprop U         U           = refl
  Γ⊢Aprop (El tw)   (El tw')    = El & Γ⊢t⇓Aprop tw tw'
  Γ⊢Aprop (Π Aw Bw) (Π Aw' Bw') = Π & Γ⊢Aprop Aw Aw' ⊗ Γ⊢Aprop Bw Bw'

  ⇑unique :
    ∀ {n}{Γ : Con n}{t A B} → Γ ⊢ t ⇑ A → Γ ⊢ t ⇑ B → A ≡ B
  ⇑unique (var x)     (var _)       = refl
  ⇑unique (lam Aw tw) (lam Aw' tw') = Π _ & ⇑unique tw tw'
  ⇑unique (app tw uw) (app tw' uw') = Tyₛ _ & proj₂ (Π-inj (⇑unique tw tw'))

  Γ⊢t⇑Aprop : ∀ {n}{Γ : Con n}{t A} → Prop (Γ ⊢ t ⇑ A)
  Γ⊢t⇑Aprop tw tw' = Γ⊢t⇑Aprop' refl tw tw'

  Γ⊢t⇑Aprop' :
    ∀ {n}{Γ : Con n}{t A B}(p : A ≡ B)(x : Γ ⊢ t ⇑ A)(y : Γ ⊢ t ⇑ B)
    → coe ((Γ ⊢ t ⇑_) & p) x ≡ y
  Γ⊢t⇑Aprop' p (var x)     (var _)  rewrite hedberg Ty≡? p refl = refl
  Γ⊢t⇑Aprop' p (lam Aw tw) (lam Aw' tw') with ⇑unique tw tw' | p
  ... | refl | p' rewrite hedberg Ty≡? p' refl =
    lam & Γ⊢Aprop Aw Aw' ⊗ Γ⊢t⇑Aprop' refl tw tw'
  Γ⊢t⇑Aprop' p (app tw uw) (app tw' uw') with ⇑unique tw tw' | p | tw' | uw'
  ... | refl | p* | tw'* | uw'* rewrite hedberg Ty≡? p* refl =
    app & Γ⊢t⇑Aprop' refl tw tw'* ⊗ Γ⊢t⇓Aprop uw uw'*

  Γ⊢t⇓Aprop : ∀ {n}{Γ : Con n}{t A} → Prop (Γ ⊢ t ⇓ A)
  Γ⊢t⇓Aprop (A , tw , p) (A' , tw' , p') with ⇑unique tw tw' | p | p'
  ... | refl | p* | p'* rewrite Γ⊢t⇑Aprop tw tw' | trunc p* p'* = refl

-- Π conversion
--------------------------------------------------------------------------------

mutual
  A~Π : ∀ {n A B C} → Π {n} A B ~ₜ C → ∃₂ λ C₀ C₁ → C ≡ Π C₀ C₁
  A~Π (Π p q) = _ , _ , refl
  A~Π ~ₜrefl = _ , _ , refl
  A~Π (p ~ₜ⁻¹) = Π~A p
  A~Π (p ~ₜ◾ q) with A~Π p
  ... | C₀ , C₁ , refl = A~Π q

  Π~A : ∀ {n A B C} → C ~ₜ Π {n} A B → ∃₂ λ C₀ C₁ → C ≡ Π C₀ C₁
  Π~A (Π p q)   = _ , _ , refl
  Π~A ~ₜrefl    = _ , _ , refl
  Π~A (p ~ₜ⁻¹)  = A~Π p
  Π~A (p ~ₜ◾ q) with Π~A q
  ... | C₀ , C₁ , refl = Π~A p

Π~Π : ∀ {n A B A' B'} → Π {n} A B ~ₜ Π A' B' → (A ~ₜ A') × (B ~ₜ B')
Π~Π (Π p q) = p , q
Π~Π ~ₜrefl = ~ₜrefl , ~ₜrefl
Π~Π (p ~ₜ⁻¹) with Π~Π p
... | q , r = q ~ₜ⁻¹ , r ~ₜ⁻¹
Π~Π (p ~ₜ◾ q) with A~Π p
... | C₀ , C₁ , refl with Π~Π p
... | r , s with Π~Π q
... | t , u = (r ~ₜ◾ t) , (s ~ₜ◾ u)

-- Substitution
--------------------------------------------------------------------------------

data Sub⊢ {n}(Γ : Con n) : ∀ {m} → Con m → Sub n m → Set where
  ∙   : Sub⊢ Γ ∙ ∙
  _,_ : ∀ {m Δ A t σ} → Sub⊢ Γ {m} Δ σ → Γ ⊢ t ⇓ Tyₛ σ A → Sub⊢ Γ (Δ ▷ A) (σ , t)

infixr 6 _ₛ∘⊢ₑ_

_ₛ∘⊢ₑ_ :
  ∀ {n m k Γ Δ Σ σ δ} → Sub⊢ {n} Γ {m} Δ σ → OPE⊢ Σ Γ δ → Sub⊢ {k} Σ {m} Δ (σ ₛ∘ₑ δ)
_ₛ∘⊢ₑ_ ∙ δw = ∙
_ₛ∘⊢ₑ_ {Σ = Σ} {δ = δ} (_,_ {Δ = Δ} {A} {t} {σ} σw tw) δw =
    (σw ₛ∘⊢ₑ δw) ,
    coe ((Σ ⊢ Tmₑ δ t ⇓_) & (Ty-ₛ∘ₑ σ δ A ⁻¹)) (Γ⊢t⇓Aₑ δw tw)

⇑⇓ : ∀ {n}{Γ : Con n}{t A} → Γ ⊢ t ⇑ A → Γ ⊢ t ⇓ A
⇑⇓ tw = _ , tw , embed ~ₜrefl

⇓~ : ∀ {n}{Γ : Con n}{t A A'} → Γ ⊢ t ⇓ A → A ~ₜ A' → Γ ⊢ t ⇓ A'
⇓~ (B , tw , p) A~A' = _ , tw , (A~A' ~ₜ⁻¹ ~ₜ◾_) ∣&∣ p

keepₛ⊢ :
  ∀ {n m Γ Δ σ A} → Sub⊢ {n} Γ {m} Δ σ → Sub⊢ (Γ ▷ Tyₛ σ A) (Δ ▷ A) (keepₛ σ)
keepₛ⊢ {Γ = Γ}{Δ}{σ}{A} σw =
  (σw ₛ∘⊢ₑ wk⊢) ,
  coe (((Γ ▷ Tyₛ σ A) ⊢ var zero ⇓_) & (Ty-ₛ∘ₑ σ wk A ⁻¹)) (⇑⇓ (var zero))

idₛ⊢ : ∀ {n Γ} → Sub⊢ {n} Γ Γ idₛ
idₛ⊢ {Γ = ∙}     = ∙
idₛ⊢ {Γ = Γ ▷ A} =
  coe ((λ x → Sub⊢ (Γ ▷ x) (Γ ▷ A) (keepₛ idₛ)) & Ty-idₛ A) (keepₛ⊢ idₛ⊢)

mutual
  Γ⊢Aₛ :
    ∀ {n m Γ Δ A σ} → Sub⊢ {n} Γ {m} Δ σ → Δ ⊢ A → Γ ⊢ Tyₛ σ A
  Γ⊢Aₛ σw U         = U
  Γ⊢Aₛ σw (El tw)   = El (Γ⊢t⇓Aₛ σw tw)
  Γ⊢Aₛ σw (Π Aw Bw) = Π (Γ⊢Aₛ σw Aw) (Γ⊢Aₛ (keepₛ⊢ σw) Bw)

  lookupₛ :
    ∀ {n m Γ Δ σ} → Sub⊢ {n} Γ {m} Δ σ → ∀ x → Γ ⊢ ∈ₛ σ x ⇓ Tyₛ σ (lookup x Δ)
  lookupₛ {Γ = Γ} (_,_ {A = A} {t} {σ} σw tw) zero =
    coe ((Γ ⊢ t ⇓_) & ((λ x → Tyₛ x A) & (idlₑₛ σ ⁻¹) ◾ Ty-ₑ∘ₛ wk (σ , t) A)) tw
  lookupₛ {Γ = Γ} (_,_ {Δ = Δ} {t = t} {σ} σw tw) (suc x) =
    coe ((Γ ⊢ ∈ₛ σ x ⇓_)& ((λ x → Tyₛ x _) & (idlₑₛ σ ⁻¹) ◾ Ty-ₑ∘ₛ wk (σ , t) _))
        (lookupₛ σw x)

  Γ⊢t⇑Aₛ : ∀ {n m Γ Δ t A σ} → Sub⊢ {n} Γ {m} Δ σ → Δ ⊢ t ⇑ A → Γ ⊢ Tmₛ σ t ⇓ Tyₛ σ A
  Γ⊢t⇑Aₛ σw (var x)     = lookupₛ σw x
  Γ⊢t⇑Aₛ {Γ = Γ} {Δ} {σ = σ} σw (lam {A} {B} {t} Aw tw) with Γ⊢t⇑Aₛ (keepₛ⊢ σw) tw
  ... | B' , tw' , p = _ , lam (Γ⊢Aₛ σw Aw) tw' , Π ~ₜrefl ∣&∣ p

  Γ⊢t⇑Aₛ {Γ = Γ} {σ = σ} σw (app {t} {u} {A} {B} tw uw)
    with Γ⊢t⇑Aₛ σw tw
  ... | ΠAB' , tw' , p =
    ∣∣-rec
      (λ p → case A~Π p of λ {(C₀ , C₁ , eq) →
        let p'   = coe ((_ ~ₜ_) & eq) p
            tw'' = coe ((Γ ⊢ Tmₛ σ t ⇑_) & eq) tw'
            uw'  = Γ⊢t⇓Aₛ σw uw
            A~C₀ , B~C₁ = Π~Π p'
        in _ ,
           _⊢_⇑_.app tw'' (⇓~ uw' A~C₀) ,
           embed
             (coe
               ((_~ₜ Tyₛ (idₛ , Tmₛ σ u) C₁) &
                    (Ty-∘ₛ (keepₛ σ) (idₛ , Tmₛ σ u) B ⁻¹
                   ◾ (λ x → Tyₛ (x , Tmₛ σ u) B) &
                       (assₛₑₛ σ wk (idₛ , Tmₛ σ u)
                     ◾ (σ ∘ₛ_) & idlₑₛ idₛ
                     ◾ idrₛ σ ◾ idlₛ σ ⁻¹)
                   ◾ Ty-∘ₛ (idₛ , u) σ B))
               (~ₜₛ (idₛ , Tmₛ σ u) B~C₁))})
      Γ⊢t⇓Aprop p

  Γ⊢t⇓Aₛ : ∀ {n m Γ Δ t A σ} → Sub⊢ {n} Γ {m} Δ σ → Δ ⊢ t ⇓ A → Γ ⊢ Tmₛ σ t ⇓ Tyₛ σ A
  Γ⊢t⇓Aₛ {Γ = Γ} {t = t} {A} {σ} σw (A' , tw , p) with Γ⊢t⇑Aₛ σw tw
  ... | A'' , tw' , p' = A'' , tw' , (λ p p' → ~ₜₛ σ p ~ₜ◾ p') ∣&∣ p ∣⊗∣ p'

-- Inference inversion
--------------------------------------------------------------------------------

lookup⊢ : ∀ {n Γ} → Γ ⊢ → ∀ x → Γ ⊢ lookup {n} x Γ
lookup⊢ ∙ ()
lookup⊢ (Γw ▷ Aw) zero    = Γ⊢Aₑ wk⊢ Aw
lookup⊢ (Γw ▷ Aw) (suc x) = Γ⊢Aₑ wk⊢ (lookup⊢ Γw x)

mutual
  Γ⊢t⇑? : ∀ {n}{Γ : Con n}{t A} → Γ ⊢ → Γ ⊢ t ⇑ A → Γ ⊢ A
  Γ⊢t⇑? Γw (var x)     = lookup⊢ Γw x
  Γ⊢t⇑? Γw (lam Aw tw) = Π Aw (Γ⊢t⇑? (Γw ▷ Aw) tw)
  Γ⊢t⇑? {Γ = Γ} Γw (app {t} {u} {A} {B} tw uw) with Γ⊢t⇑? Γw tw
  ... | Π Aw Bw = Γ⊢Aₛ (idₛ⊢ , coe ((Γ ⊢ u ⇓_) & (Ty-idₛ A ⁻¹)) uw) Bw
