{-# OPTIONS --without-K #-}

module Sanity where

open import Lib
open import Syntax
open import Embedding
open import Substitution
open import Conversion
open import Typing

-- TODO consider sized types to cut out Γ ⊢ A from _⊢_∈_.lam
--   otherwise termination check issue with Γ⊢t∈Aₛ

?⊢U : ∀ {n}{Γ : Con n} → Γ ⊢ U → Γ ⊢
?⊢U (U Γ) = Γ

?▷A⊢ : ∀ {n}{Γ : Con n}{A} → (Γ ▷ A) ⊢ → Γ ⊢
?▷A⊢ (ΓA ▷ _) = ΓA

Γ▷?⊢ : ∀ {n}{Γ : Con n}{A} → (Γ ▷ A) ⊢ → Γ ⊢ A
Γ▷?⊢ (_ ▷ A) = A

-- sanity: I don't quite know?
data Sub⊢ {n}(Γ : Con n) : ∀ {m} → Con m → Sub n m → Set where
  ∙    : Γ ⊢ → Sub⊢ Γ ∙ ∙
  cons : ∀ {m Δ A t σ} → Γ ⊢ t ∈ Tyₛ σ A → Sub⊢ Γ {m} Δ σ → Sub⊢ Γ (Δ ▷ A) (σ , t)

-- sanity: if (Δ ⊢) and (OPE⊢ Γ Δ σ), then (Γ ⊢)
data OPE⊢ : ∀ {n m} → Con n → Con m → OPE n m → Set where
  ∙    : OPE⊢ ∙ ∙ ∙
  drop : ∀ {n m Γ Δ A σ} → Γ ⊢ A → OPE⊢ {n}{m} Γ Δ σ → OPE⊢ (Γ ▷ A) Δ (drop σ)
  keep : ∀ {n m Γ Δ A σ} → OPE⊢ {n}{m} Γ Δ σ → OPE⊢ (Γ ▷ Tyₑ σ A) (Δ ▷ A) (keep σ)

Γ⊢ΠA? : ∀ {n}{Γ : Con n}{A B} → Γ ⊢ Π A B → Γ ▷ A ⊢ B
Γ⊢ΠA? (Π _ B) = B

Γ⊢Π?B : ∀ {n}{Γ : Con n}{A B} → Γ ⊢ Π A B → Γ ⊢ A
Γ⊢Π?B (Π A _) = A

OPE⊢-idₑ : ∀ {n Γ} → Γ ⊢ → OPE⊢ {n} Γ Γ idₑ
OPE⊢-idₑ ∙       = ∙
OPE⊢-idₑ (_▷_ {Γ = Γ} {A} Γw Aw) =
  coe ((λ x → OPE⊢ (Γ ▷ x) (Γ ▷ A) (keep idₑ)) & Ty-idₑ A)
  (OPE⊢.keep (OPE⊢-idₑ Γw))

mutual
  x,A∈? : ∀ {n}{Γ : Con n}{x A} → x , A ∈ Γ → Γ ⊢
  x,A∈? (zero A)  = ?⊢A A ▷ A
  x,A∈? (suc B x) = ?⊢A B ▷ B

  ?⊢t∈A : ∀ {n}{Γ : Con n}{A t} → Γ ⊢ t ∈ A → Γ ⊢
  ?⊢t∈A (var x)        = x,A∈? x
  ?⊢t∈A (app t u)      = ?⊢t∈A t
  ?⊢t∈A (lam _ t)      = ?▷A⊢ (?⊢t∈A t)
  ?⊢t∈A (conv B A~B t) = ?⊢A B

  ?⊢A : ∀ {n}{Γ : Con n}{A} → Γ ⊢ A → Γ ⊢
  ?⊢A (U Γ)   = Γ
  ?⊢A (El t)  = ?⊢t∈A t
  ?⊢A (Π A B) = ?⊢A A

mutual
  OPE⊢?Δσ : ∀ {n m Γ Δ σ} → OPE⊢ {n}{m} Γ Δ σ → Δ ⊢ → Γ ⊢
  OPE⊢?Δσ ∙          Δ = ∙
  OPE⊢?Δσ (drop A σ) Δ       = OPE⊢?Δσ σ Δ ▷ A
  OPE⊢?Δσ (keep σ  ) (Δ ▷ A) = OPE⊢?Δσ σ Δ ▷ Γ⊢Aₑ σ A

  Γ⊢Aₑ : ∀ {n m Γ Δ A σ} → OPE⊢ {n}{m} Γ Δ σ → Δ ⊢ A → Γ ⊢ Tyₑ σ A
  Γ⊢Aₑ σ (U Δ)   = U (OPE⊢?Δσ σ Δ)
  Γ⊢Aₑ σ (El t)  = El (Γ⊢t∈Aₑ σ t)
  Γ⊢Aₑ σ (Π A B) = Π (Γ⊢Aₑ σ A) (Γ⊢Aₑ (keep σ) B)

  x,A∈Γₑ : ∀ {n m Γ Δ x A σ} → OPE⊢ {n}{m} Γ Δ σ → x , A ∈ Δ → ∈ₑ σ x , Tyₑ σ A ∈ Γ
  x,A∈Γₑ ∙ ()
  x,A∈Γₑ {x = x} {A} (drop {Γ = Γ} {A = B} {σ} Bw σw) xw =
    coe
      ((λ y → suc (∈ₑ σ x) , y ∈ (Γ ▷ B)) &
          (Ty-∘ₑ σ wk A ⁻¹ ◾ (λ x → Tyₑ (drop x) A) & idrₑ σ))
      (suc Bw (x,A∈Γₑ σw xw))
  x,A∈Γₑ (keep {Γ = Γ} {A = A} {σ} σw) (zero Aw) =
    coe
      ((zero ,_∈ (Γ ▷ Tyₑ σ A)) &
          (Ty-∘ₑ σ wk A ⁻¹
        ◾ (λ x → Tyₑ (drop x) A) &
            (idrₑ σ ◾ idlₑ σ ⁻¹)
          ◾ Ty-∘ₑ wk (keep σ) A))
      (_,_∈_.zero (Γ⊢Aₑ σw Aw))
  x,A∈Γₑ (keep {Γ = Γ} {A = A} {σ} σw) (suc {x = x} {B} Bw xw) =
    coe
      ((suc (∈ₑ σ x) ,_∈ (Γ ▷ Tyₑ σ A)) &
          (Ty-∘ₑ σ wk B ⁻¹ ◾ (λ x → Tyₑ (drop x) B) &
              (idrₑ σ ◾ idlₑ σ ⁻¹)
            ◾ Ty-∘ₑ wk (keep σ) B))
      (_,_∈_.suc (Γ⊢Aₑ σw Bw) (x,A∈Γₑ σw xw))

  Γ⊢t∈Aₑ : ∀ {n m Γ Δ t A σ} → OPE⊢ {n}{m} Γ Δ σ → Δ ⊢ t ∈ A → Γ ⊢ Tmₑ σ t ∈ Tyₑ σ A
  Γ⊢t∈Aₑ σ (var x)          = var (x,A∈Γₑ σ x)
  Γ⊢t∈Aₑ {Γ = Γ} {σ = σ} σw (app {t} {u} {A}{B} tw uw) =
    coe
      ((Γ ⊢ app (Tyₑ σ A) (Tyₑ (keep σ) B) (Tmₑ σ t) (Tmₑ σ u) ∈_) &
            (Ty-ₑ∘ₛ (keep σ) (idₛ , Tmₑ σ u) B ⁻¹
          ◾ (λ x → Tyₛ (x , Tmₑ σ u) B) & (idrₑₛ σ ◾ idlₛₑ σ ⁻¹)
          ◾ Ty-ₛ∘ₑ (idₛ , u) σ B))
      (_⊢_∈_.app (Γ⊢t∈Aₑ σw tw) (Γ⊢t∈Aₑ σw uw))
  Γ⊢t∈Aₑ σw (lam Aw tw) = lam (Γ⊢Aₑ σw Aw) (Γ⊢t∈Aₑ (keep σw) tw)
  Γ⊢t∈Aₑ {A = A} {σ} σw (conv {B = B} Bw A~B tw) =
    conv (Γ⊢Aₑ σw Bw) (~ₜₑ σ A~B ) (Γ⊢t∈Aₑ σw tw)

--------------------------------------------------------------------------------

Sub⊢ₑ : ∀ {n m k Γ Δ Σ σ δ} → Sub⊢ {n} Γ {m} Δ σ → OPE⊢ Σ Γ δ → Sub⊢ {k} Σ {m} Δ (σ ₛ∘ₑ δ)
Sub⊢ₑ (∙ Γ) δw = ∙ (OPE⊢?Δσ δw Γ)
Sub⊢ₑ {Σ = Σ} {δ = δ} (cons {Δ = Δ} {A} {t} {σ} tw σw) δw =
  cons (coe ((Σ ⊢ Tmₑ δ t ∈_) & (Ty-ₛ∘ₑ σ δ A ⁻¹)) (Γ⊢t∈Aₑ δw tw)) (Sub⊢ₑ σw δw)

Sub⊢-idₛ : ∀ {n Γ} → Γ ⊢ → Sub⊢ {n} Γ Γ idₛ
Sub⊢-idₛ ∙       = ∙ ∙
Sub⊢-idₛ (_▷_ {Γ = Γ} {A} Γw Aw) =
  cons
    (var (coe ((zero ,_∈ (Γ ▷ A)) &
                  (Tyₑ wk & (Ty-idₛ A ⁻¹)
                ◾ Ty-ₛ∘ₑ idₛ wk A ⁻¹))
              (zero Aw)))
    (Sub⊢ₑ (Sub⊢-idₛ Γw) (drop Aw (OPE⊢-idₑ Γw)))

--------------------------------------------------------------------------------

x,?∈Γ : ∀ {n}{Γ : Con n}{x A} → x , A ∈ Γ → Γ ⊢ A
x,?∈Γ (zero A)  = Γ⊢Aₑ (drop A (OPE⊢-idₑ (?⊢A A))) A
x,?∈Γ (suc B x) = Γ⊢Aₑ (drop B (OPE⊢-idₑ (?⊢A B))) (x,?∈Γ x)

Sub⊢?Δσ : ∀ {n m Γ Δ σ} → Sub⊢ {n} Γ {m} Δ σ → Δ ⊢ → Γ ⊢
Sub⊢?Δσ (∙ Γw)       Δw = Γw
Sub⊢?Δσ (cons tw σw) (Δw ▷ Aw) = Sub⊢?Δσ σw Δw

mutual
  Γ⊢Aₛ : ∀ {n m Γ Δ A σ} → Sub⊢ {n} Γ {m} Δ σ → Δ ⊢ A → Γ ⊢ Tyₛ σ A
  Γ⊢Aₛ σw (U Δw)    = U (Sub⊢?Δσ σw Δw)
  Γ⊢Aₛ σw (El tw)   = El (Γ⊢t∈Aₛ σw tw)
  Γ⊢Aₛ {Γ = Γ} {Δ} {σ = σ} σw (Π {A} {B} Aw Bw) =
    Π (Γ⊢Aₛ σw Aw)
      (Γ⊢Aₛ (cons (var (coe ((zero ,_∈ (Γ ▷ Tyₛ σ A)) &
                         (Ty-ₛ∘ₑ σ wk A ⁻¹)) (_,_∈_.zero (Γ⊢Aₛ σw Aw))))
                  (Sub⊢ₑ σw (drop (Γ⊢Aₛ σw Aw) (OPE⊢-idₑ (Sub⊢?Δσ σw (?⊢A Aw))))))
            Bw)

  x,A∈Γₛ : ∀ {n m Γ Δ x A σ} → Sub⊢ {n} Γ {m} Δ σ → x , A ∈ Δ → Γ ⊢ ∈ₛ σ x ∈ Tyₛ σ A
  x,A∈Γₛ {Γ = Γ} (cons {A = A} {t} {σ} tw σw) (zero Aw) =
    coe ((Γ ⊢ t ∈_) & ((λ x → Tyₛ x A) & (idlₑₛ σ ⁻¹) ◾ Ty-ₑ∘ₛ wk (σ , t) A ))
        tw
  x,A∈Γₛ {Γ = Γ} (cons {t = t} {σ} tw σw) (suc {x = x} {A} Bw xw) =
    coe ((Γ ⊢ ∈ₛ σ x ∈_) & ((λ x → Tyₛ x A) & (idlₑₛ σ ⁻¹) ◾ Ty-ₑ∘ₛ wk (σ , t) A))
        (x,A∈Γₛ σw xw)

  Γ⊢t∈Aₛ : ∀ {n m Γ Δ t A σ} → Sub⊢ {n} Γ {m} Δ σ → Δ ⊢ t ∈ A → Γ ⊢ Tmₛ σ t ∈ Tyₛ σ A
  Γ⊢t∈Aₛ σw (var x) = x,A∈Γₛ σw x
  Γ⊢t∈Aₛ {Γ = Γ} {σ = σ} σw (app {t} {u} {A} {B} tw uw) =
    coe
      ((Γ ⊢ app (Tyₛ σ A) (Tyₛ (keepₛ σ) B) (Tmₛ σ t) (Tmₛ σ u) ∈_) &
          (Ty-∘ₛ (keepₛ σ) (idₛ , Tmₛ σ u) B ⁻¹
        ◾ (λ x → Tyₛ (x , Tmₛ σ u) B) &
             (assₛₑₛ σ wk (idₛ , Tmₛ σ u)
           ◾ (σ ∘ₛ_) & idlₑₛ idₛ
           ◾ idrₛ σ ◾ idlₛ σ ⁻¹)
        ◾ Ty-∘ₛ (idₛ , u) σ B))
      (app (Γ⊢t∈Aₛ σw tw) (Γ⊢t∈Aₛ σw uw))
  Γ⊢t∈Aₛ {Γ = Γ} {Δ} {σ = σ} σw (lam {t} {A} {B} Aw tw) =
    let Aw' = Γ⊢Aₛ σw Aw
        σw' = cons (var (coe
                          ((zero ,_∈ (Γ ▷ Tyₛ σ A)) & (Ty-ₛ∘ₑ σ wk A ⁻¹))
                          (zero Aw')))
                   (Sub⊢ₑ σw (drop Aw' (OPE⊢-idₑ (Sub⊢?Δσ σw (?▷A⊢ (?⊢t∈A tw))))))
    in lam Aw' (Γ⊢t∈Aₛ σw' tw)

  Γ⊢t∈Aₛ σw (conv Bw A~B tw) =
    conv (Γ⊢Aₛ σw Bw) (~ₜₛ _ A~B) (Γ⊢t∈Aₛ σw tw)

Γ⊢t∈? : ∀ {n}{Γ : Con n}{A t} → Γ ⊢ t ∈ A → Γ ⊢ A
Γ⊢t∈? (var x)        = x,?∈Γ x
Γ⊢t∈? {Γ = Γ} (app {t} {u} {A} {B} tw uw) =
  Γ⊢Aₛ (cons (coe ((Γ ⊢ u ∈_) & (Ty-idₛ A ⁻¹)) uw) (Sub⊢-idₛ (?⊢t∈A uw)))
       (Γ⊢ΠA? (Γ⊢t∈? tw))
Γ⊢t∈? (lam Aw t)     = Π (Γ▷?⊢ (?⊢t∈A t)) (Γ⊢t∈? t)
Γ⊢t∈? (conv B A~B t) = B

-- unicity of typing: not true because lam isn't type annotated

-- exercise: Π injectivity
--------------------------------------------------------------------------------

mutual
  leml : ∀ {n A B C} → Π {n} A B ~ₜ C → ∃₂ λ C₀ C₁ → C ≡ Π C₀ C₁
  leml (Π p q) = _ , _ , refl
  leml ~ₜrefl = _ , _ , refl
  leml (p ~ₜ⁻¹) = lemr p
  leml (p ~ₜ◾ q) with leml p
  ... | C₀ , C₁ , refl = leml q

  lemr : ∀ {n A B C} → C ~ₜ Π {n} A B → ∃₂ λ C₀ C₁ → C ≡ Π C₀ C₁
  lemr (Π p q)   = _ , _ , refl
  lemr ~ₜrefl    = _ , _ , refl
  lemr (p ~ₜ⁻¹)  = leml p
  lemr (p ~ₜ◾ q) with lemr q
  ... | C₀ , C₁ , refl = lemr p

Π-inj : ∀ {n A B A' B'} → Π {n} A B ~ₜ Π A' B' → (A ~ₜ A') × (B ~ₜ B')
Π-inj (Π p q) = p , q
Π-inj ~ₜrefl = ~ₜrefl , ~ₜrefl
Π-inj (p ~ₜ⁻¹) with Π-inj p
... | q , r = q ~ₜ⁻¹ , r ~ₜ⁻¹
Π-inj (p ~ₜ◾ q) with leml p
... | C₀ , C₁ , refl with Π-inj p
... | r , s with Π-inj q
... | t , u = (r ~ₜ◾ t) , (s ~ₜ◾ u)
