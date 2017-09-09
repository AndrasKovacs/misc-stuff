
module Sanity where

open import Lib
open import Syntax
open import Embedding
open import Substitution
open import Typing

?⊢U : ∀ {n}{Γ : Con n} → Γ ⊢ U → Γ ⊢
?⊢U (U Γ) = Γ

π₁Γ⊢ : ∀ {n}{Γ : Con n}{A} → (Γ ▷ A) ⊢ → Γ ⊢
π₁Γ⊢ (ΓA ▷ _) = ΓA

π₂Γ⊢ : ∀ {n}{Γ : Con n}{A} → (Γ ▷ A) ⊢ → Γ ⊢ A
π₂Γ⊢ (_ ▷ A) = A

data Sub⊢ {n}(Γ : Con n) : ∀ {m} → Con m → Sub n m → Set where
  ∙    : Sub⊢ Γ ∙ ∙
  cons : ∀ {m Δ A t σ} → Γ ⊢ t ∈ Tyₛ σ A → Sub⊢ Γ {m} Δ σ → Sub⊢ Γ (Δ ▷ A) (σ , t)

data OPE⊢ : ∀ {n m} → Con n → Con m → OPE n m → Set where
  ∙    : OPE⊢ ∙ ∙ ∙
  drop : ∀ {n m Γ Δ A σ} → Γ ⊢ A → OPE⊢ {n}{m} Γ Δ σ → OPE⊢ (Γ ▷ A) Δ (drop σ)
  keep : ∀ {n m Γ Δ A σ} → Δ ⊢ A → OPE⊢ {n}{m} Γ Δ σ → OPE⊢ (Γ ▷ Tyₑ σ A) (Δ ▷ A) (keep σ)

Γ⊢ΠA? : ∀ {n}{Γ : Con n}{A B} → Γ ⊢ Π A B → Γ ▷ A ⊢ B
Γ⊢ΠA? (Π _ B) = B

Γ⊢Π?B : ∀ {n}{Γ : Con n}{A B} → Γ ⊢ Π A B → Γ ⊢ A
Γ⊢Π?B (Π A _) = A

OPE⊢-idₑ : ∀ {n Γ} → Γ ⊢ → OPE⊢ {n} Γ Γ idₑ
OPE⊢-idₑ ∙       = ∙
OPE⊢-idₑ (_▷_ {Γ = Γ} {A} Γw Aw) =
  coe ((λ x → OPE⊢ (Γ ▷ x) (Γ ▷ A) (keep idₑ)) & Ty-idₑ A)
  (OPE⊢.keep Aw (OPE⊢-idₑ Γw))

Sub⊢-idₛ : ∀ {n Γ} → Γ ⊢ → Sub⊢ {n} Γ Γ idₛ
Sub⊢-idₛ ∙       = ∙
Sub⊢-idₛ (_▷_ {Γ = Γ} {A} Γw Aw) =
  cons
    (var (coe ((λ x → (zero , x ∈ (Γ ▷ A))) &
                  (Tyₑ wk & (Ty-idₛ A ⁻¹)
                ◾ Ty-ₛ∘ₑ idₛ wk A ⁻¹))
              (zero Aw)))
    {!!}

mutual
  OPE⊢?Δσ : ∀ {n m Γ Δ σ} → OPE⊢ {n}{m} Γ Δ σ → Γ ⊢
  OPE⊢?Δσ ∙          = ∙
  OPE⊢?Δσ (drop A σ) = OPE⊢?Δσ σ ▷ A
  OPE⊢?Δσ (keep A σ) = OPE⊢?Δσ σ ▷ Γ⊢Aₑ σ A

  Γ⊢Aₑ : ∀ {n m Γ Δ A}{σ : OPE n m} → OPE⊢ Γ Δ σ → Δ ⊢ A → Γ ⊢ Tyₑ σ A
  Γ⊢Aₑ σ (U _)   = U (OPE⊢?Δσ σ)
  Γ⊢Aₑ σ (El t)  = {!!}
  Γ⊢Aₑ σ (Π A B) = {!!}

  Γ⊢t∈Aₑ : ∀ {n m Γ Δ t A}{σ : OPE n m} → OPE⊢ Γ Δ σ → Δ ⊢ t ∈ A → Γ ⊢ Tmₑ σ t ∈ Tyₑ σ A
  Γ⊢t∈Aₑ σ (var x)          = {!!}
  Γ⊢t∈Aₑ σ (app t u)        = {!!}
  Γ⊢t∈Aₑ σ (lam A t)        = {!!}
  Γ⊢t∈Aₑ σ (conv A B t A~B) = {!!}

mutual
  Sub⊢?Δσ : ∀ {n m Γ Δ σ} → Sub⊢ {n} Γ {m} Δ σ → Γ ⊢
  Sub⊢?Δσ σ = {!!}

  Γ⊢Aₛ : ∀ {n m Γ Δ A}{σ : Sub n m} → Sub⊢ Γ Δ σ → Δ ⊢ A → Γ ⊢ Tyₛ σ A
  Γ⊢Aₛ σ (U Δ)   = U (Sub⊢?Δσ σ)
  Γ⊢Aₛ σ (El t)  = {!!}
  Γ⊢Aₛ σ (Π A B) = {!!}

mutual
  x,?∈Γ : ∀ {n}{Γ : Con n}{x A} → x , A ∈ Γ → Γ ⊢ A
  x,?∈Γ (zero A)  = Γ⊢Aₑ (drop A (OPE⊢-idₑ (?⊢A A))) A
  x,?∈Γ (suc B x) = Γ⊢Aₑ (drop B (OPE⊢-idₑ (?⊢A B))) (x,?∈Γ x)

  Γ⊢t∈? : ∀ {n}{Γ : Con n}{A t} → Γ ⊢ t ∈ A → Γ ⊢ A
  Γ⊢t∈? (var x)          = x,?∈Γ x
  Γ⊢t∈? {Γ = Γ} (app {u = u} {A} {B} tw uw) =
    Γ⊢Aₛ (cons (coe ((Γ ⊢ u ∈_) & (Ty-idₛ A ⁻¹)) uw)
               (Sub⊢-idₛ {!Γ⊢t∈? tw!})) (Γ⊢ΠA? (Γ⊢t∈? tw))
  Γ⊢t∈? (lam A t)        = Π {!π₂Γ⊢  (?⊢A (Γ⊢t∈? t))!} (Γ⊢t∈? t)
  Γ⊢t∈? (conv A B t A~B) = B

  ?⊢A : ∀ {n}{Γ : Con n}{A} → Γ ⊢ A → Γ ⊢
  ?⊢A (U Γ)   = Γ
  ?⊢A (El t)  = ?⊢U (Γ⊢t∈? t)
  ?⊢A (Π A B) = ?⊢A A
