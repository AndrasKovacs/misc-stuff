
module STLC.Renaming where

open import STLC.lib
open import STLC.Syntax
open import STLC.Nf

infix 3 _⊆_
infixr 9 _∘ᵣ_

data _⊆_ : Con → Con → Set where
  idᵣ  : ∀ {Γ} → Γ ⊆ Γ
  add  : ∀ {A Γ Δ} → Γ ⊆ Δ → Γ ⊆ Δ , A
  keep : ∀ {A Γ Δ} → Γ ⊆ Δ → Γ , A ⊆ Δ , A

_∘ᵣ_ : ∀ {Γ Δ Ξ} → Δ ⊆ Ξ → Γ ⊆ Δ → Γ ⊆ Ξ
idᵣ    ∘ᵣ o'      = o'
add o  ∘ᵣ o'      = add (o ∘ᵣ o')
keep o ∘ᵣ idᵣ     = keep o
keep o ∘ᵣ add o'  = add (o ∘ᵣ o')
keep o ∘ᵣ keep o' = keep (o ∘ᵣ o')

∈↑ : ∀ {Γ Δ A} → Γ ⊆ Δ → A ∈ Γ → A ∈ Δ
∈↑ idᵣ      v       = v
∈↑ (add r)  v       = vsₙ (∈↑ r v)
∈↑ (keep r) vzₙ     = vzₙ
∈↑ (keep r) (vsₙ v) = vsₙ (∈↑ r v)

mutual
  Nf↑ : ∀ {Γ Δ A} → Γ ⊆ Δ → Nf Γ A → Nf Δ A
  Nf↑ r (ne n)   = ne (Ne↑ r n)
  Nf↑ r (lamₙ t) = lamₙ (Nf↑ (keep r) t)
  
  Ne↑ : ∀ {Γ Δ A} → Γ ⊆ Δ → Ne Γ A → Ne Δ A
  Ne↑ r (var v)  = var (∈↑ r v)
  Ne↑ r (n $ₙ t) = Ne↑ r n $ₙ Nf↑ r t

sub : ∀ {Γ Δ} → Γ ⊆ Δ → Tms Δ Γ
sub idᵣ          = id
sub (add r)      = sub r ∘ wk
sub (keep {A} r) = sub r ^ A

Tm↑ : ∀ {Γ Δ A} → Γ ⊆ Δ → Tm Γ A → Tm Δ A
Tm↑ r t = t [ sub r ]

