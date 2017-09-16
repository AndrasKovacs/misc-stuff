{-# OPTIONS --without-K #-}

module StdModel where

open import Lib
open import Syntax
open import Embedding
open import Substitution
open import Conversion
open import Typing
open import Sanity

open import Data.Maybe
open import Category.Monad
open module MaybeMonad {α} = RawMonad {α} Data.Maybe.monad

import Level as L

module M (Uᴹ : Set)(Elᴹ : Uᴹ → Set) where

  mutual
    Conᴹ : ∀ {n} → Con n → Set
    Conᴹ ∙       = ⊤
    Conᴹ (Γ ▷ A) = Σ (Conᴹ Γ) (Tyᴹ A)

    Tyᴹ : ∀ {n Γ} → Ty n → Conᴹ  {n} Γ → Set
    Tyᴹ U             γ = Uᴹ
    Tyᴹ {_}{Γ}(El t)  γ = Elᴹ (Tmᴹ {_}{Γ}{U} t γ)
    Tyᴹ {_}{Γ}(Π A B) γ = (α : Tyᴹ A γ) → Tyᴹ {_}{Γ ▷ A} B (γ , α)

    -- need equality of expected type + type in context (branch on decidable raw type equality)
    ∈ᴹ : ∀ {n Γ A} → Fin n → (γ : Conᴹ {n} Γ) → Tyᴹ {n} A γ
    ∈ᴹ {.(suc _)} {Γ ▷ A'} {A} zero    (γ , t) = {!t!}
    ∈ᴹ {.(suc _)} {Γ ▷ A'} {A} (suc x) (γ , t) = {!∈ᴹ {_}{Γ}{A'} x γ!}

    Tmᴹ : ∀ {n Γ A} → Tm n → (γ : Conᴹ {n} Γ) → Tyᴹ {n} A γ
    Tmᴹ {Γ = Γ} {A} (var x) γ = ∈ᴹ {_}{Γ}{A} x γ
    Tmᴹ {A = U}     (lam t) γ = undef where postulate undef : _
    Tmᴹ {A = El x}  (lam t) γ = undef where postulate undef : _
    Tmᴹ {A = Π A B} (lam t) γ = λ α → {!!}
    Tmᴹ (app t u) γ = {!!} -- we need typed app in raw terms: see Streicher page 177


-- It's crap

-- mutual
--   Conᴹ :  ∀ {n} → Con n → Set
--   Conᴹ ∙       = ⊤
--   Conᴹ (Γ ▷ A) = Σ (Conᴹ Γ) (Tyᴹ A)

--   Tyᴹ : ∀ {n Γ} → Ty n → Conᴹ {n} Γ → Set
--   Tyᴹ U       γ = ⊥
--   Tyᴹ (El _)  γ = ⊥
--   Tyᴹ {n}{Γ}(Π A B) γ = (α : Tyᴹ {_}{Γ} A γ) → Tyᴹ {suc n}{Γ ▷ A} B (γ , α)

--   OPEᴹ : ∀ {n m Γ Δ σ} → OPE⊢ {n}{m} Γ Δ σ → Conᴹ {n} Γ → Conᴹ {m} Δ
--   OPEᴹ ∙ γ = tt
--   OPEᴹ (drop Bw σw) (γ , t) = OPEᴹ σw γ
--   OPEᴹ (keep {A = A} σw) (γ , t) = OPEᴹ σw γ , coe (Tyᴹₑ σw A γ) t

--   {-# TERMINATING #-}
--   Tyᴹₑ : ∀ {n m Γ Δ σ} σw A γ → Tyᴹ (Tyₑ σ A) γ ≡ Tyᴹ A (OPEᴹ {n}{m}{Γ}{Δ}{σ} σw γ)
--   Tyᴹₑ σw U       γ = refl
--   Tyᴹₑ σw (El t)  γ = refl
--   Tyᴹₑ σw (Π A B) γ = Π-≡ (Tyᴹₑ σw A γ) (λ a → Tyᴹₑ (keep σw) B (γ , a))

--   ∈ᴹ : ∀ {n Γ A x} → x , A ∈ Γ → (γ : Conᴹ {n} Γ) → Tyᴹ A γ
--   ∈ᴹ (zero {A = A} Aw) (γ , t) = coe (Tyᴹₑ (drop Aw (OPE⊢-idₑ (?⊢A Aw))) A (γ , t) ⁻¹) (coe {!!} t)
--   ∈ᴹ (suc Bw xw) (γ , t) = coe {!!} (∈ᴹ xw γ)

--   Tmᴹ : ∀ {n Γ A t} → Γ ⊢ t ∈ A → (γ : Conᴹ {n} Γ) → Tyᴹ A γ
--   Tmᴹ (var xw)        γ = ∈ᴹ xw γ
--   Tmᴹ (app tw uw)     γ = coe {!!} (Tmᴹ tw γ (Tmᴹ uw γ))
--   Tmᴹ (lam Aw tw)     γ = λ α → Tmᴹ tw (γ , α)
--   Tmᴹ (conv B A~B tw) γ = coe {!!} (Tmᴹ tw γ)







-- mutual
--   Conᴹ : ∀ {n} → Con n → Set
--   Conᴹ ∙       = ⊤
--   Conᴹ (Γ ▷ A) = Σ (Conᴹ Γ) (Tyᴹ Γ A)

--   Tyᴹ : ∀ {n}(Γ : Con n) → Ty n → Conᴹ Γ → Set
--   Tyᴹ Γ U       γ = ⊥
--   Tyᴹ Γ (El t)  γ = ⊥
--   Tyᴹ Γ (Π A B) γ = (α : Tyᴹ Γ A γ) → Tyᴹ (Γ ▷ A) B (γ , α)

-- mutual
--   Conᴹ : ∀ {n} → Con n → Maybe Set
--   Conᴹ ∙       = just ⊤
--   Conᴹ (Γ ▷ A) with Conᴹ Γ
--   ... | just Γᴹ = {!Tyᴹ {_}{Γ} A!}
--   ... | _       = just ⊥

--   Tyᴹ : ∀ {n}{Γ : Con n} → Ty n → maybe (λ Γᴹ → Γᴹ → Set) (L.Lift ⊥) (Conᴹ Γ)
--   Tyᴹ = {!!}

-- mutual
--   Conᴹ : ∀ {n}{Γ : Con n} → Γ ⊢ → Set
--   Conᴹ ∙         = ⊤
--   Conᴹ (Γw ▷ Aw) = Σ (Conᴹ Γw) (Tyᴹ Aw)

--   Tyᴹ : ∀ {n Γ Γw A} → Γ ⊢ A → Conᴹ {n}{Γ} Γw → Set
--   Tyᴹ (U Γw)              γ = ⊥
--   Tyᴹ (El tw)             γ = ⊥
--   Tyᴹ {Γw = Γw} (Π Aw Bw) γ = (α : Tyᴹ Aw γ) → Tyᴹ {Γw = Γw ▷ Aw} Bw (γ , α)

--   ∈ᴹ : ∀ {n Γ Γw A Aw x} → x , A ∈ Γ → (γ : Conᴹ {n}{Γ} Γw) → Tyᴹ {A = A} Aw γ
--   ∈ᴹ {Γw = Γw ▷ Aw₁} {Aw = Aw} (zero _)    (γ , tᴹ) = {!tᴹ!}
--   ∈ᴹ {Γw = Γw ▷ _ }  {Aw = Aw} (suc Bw xw) (γ , tᴹ) = {!!}

--   Tmᴹ : ∀ {n Γ Γw A Aw t} → Γ ⊢ t ∈ A → (γ : Conᴹ {n}{Γ} Γw) → Tyᴹ {A = A} Aw γ
--   Tmᴹ (var x) γ          = {!!}
--   Tmᴹ (app tw uw) γ      = {!!}
--   Tmᴹ (lam Aw tw) γ      = {!!}
--   Tmᴹ (conv Bw A~B tw) γ = {!!}
