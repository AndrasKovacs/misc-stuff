{-# OPTIONS --without-K #-}

open import Lib hiding (id)
import Lib


isContr : ∀ {i} → Set i → Set i
isContr A = Σ A λ a → ∀ a' → a' ≡ a

isProp : ∀ {i} → Set i → Set i
isProp A = (a a' : A) → a ≡ a'

isSet : ∀ {i} → Set i → Set i
isSet A = (a a' : A) → isProp (a ≡ a')

contr→prop : ∀ {i}{A : Set i} → isContr A → isProp A
contr→prop (a* , p) a a' = p a ◾ p a' ⁻¹

lem : ∀ {i}{A : Set i}{a b c : A} (p : b ≡ c) (q : a ≡ b) → coe ((a ≡_) & p) q ≡ (q ◾ p)
lem refl refl = refl

lem2 : ∀ {i}{A : Set i}{a b c : A} (p : a ≡ b) q (r : a ≡ c) → (p ◾ q) ≡ r → q ≡ (p ⁻¹ ◾ r)
lem2 refl _ _ s = s

prop→set : ∀ {i}{A : Set i} → isProp A → isSet A
prop→set {_}{A} f a a' p q =
    (lem2 (f a a) _ _ (lem p (f a a) ⁻¹ ◾ apd (f a) p))
  ◾ (lem2 (f a a) _ _ (lem q (f a a) ⁻¹ ◾ apd (f a) q) ⁻¹)

contrProp : ∀ {i}(A : Set i) → isProp (isContr A)
contrProp A (a , p) (a' , p') = ,≡ (p' a) (ext λ x → prop→set (contr→prop (a , p)) _ _ _ _)



C : Set₁
C = Σ Set λ S → S → Set

module _ (c : C) where
  S = ₁ c
  P = ₂ c

  Con : Set₁
  Con = ∃ λ (W : Set) → ∀ s → (P s → W) → W

  Ty : Con → Set₁
  Ty (W , con) =
    ∃ λ (Wᴰ : W → Set) → ∀ s (f : P s → W) → (∀ p → Wᴰ (f p)) → Wᴰ (con s f)

  Sub : Con → Con → Set
  Sub (W , con) (W' , con') =
    ∃ λ (Wᴹ : W → W') → ∀ s (f : P s → W) → Wᴹ (con s f) ≡ con' s (Wᴹ ∘ f)

  Tm : (Γ : Con) → Ty Γ → Set
  Tm (W , con)(Wᴰ , conᴰ) =
    ∃ λ (Wˢ : ∀ x → Wᴰ x) → ∀ s (f : P s → W) → Wˢ (con s f) ≡ conᴰ s f (Wˢ ∘ f)

  infix 5 _[_]
  _[_] : ∀ {Γ Δ} → Ty Δ → Sub Γ Δ → Ty Γ
  _[_] {W , con}{W' , con'} (Wᴰ , conᴰ) (Wᴹ , conᴹ) =
      (Wᴰ ∘ Wᴹ)
    , (λ s f fᴰ → tr Wᴰ (conᴹ s f ⁻¹) (conᴰ s (λ p → Wᴹ (f p)) fᴰ))

  id : ∀ {Γ} → Sub Γ Γ
  id {W , con} = (λ x → x) , (λ s f → refl)

  [id] : ∀ {Γ}{A : Ty Γ} → A [ id ] ≡ A
  [id] {W , con}{Wᴰ , conᴰ} = refl

  infixl 4 _▶_
  _▶_ : (Γ : Con) → Ty Γ → Con
  (W , con) ▶ (Wᴰ , conᴰ) =
    (Σ W Wᴰ) , (λ s f → (con s (₁ ∘ f)) , conᴰ s (₁ ∘ f) (₂ ∘ f))

  π₁ : ∀ {Γ Δ A} → Sub Γ (Δ ▶ A) → Sub Γ Δ
  π₁ {W , con}{W' , con'}{Wᴰ , conᴰ}(Wᴹ , conᴹ) =
    (₁ ∘ Wᴹ) , (λ s f → ₁ & conᴹ s f)

  π₂ : ∀ {Γ Δ}{A : Ty Δ}(σ : Sub Γ (Δ ▶ A)) → Tm Γ (A [ π₁ {A = A} σ ])
  π₂ {W , con}{W' , con'}{Wᴰ , conᴰ}(Wᴹ , conᴹ) =
    (₂ ∘ Wᴹ) , (λ s f →
      coe→⁻¹ (  Wᴰ & (₁ & conᴹ s f ⁻¹)) _ _ ((λ x → coe x (₂ (Wᴹ (con s f)))) &
                     ((&⁻¹ Wᴰ _ ◾ (Wᴰ &_) & ⁻¹⁻¹ (₁ & conᴹ s f)) ◾ ∘& Wᴰ ₁ (conᴹ s f) )
              ◾ apd ₂ (conᴹ s f)))

  K : (Γ : Con) → ∀ {Δ} → Ty Δ
  K (W , con){W' , con'} = (λ _ → W) , λ s _ → con s

  unk : ∀ {Γ Δ} → Tm Γ (K Δ) → Sub Γ Δ
  unk = Lib.id

  mk : ∀ {Γ Δ} → Sub Γ Δ → Tm Γ (K Δ)
  mk = Lib.id

  Kβ : ∀ {Γ Δ σ} → unk {Γ}{Δ} (mk {Γ}{Δ} σ) ≡ σ
  Kβ = refl

  Eq : ∀ {Γ A} → Tm Γ A → Tm Γ A → Ty Γ
  Eq {W , con}{Wᴰ , conᴰ}(Wˢ , conˢ)(Wˢ' , conˢ') =
      (λ w → Wˢ w ≡ Wˢ' w)
    , (λ s f fᴰ → conˢ s f ◾ conᴰ s f & ext fᴰ ◾ conˢ' s f ⁻¹)

  Reflect : ∀ {Γ A}{t u : Tm Γ A}(e : Tm Γ (Eq {Γ}{A} t u)) → t ≡ u
  Reflect {W , con}{Wᴰ , conᴰ}{Wˢ , conˢ}{Wˢ' , conˢ'}(Wᵉ , conᵉ) =
    ,≡ (ext Wᵉ)
       (ext λ s → ext λ f → {!!})

  Initial : Con → Set₁
  Initial Γ = ∀ Δ → isContr (Sub Γ Δ)

  InitialityProp : ∀ Γ → isProp (Initial Γ)
  InitialityProp Γ init init' = ext λ Δ → contrProp (Sub Γ Δ) (init Δ) (init' Δ)

  Induction : Con → Set₁
  Induction Γ = ∀ A → Tm Γ A

  Induction⇒Initial : ∀ Γ → Induction Γ → Initial Γ
  Induction⇒Initial Γ ind Δ =
    ind (K Δ) ,
    λ σ → Reflect {Γ}{K Δ {Γ}} {σ} {ind (K Δ)} (ind (Eq {Γ}{K Δ{Γ}} σ (ind (K Δ {Γ}))))

  Initial⇒Induction : ∀ Γ → Initial Γ → Induction Γ
  Initial⇒Induction Γ init A =
    coe ( Tm Γ & (
            (A [_]) & (init Γ .₂ _ ◾ init Γ .₂ _ ⁻¹)
          ◾ [id]))
        (π₂ {Γ}{Γ}{A}(init (Γ ▶ A) .₁))

  InductionProp : ∀ Γ → isProp (Induction Γ)
  InductionProp Γ ind ind' = ext λ A → Reflect (ind (Eq {Γ}{A}(ind A) (ind' A)))
