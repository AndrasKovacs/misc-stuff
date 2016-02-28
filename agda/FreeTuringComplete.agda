open import Function

data General (S : Set) (T : S → Set) (X : Set) : Set where
  !!   : X → General S T X
  _??_ : (s : S) → (T s → General S T X) → General S T X
infixr 5 _??_

fold : ∀ {ℓ S T X}{Y : Set ℓ} → (X → Y) → (∀ s → (T s → Y) → Y) → General S T X → Y
fold r c (!! x)   = r x
fold r c (s ?? k) = c s λ z → fold r c (k z)

_>>=_ : ∀ {S T X Y} → General S T X → (X → General S T Y) → General S T Y
g >>= f = fold f _??_ g
infixl 4 _>>=_

call : ∀ {S T}(s : S) → General S T (T s)
call s = s ?? !!

PiG : (S : Set)(T : S → Set) → Set
PiG S T = ∀ s → General S T (T s)

open import Data.Nat hiding (fold; _⊔_)

fusc : PiG ℕ λ _ → ℕ
fusc zero    = !! zero
fusc (suc n) = n ?? λ fn → fn ?? λ ffn → !! (suc ffn)

fusc' : PiG ℕ λ _ → ℕ
fusc' zero    = !! zero
fusc' (suc n) = call n >>= λ fn → call fn >>= λ ffn → !! (suc ffn)

morph :
  ∀ {ℓ S T}{M : Set → Set ℓ}
  → (return  : ∀ {A} → A → M A)
  → (bind    : ∀ {A B} → M A → (A → M B) → M B)
  → (∀ s → M (T s))
  → ∀ {X} → General S T X → M X
morph return bind h = fold return (bind ∘ h)

expand : ∀ {S T X} → PiG S T → General S T X → General S T X
expand f = morph !! _>>=_ f

-- perhaps more clear this way
expand' : ∀ {S T X} → PiG S T → General S T X → General S T X
expand' f (!! x)   = !! x
expand' f (s ?? k) = f s >>= (λ p → expand' f (k p))

open import Data.Bool

halting : ∀ {S} → (S → Bool) → (S → S) → PiG S λ _ → S
halting stop step start with stop start
... | true  = !! start
... | false = step start ?? !!

open import Data.Maybe

bindM : {A B : Set} → Maybe A → (A → Maybe B) → Maybe B
bindM ma f = maybe′ f nothing ma

already : ∀ {S T X} → General S T X → Maybe X
already = morph just bindM (λ s → nothing)

engine : ∀ {S T}(f : PiG S T) → ℕ → ∀ {X} → General S T X → General S T X
engine f zero    = id
engine f (suc n) = engine f n ∘ expand f

petrol : ∀ {S T} → PiG S T → ℕ → ∀ s → Maybe (T s)
petrol f n = already ∘ engine f n ∘ f

petrol' : ∀ {S T} → PiG S T → ℕ → ∀ s → Maybe (T s)
petrol' f zero    s = already (f s)
petrol' f (suc n) s = morph just bindM (petrol' f n) (f s)

-- IR stuff omitted for my lack of effort and comprehension
