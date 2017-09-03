
open import Lib hiding (_×_; ⊤)
import Lib as L
open import Data.Maybe

infixl 4 _<$>_
_<$>_ : {A B : Set} → (A → B) → (Maybe A → Maybe B)
f <$> just x = just (f x)
f <$> nothing = nothing

<$>-∘ : ∀ {A B C : Set}(f : B → C)(g : A → B) m → (f <$> (g <$> m)) ≡ ((f ∘ g) <$> m)
<$>-∘ f g (just x) = refl
<$>-∘ f g nothing  = refl

<$>-id : ∀ {A : Set} (m : Maybe A) → (id <$> m) ≡ m
<$>-id (just x) = refl
<$>-id nothing = refl

infixl 1 _>>=_
_>>=_ : {A B : Set} → Maybe A → (A → Maybe B) → Maybe B
just x >>= f = f x
nothing >>= f = nothing

>>=-just : ∀ {A : Set} (m : Maybe A) → (m >>= just) ≡ m
>>=-just (just x) = refl
>>=-just nothing = refl

infixl 4 _<*>_
_<*>_ : {A B : Set} → Maybe (A → B) → Maybe A → Maybe B
just f <*> x = f <$> x
nothing <*> x = nothing

mutual
  -- Types
  data * : Set where
    ⊤ : *
    μ : F → *

    -- Functors
  data F : Set where
    I       : F
    K       : * → F
    _+_ _×_ : F → F → F

infixr 5 _+_
infixr 6 _×_

mutual
  ⟦_⟧ : * → Set
  ⟦ ⊤   ⟧ = L.⊤
  ⟦ μ f ⟧ = ⟦μ⟧ f

  ⟦_⟧ᶠ : F → Set → Set
  ⟦ I     ⟧ᶠ A = A
  ⟦ K a   ⟧ᶠ _ = ⟦ a ⟧
  ⟦ f + g ⟧ᶠ A = ⟦ f ⟧ᶠ A ⊎ ⟦ g ⟧ᶠ A
  ⟦ f × g ⟧ᶠ A = ⟦ f ⟧ᶠ A L.× ⟦ g ⟧ᶠ A

  data ⟦μ⟧ (f : F) : Set where
    ⟨_⟩ : ⟦ f ⟧ᶠ (⟦μ⟧ f) → ⟦μ⟧ f

out : ∀ {f} → ⟦μ⟧ f → ⟦ f ⟧ᶠ (⟦μ⟧ f)
out ⟨ t ⟩ = t

data AtLeastOne (A B : Set) : Set where
  left  : A → AtLeastOne A B
  right : B → AtLeastOne A B
  both  : A → B → AtLeastOne A B

mutual
  -- non-empty functor
  *ᵀ : * → Set → Set
  *ᵀ ⊤     A = A
  *ᵀ (μ f) A = μᵀ f A

  data μᵀ (f : F)(A : Set) : Set where
    ⟨_⟩ : Fᵀ f (μ f) A → μᵀ f A

  -- non-empty higher functor
  Fᵀ : F → * → Set → Set
  Fᵀ I       a A = *ᵀ a A
  Fᵀ (K a)   _ A = *ᵀ a A
  Fᵀ (f + g) a A = AtLeastOne (Fᵀ f a A) (Fᵀ g a A)
  Fᵀ (f × g) a A = Fᵀ f a (Fᵀ g a A)

outᵀ : ∀ {f A} → μᵀ f A → Fᵀ f (μ f) A
outᵀ ⟨ t ⟩ = t

⟨⟩-outᵀ : ∀ {f A}(t : μᵀ f A) → ⟨ outᵀ {f}{A} t ⟩ ≡ t
⟨⟩-outᵀ ⟨ _ ⟩ = refl

bothM : ∀ {A B} → Maybe A → Maybe B → Maybe (AtLeastOne A B)
bothM (just a) (just b) = just (both a b)
bothM (just a) nothing = just (left a)
bothM nothing (just b) = just (right b)
bothM nothing nothing = nothing

mutual
  lookup : ∀ a {B} → ⟦ a ⟧ → Maybe (*ᵀ a B) → Maybe B
  lookup ⊤     i     t = t
  lookup (μ f) ⟨ i ⟩ t = lookupF f f i (outᵀ <$> t)

  lookupF : ∀ f g {B} → ⟦ f ⟧ᶠ (⟦μ⟧ g) → Maybe (Fᵀ f (μ g) B) → Maybe B
  lookupF I       h ⟨ i ⟩     t                 = lookupF h h i (outᵀ <$> t)
  lookupF (K a)   h i         t                 = lookup a i t
  lookupF (f + g) h (inl i)   (just (left l))   = lookupF f h i (just l)
  lookupF (f + g) h (inl i)   (just (right r))  = nothing
  lookupF (f + g) h (inl i)   (just (both l e)) = lookupF f h i (just l)
  lookupF (f + g) h (inr i)   (just (left l))   = nothing
  lookupF (f + g) h (inr i)   (just (right r))  = lookupF g h i (just r)
  lookupF (f + g) h (inr i)   (just (both l r)) = lookupF g h i (just r)
  lookupF (f + g) h i         nothing           = nothing
  lookupF (f × g) h (il , ir) t                 = lookupF g h ir (lookupF f h il t)

mutual
  modify : ∀ a {B} → ⟦ a ⟧ → (Maybe B → Maybe B) → Maybe (*ᵀ a B) → Maybe (*ᵀ a B)
  modify ⊤     i     m t = m t
  modify (μ f) ⟨ i ⟩ m t = ⟨_⟩ <$> modifyF f f i m (outᵀ <$> t)

  modifyF : ∀ f g {B} → ⟦ f ⟧ᶠ (⟦μ⟧ g) → (Maybe B → Maybe B) → Maybe (Fᵀ f (μ g) B) → Maybe (Fᵀ f (μ g) B)
  modifyF I       h ⟨ i ⟩     m t                  = ⟨_⟩ <$> modifyF h h i m (outᵀ <$> t)
  modifyF (K a)   h i         m t                  = modify a i m t
  modifyF (f + g) h (inl i)   m (just (left l))    = left <$> modifyF f h i m (just l)
  modifyF (f + g) h (inr i)   m (just (left l))    = bothM (just l) (modifyF g h i m nothing)
  modifyF (f + g) h (inl i)   m (just (right r))   = bothM (modifyF f h i m nothing) (just r)
  modifyF (f + g) h (inr i)   m (just (right r))   = right <$> modifyF g h i m (just r)
  modifyF (f + g) h (inl i)   m (just (both l r))  = bothM (modifyF f h i m (just l)) (just r)
  modifyF (f + g) h (inr i)   m (just (both l r))  = bothM (just l) (modifyF g h i m (just r))
  modifyF (f + g) h (inl i)   m nothing            = left <$> modifyF f h i m nothing
  modifyF (f + g) h (inr i)   m nothing            = right <$> modifyF g h i m nothing
  modifyF (f × g) h (il , ir) m t                  = modifyF f h il (λ t → modifyF g h ir m t) t

--------------------------------------------------------------------------------

delete : ∀ a {B} → ⟦ a ⟧ → Maybe (*ᵀ a B) → Maybe (*ᵀ a B)
delete a i t = modify a i (λ _ → nothing) t

insert : ∀ a {B} → ⟦ a ⟧ → B → Maybe (*ᵀ a B) → Maybe (*ᵀ a B)
insert a i b t = modify a i (λ _ → just b) t


mutual
  modify-id : ∀ a {B} i t → modify a {B} i id t ≡ t
  modify-id ⊤     i t = refl
  modify-id (μ f) ⟨ i ⟩ t
    rewrite modifyF-id f f i (outᵀ <$> t) | <$>-∘ (μᵀ.⟨_⟩{f}) outᵀ t with t
  ... | just _  = just & (⟨⟩-outᵀ _)
  ... | nothing = refl

  modifyF-id : ∀ f g {B} i t → modifyF f g {B} i id t ≡ t
  modifyF-id I h ⟨ i ⟩ t
    rewrite modifyF-id h h i (outᵀ <$> t) | <$>-∘ (μᵀ.⟨_⟩{h}) outᵀ t with t
  ... | just _  = just & (⟨⟩-outᵀ _)
  ... | nothing = refl
  modifyF-id (K a) h i t = modify-id a i t
  modifyF-id (f + g) h {B} (inl i) (just (left l)) rewrite modifyF-id f h i (just l) = refl
  modifyF-id (f + g) h {B} (inl i) (just (right r)) rewrite modifyF-id f h {B} i nothing = refl
  modifyF-id (f + g) h {B} (inl i) (just (both l r)) rewrite modifyF-id f h i (just l) = refl
  modifyF-id (f + g) h {B} (inr i) (just (left l)) rewrite modifyF-id g h {B} i nothing = refl
  modifyF-id (f + g) h {B} (inr i) (just (right r))  rewrite modifyF-id g h i (just r) = refl
  modifyF-id (f + g) h {B} (inr i) (just (both l r)) rewrite modifyF-id g h i (just r) = refl
  modifyF-id (f + g) h {B} (inl i) nothing rewrite modifyF-id f h {B} i nothing = refl
  modifyF-id (f + g) h {B} (inr i) nothing rewrite modifyF-id g h {B} i nothing = refl
  modifyF-id (f × g) h {B} (il , ir) t
    rewrite ext (modifyF-id g h {B} ir) = modifyF-id f h il t

mutual
  modify-∘ :
    ∀ a {B} i m m' t → modify a {B} i m' (modify a i m t) ≡ modify a i (m' ∘ m) t
  modify-∘ ⊤     i m m' t = refl
  modify-∘ (μ f) {B} ⟨ i ⟩ m m' t
    rewrite modifyF-∘ f f  i m m' (outᵀ <$> t) ⁻¹
    | <$>-∘ outᵀ (μᵀ.⟨_⟩{f}{B}) (modifyF f f i m (outᵀ <$> t))
    | <$>-id (modifyF f f i m (outᵀ <$> t))
    = refl

  modifyF-∘ :
    ∀ f g {B} i m m' t → modifyF f g {B} i m' (modifyF f g i m t) ≡ modifyF f g i (m' ∘ m) t
  modifyF-∘ I h {B}  ⟨ i ⟩ m m' t
    rewrite modifyF-∘ h h i m m' (outᵀ <$> t) ⁻¹
    | <$>-∘ outᵀ (μᵀ.⟨_⟩{h}{B}) (modifyF h h i m (outᵀ <$> t))
    | <$>-id (modifyF h h i m (outᵀ <$> t))
    = refl
  modifyF-∘ (K a)   h i         m m' t = modify-∘ a i m m' t
  modifyF-∘ (f + g) h (inl i)   m m' (just (left l))
    rewrite modifyF-∘ f h i m m' (just l) ⁻¹ with modifyF f h i m (just l)
  ... | nothing = refl
  ... | just t  = refl
  modifyF-∘ (f + g) h (inr i)  m m' (just (left l))
    rewrite modifyF-∘ g h i m m' nothing ⁻¹ with modifyF g h i m nothing
  ... | nothing = refl
  ... | just t  = refl
  modifyF-∘ (f + g) h (inl i)   m m' (just (right r))
    rewrite modifyF-∘ f h i m m' nothing ⁻¹ with modifyF f h i m nothing
  ... | nothing = refl
  ... | just t  = refl
  modifyF-∘ (f + g) h (inr i)   m m' (just (right r))
    rewrite modifyF-∘ g h i m m' (just r) ⁻¹ with modifyF g h i m (just r)
  ... | nothing = refl
  ... | just t  = refl
  modifyF-∘ (f + g) h (inl i)   m m' (just (both l r))
    rewrite modifyF-∘ f h i m m' (just l) ⁻¹ with modifyF f h i m (just l)
  ... | nothing = refl
  ... | just t  = refl
  modifyF-∘ (f + g) h (inr i)   m m' (just (both l r))
    rewrite modifyF-∘ g h i m m' (just r) ⁻¹ with modifyF g h i m (just r)
  ... | nothing = refl
  ... | just t  = refl
  modifyF-∘ (f + g) h (inl i)   m m' nothing
    rewrite modifyF-∘ f h i m m' nothing ⁻¹ with modifyF f h i m nothing
  ... | nothing = refl
  ... | just t  = refl
  modifyF-∘ (f + g) h (inr i) m m' nothing
    rewrite modifyF-∘ g h i m m' nothing ⁻¹ with modifyF g h i m nothing
  ... | nothing = refl
  ... | just t  = refl
  modifyF-∘ (f × g) h (il , ir) m m' t =
    modifyF-∘ f h il (modifyF g h ir m) (modifyF g h ir m') t
    ◾ (λ x → modifyF f h il x t) & ext λ t → modifyF-∘ g h ir m m' t

-- TODO : lookup-nothing

-- mutual
--   modify-lookup : ∀ a {B} i m t → modify a {B} i m t ≡ modify a i (λ _ → m (lookup a i t)) t
--   modify-lookup ⊤     i     m t = refl
--   modify-lookup (μ f) ⟨ i ⟩ m t rewrite modifyF-lookupF f f i m (outᵀ <$> t) ⁻¹ = refl

--   modifyF-lookupF : ∀ f g {B} i m t → modifyF f g {B} i m t ≡ modifyF f g i (λ _ → m (lookupF f g i t)) t
--   modifyF-lookupF I h ⟨ i ⟩  m t rewrite modifyF-lookupF h h i m (outᵀ <$> t) ⁻¹ = refl
--   modifyF-lookupF (K a) h i m t = modify-lookup a i m t
--   modifyF-lookupF (f + g) h (inl i) m (just (left l)) = {!!}
--   modifyF-lookupF (f + g) h (inl i) m (just (right r)) = {!!}
--   modifyF-lookupF (f + g) h (inl i) m (just (both l r)) = {!!}
--   modifyF-lookupF (f + g) h (inr i) m (just (left l)) = {!!}
--   modifyF-lookupF (f + g) h (inr i) m (just (right r)) = {!!}
--   modifyF-lookupF (f + g) h (inr i) m (just (both l r)) = {!!}
--   modifyF-lookupF (f + g) h (inl i) m nothing rewrite modifyF-lookupF f h i m nothing = {!!}
--   modifyF-lookupF (f + g) h (inr i) m nothing = {!!}
--   modifyF-lookupF (f × g) h i m t = {!!}

-- mutual
--   lookup-modify : ∀ a {B} i m t → lookup a {B} i (modify a i m t) ≡ m (lookup a i t)
--   lookup-modify ⊤     i     m t = refl
--   lookup-modify (μ f) ⟨ i ⟩ m t
--       rewrite
--       lookupF-modifyF f f i m (outᵀ <$> t) ⁻¹
--     | <$>-∘ outᵀ (μᵀ.⟨_⟩ {f}) (modifyF f f i m (outᵀ <$> t))
--     | <$>-id (modifyF f f i m (outᵀ <$> t))
--     = refl

--   lookupF-modifyF : ∀ f g {B} i m t → lookupF f g {B} i (modifyF f g i m t) ≡ m (lookupF f g i t)
--   lookupF-modifyF I       h ⟨ i ⟩     m t
--       rewrite
--       lookupF-modifyF h h i m (outᵀ <$> t) ⁻¹
--     | <$>-∘ outᵀ (μᵀ.⟨_⟩ {h}) (modifyF h h i m (outᵀ <$> t))
--     | <$>-id (modifyF h h i m (outᵀ <$> t))
--     = refl
--   lookupF-modifyF (K a)   h i         m t                  = lookup-modify a i m t
--   lookupF-modifyF (f + g) h (inl i)   m (just (left l))    = {!!}
--   lookupF-modifyF (f + g) h (inr i)   m (just (left l))    = {!!}
--   lookupF-modifyF (f + g) h (inl i)   m (just (right r))   = {!!}
--   lookupF-modifyF (f + g) h (inr i)   m (just (right r))   = {!!}
--   lookupF-modifyF (f + g) h (inl i)   m (just (both l r))  = {!!}
--   lookupF-modifyF (f + g) h (inr i)   m (just (both l r))  = {!!}
--   lookupF-modifyF (f + g) h (inl i)   m nothing            = {!!}
--   lookupF-modifyF (f + g) h (inr i)   m nothing            = {!!}
--   --   rewrite lookupF-modifyF g h i m nothing with modifyF g h i m nothing
--   -- ... | nothing = {!!}
--   -- ... | just _  = {!!}

--   lookupF-modifyF (f × g) h (il , ir) m t
--     rewrite lookupF-modifyF f h il (modifyF g h ir m) t
--     = lookupF-modifyF g h ir m (lookupF f h il t)



