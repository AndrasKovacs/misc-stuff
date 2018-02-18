

##### Source language

```
Γ ⊢          Context formation
Γ ⊢ A        Type formation
Γ ⊢ t : A    Typing

───
∙ ⊢

Γ ⊢   Γ ⊢ A
───────────
Γ, a : A ⊢

─────
Γ ⊢ U

Γ ⊢ A : U
─────────
Γ ⊢ El A

──────────
Γ ⊢ U' : U

El U' ≡ U

Γ ⊢ A : U   Γ, a : El A ⊢ B : U
───────────────────────────────
    Γ ⊢ (a : A) → B : U

   Γ, a : El A ⊢ t : El B
────────────────────────────
Γ ⊢ λ a. t : El ((a : A) → B)

Γ ⊢ t : (a : A) → B   Γ ⊢ u : El A
──────────────────────────────────
    Γ ⊢ t u : El (B[a ⊢> u])

(λ a. t) u ≡ t[a ⊢> u]
λ a. t a ≡ t

```

##### Target language

```
Γ ⊢          Context formation
Γ ⊢ A        Type formation
Γ ⊢ t : A    Typing

───
∙ ⊢

Γ ⊢   Γ ⊢ A
───────────
Γ, a : A ⊢

Types

─────
Γ ⊢ U

Γ ⊢ A : U
─────────
Γ ⊢ El A

─────
Γ ⊢ ⊤

──────────
Γ ⊢ tt : ⊤

Γ ⊢ A   Γ, a : A ⊢ B
────────────────────
  Γ ⊢ (a : A) → B

   ∙, a : A ⊢ t : B
────────────────────────
Γ ⊢ λ a. t : (a : A) → B

Γ ⊢ t : (a : A) → B   Γ ⊢ u : A
───────────────────────────────
   Γ ⊢ t u : B[a ⊢> u]

(λ a. t) u ≡ t[a ⊢> u]
t ≡ (λ a. t a)

-- Σ types
-- We only use Σ to store closed environment types, so we make type formation closed
-- This makes context quoting simpler, since Σ codes only need to store primitive
-- functions for second field types as opposed to closures.

∙ ⊢ A   ∙, a : A ⊢ B
────────────────────
   Γ ⊢ (a : A, B)

∙ ⊢ A   ∙, a : A ⊢ B   Γ ⊢ t : A   Γ ⊢ u : B[a ⊢> t]
────────────────────────────────────────────────────
         Γ ⊢ (t, u) : (t : A, B)

        Γ ⊢ t : (a : A, B)
──────────────────────────────────────
Γ ⊢ π₁ t : A   Γ ⊢ π₂ t : B[a ⊢> π₁ t]

π₁ (t, u) ≡ t
π₂ (t, u) ≡ u
t ≡ (π₁ t, π₂ t)

-- Closures

 Γ ⊢ A   Γ, a : A ⊢ B
───────────────────────
   Γ ⊢ Cl (a : A) B

  ∙ ⊢ E   Γ ⊢ e* : E   ∙ ⊢ t : (ea : (e : E, A)) → B
───────────────────────────────────────────────────────
Γ ⊢ pack E e* t : Cl (a : A[e ⊢> e*])(B[ea ⊢> (e*, a)])

Γ ⊢ t : Cl (a : A) B   Γ ⊢ u : A
────────────────────────────────
      Γ ⊢ t u : B[a ⊢> u]

(pack E e* t) u ≡ t (e*, u)

-- Codes (strongly Tarski)

──────────
Γ ⊢ U' : U

El U' ≡ U

──────────
Γ ⊢ ⊤' : U

El ⊤' ≡ ⊤

Γ ⊢ A : U   Γ ⊢ B : Cl (El A) U
───────────────────────────────
        Γ ⊢ A →' B : U

El (A →' B) ≡ (a : El A) → El (B a)

∙ ⊢ A : U   ∙ ⊢ B : El A → U
────────────────────────────
     Γ ⊢ (A ,' B) : U

El (A ,' B) ≡ (a : El A, El (B a))

Γ ⊢ A : U   Γ ⊢ B : Cl (El A) U
────────────────────────────────
       Γ ⊢ Cl' A B : U

El (Cl' A B) ≡ Cl (a : El A) (El (B a))

```

##### Closure conversion

```
Closure building, uncurrying and quoting are defined by mutual induction

Closure building
------------------------------------------------------------

given Γ, a : A ⊢ t : B, we build Γ ⊢ ? : Cl (a : A) B

     Γ, a : A ⊢ t : B
  ─────────────────────
  let Γ' be the smallest environment such that Γ', a : A ⊢ t : B
      ∙ ⊢ quote (Γ', a : A) : U
      Γ ⊢ e* : El (quote (Γ', a : A))
      ∙, (e : El (quote (Γ', a : A))) ⊢ t [uncurry (Γ', a : A)] : B [uncurry (Γ', a : A)]

  Γ ⊢ (λ {a}. t) : Cl (a : A) B
      (λ {a}. t) := pack (quote (Γ', a : A)) e* (λ e. t [uncurry (Γ', a : A)])

-- Uncurrying
------------------------------------------------------------

-- uncurry substitution

uncurry Γ : Sub (∙, (e : El (quote Γ))) Γ
uncurry ∙ = []
uncurry (Γ, a : A) =
  let uncurry Γ : Sub (∙, (e : El (quote Γ))) Γ
      ∙, (e : El (quote Γ)) ⊢ A [uncurry Γ]

  goal :
       Sub (∙, (env : El (quote (Γ, a : A)))) (Γ, a : A)
    =  Sub (∙, (env : El (quote Γ ,' (λ e. quote (A [uncurry Γ])))) (Γ, a : A)
    =  Sub (∙, (env : (e: El (quote Γ) ,' El (quote (A [uncurry Γ]))))) (Γ, a : A)
    =  Sub (∙, (env : (e: El (quote Γ) ,' A [uncurry Γ]))) (Γ, a : A)

  := [ (uncurry Γ ∘ [env ⊢> proj₁ env]), a ⊢> proj₂ env ]

-- Quoting
------------------------------------------------------------

      Γ ⊢
───────────────
∙ ⊢ quote Γ : U

               Γ ⊢ A
───────────────────────────────────────
Γ ⊢ quote A : U    Γ ⊢ El (quote A) ≡ A

quote ∙          = ⊤'
quote (Γ, a : A) = (quote Γ ,' (λ e. quote (A [uncurry Γ])))

quote U              = U'
quote ⊤              = ⊤'
quote (El A)         = A
quote ((a : A) → B)  = quote A →' (λ {a}. quote B)
quote (Cl (a : A) B) = Cl' (quote A) (λ {a}. quote B)
quote (a : A, B)     = (quote A ,' (λ a. quote B))


Closure conversion
------------------------------------------------------------

Γ ⊢
────
Γ⁺ ⊢

∙⁺          = ∙
(Γ, a : A)⁺ = (Γ⁺, a : A⁺)

Γ ⊢ A
───────
Γ⁺ ⊢ A⁺

 Γ ⊢ t : A
────────────
Γ⁺ ⊢ t⁺ : A⁺

U⁺             = U
(El A)⁺        = El A⁺
x⁺             = x
((a : A) → B)⁺ = Cl' A⁺ (λ {a}. B⁺)
(λ a. t)⁺      = λ {a}.t⁺
(t u)⁺         = t⁺ u⁺


-- Lemma 1: quote A [σ] ≡ quote (A [σ])
------------------------------------------------------------

case U: OK
case ⊤: OK
case (El A): OK
case ((a : A) → B):
  goal :
     (quote A →' (λ {a}. quote B)) [σ] ≡ quote (((a : A) → B) [σ])
   = (quote A →' (λ {a}. quote B)) [σ] ≡ quote ((a : A [σ]) → B [σ, a ↦ a])
   = (quote A →' (λ {a}. quote B)) [σ] ≡ quote (A [σ]) →' (λ {a}. quote (B [σ, a ↦ a]))
   = quote A [σ] →' (λ {a}. (quote B) [σ, a ↦ a]) ≡ quote (A [σ]) →' (λ {a}. quote (B [σ, a ↦ a]))
   = quote A [σ] →' (λ {a}. (quote B) [σ, a ↦ a]) ≡ quote A [σ] →' (λ {a}. quote B [σ, a ↦ a]) OK

likewise for other cases


-- Lemma 2: El (quote A) ≡ A
------------------------------------------------------------

To show: El (quote (a : A, B)) ≡ (a : A, B)

  hyp: ∙ ⊢ A
       ∙, a : A ⊢ B
       ∙ ⊢ El (quote A) ≡ A
       ∙, a : A ⊢ El (quote B) ≡ B

         El (quote (a : A, B)) ≡ (a : A, B)   -- by def.
       = El (quote A ,' (λ a. quote B))       -- by def.
       = (a : El (quote A) , El (quote B))    -- by def.
       = (a : A, B)                           -- by inductive hypothesis

To show: Γ, a : A ⊢ El ((λ {a}. quote B) a) ≡ B

  hyp:
    Γ, a : A ⊢ B
    Γ, a : A ⊢ El (quote B) ≡ B

      El ((λ {a}. quote B) a) ≡ B
    = El ((pack (quote (Γ', a : A)) vars (λ env. quote B [uncurry (Γ', a : A)])) a) -- by def.
    = El ((λ env. quote B [uncurry (Γ', a : A)]) (vars, a))                         -- by def.
    = El (quote B [uncurry (Γ', a : A)] [env ⊢> (vars, a)])                         -- by def.
    = El (quote (B [uncurry (Γ', a : A)][env ⊢> (vars, a)]))  -- quote A [σ] lemma
    = El (quote B)                                            -- uncurry-vars lemma (TODO)
    = B

for other cases, use (El ((λ {a}. quote B) a) ≡ B)

```
