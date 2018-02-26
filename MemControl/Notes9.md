
TODO:
  - clear up what properties we need for well-typed -⁺. Maybe we need everything mutually.
  - clean up closure building. Prove properties about env & strengthening renaming.

dependency structure:

  - quoting, uncurrying, vars (strengthening), closure building defined
    by mutual induction on typed CC terms and substitutions, along with required equations.
  - cconv defined mutually on contexts, types and terms
  - every instance of induction must prove beta-eta preservation

IDEAS:
  - If we only have applictaion as eliminator for closures, perhaps we can place closures
    to the univ level of the source function.
  - Have countable univ hierarchy, then show consistency of CCTT by translating to MLTT
    where ⟦ Cl (a : A) B ⟧ = ((a : ⟦ A ⟧) → ⟦ B ⟧), at same univ level.


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

 i ∈ ℕ
───────
Γ ⊢ U i

Γ ⊢ A : U i
───────────
 Γ ⊢ El A

────────────────────
Γ ⊢ U' i : U (1 + i)

El (U' i) ≡ U i

Γ ⊢ A : U i   Γ, a : El A ⊢ B : U j
───────────────────────────────────
    Γ ⊢ (a : A) → B : U (i ⊔ j)

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
Γ ⊢ A i      Type formation
Γ ⊢ t : A    Typing

───
∙ ⊢

Γ ⊢   Γ ⊢ A
───────────
Γ, a : A ⊢

Types

 i ∈ ℕ
───────
Γ ⊢ U i

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
t ≡ (λ a. t a)     -- possible only if ∙ ⊢ t : (a : A) → B

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

∙ ⊢ E : U   Γ ⊢ env : El E   ∙ ⊢ t : (ea : (e : El E, A)) → B
─────────────────────────────────────────────────────────────
  Γ ⊢ pack E env t : Cl (a : A[e ⊢> env])(B[ea ⊢> (env, a)])

Γ ⊢ t : Cl (a : A) B   Γ ⊢ u : A
────────────────────────────────
      Γ ⊢ t u : B[a ⊢> u]

-- closure β:
(pack E env t) u ≡ t (env, u)

-- closure η:
Γ ⊢ t : Cl (a : A) B   Γ ⊢ u : Cl (a : A) B
          Γ, a : A ⊢ t a ≡ u a
───────────────────────────────────────────
              Γ ⊢ t ≡ u

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
on CC contexts, types, terms, substitutions and equations

Closure building
------------------------------------------------------------

given Γ, a : A ⊢ t : B, we build Γ ⊢ ? : Cl (a : A) B

     Γ, a : A ⊢ t : B
  ─────────────────────
  let Γ' be the smallest environment such that Γ', a : A ⊢ t : B
      ∙ ⊢ quote (Γ', a : A) : U
      Γ ⊢ vars : El (quote Γ')
      ∙, (e : El (quote (Γ', a : A))) ⊢ t [uncurry (Γ', a : A)] : B [uncurry (Γ', a : A)]

  Γ ⊢ (λ {a}. t) : Cl (a : A) B
      (λ {a}. t) := pack (quote Γ') vars (λ e. t [uncurry (Γ', a : A)])

-- Uncurrying
------------------------------------------------------------

-- uncurry substitutions

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

TODO: quote action on El equations

Lemma about (El ((a : A) → B)⁺)
------------------------------------------------------------
  goal: El ((a : A) → B)⁺ ≡ Cl (a : El A⁺) (El B⁺)
        El (Cl' A⁺ (λ {a}. B⁺)) ≡ Cl (a : El A⁺) (El B⁺)
        Cl (a : El A⁺) (El ((λ {a}. B⁺) a)) ≡ Cl (a : El A⁺) (El B⁺)

  goal: El ((λ {a}. B⁺) a) ≡ El B⁺
        El ((pack (quote Γ') vars (λ ea. B⁺ [uncurry (Γ', a: A)])) a) ≡ El B⁺
        El ((λ ea. B⁺ [uncurry (Γ', a: A)]) (vars, a)) ≡ El B⁺
        El (B⁺ [uncurry (Γ', a: A)][ea ↦ (vars, a)]) ≡ El B⁺  -- OK by (uncurry-vars)

Closure conversion,
mutually on contexts, types, terms, substitutions and equations
------------------------------------------------------------

Γ ⊢
────
Γ⁺ ⊢

Γ ⊢ A
───────
Γ⁺ ⊢ A⁺

 Γ ⊢ t : A
────────────
Γ⁺ ⊢ t⁺ : A⁺

∙⁺             = ∙
(Γ, a : A)⁺    = (Γ⁺, a : A⁺)
U⁺             = U
(El A)⁺        = El A⁺
x⁺             = x
U'⁺            = U'
((a : A) → B)⁺ = Cl' A⁺ (λ {a}. B⁺)
(λ a. t)⁺      = λ {a}.t⁺
(t u)⁺         = t⁺ u⁺

Lemma 1: quote A [σ] ≡ quote (A [σ])
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


Lemma 2: El (quote A) ≡ A
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

      El ((λ {a}. quote B) a)
    = El ((pack (quote (Γ', a : A)) vars (λ env. quote B [uncurry (Γ', a : A)])) a) -- by def.
    = El ((λ env. quote B [uncurry (Γ', a : A)]) (vars, a))                         -- by def.
    = El (quote B [uncurry (Γ', a : A)] [env ⊢> (vars, a)])                         -- by def.
    = El (quote (B [uncurry (Γ', a : A)][env ⊢> (vars, a)]))  -- quote A [σ] lemma
    = El (quote B)                                            -- by uncurry-vars (TODO)
    = B

for other cases, use (El ((λ {a}. quote B) a) ≡ B)

-- Substitution on closures
--------------------------------------------------------------------------------

  σ : Sub Δ Γ
  Γ, a : A ⊢ t : B
  Γ ⊢ (λ {a}.t) : Cl (a : A) B
  Δ ⊢ (λ {a}.t)[σ]        : Cl (0a : A[σ]) (B[σ, a ↦ a])
  Δ ⊢ (λ {a}.t[σ, a ↦ a]) : Cl (a : A[σ]) (B[σ, a ↦ a])

goal:
  (λ {a}.t)[σ] ≡ (λ {a}. t[σ, a ↦ a])

    (pack (quote (Γ', a : A)) (vars Γ Γ') (λ ea. t [uncurry (Γ', a : A)])) [σ])
  ≡ pack (quote (Δ', a : A[σ])) (vars Δ Δ') (λ ea. t[σ, a ↦ a][uncurry (Δ', a : A[σ])])

    (pack (quote (Γ', a : A)) (vars Γ Γ' [σ]) (λ ea. t [uncurry (Γ', a : A)]))
  ≡ pack (quote (Δ', a : A[σ])) (vars Δ Δ') (λ ea. t[σ, a ↦ a][uncurry (Δ', a : A[σ])])

  goal invoking closure eta:
       t [uncurry (Γ', a : A)][ea ↦ (vars Γ Γ' [σ], a)]
    ≡  t [σ, a ↦ a][uncurry (Δ', a : A[σ])][ea ↦ (vars Δ Δ', a)]
    OK by uncurry-vars

-- Closure conversion on substitutions
--------------------------------------------------------------------------------

Sub⁺ operation given mutually by proofs of its action

σ : Sub Γ Δ
──────────────
σ⁺ : Sub Γ⁺ Δ⁺

lemma A[]⁺ : (A[σ])⁺ ≡ A⁺ [σ⁺]
lemma t[]⁺ : (t[σ])⁺ ≡ t⁺ [σ⁺]

[]⁺         = []
[σ, x ↦ t]⁺ = [σ⁺, x ↦ t⁺]  -- making use of (A[σ])⁺ ≡ A⁺ [σ⁺], when Γ ⊢ t : A[σ]

lemma A[]⁺ : (A[σ])⁺ ≡ A⁺ [σ⁺]
  case U : OK
  case (El A) :
    goal : (El A [σ])⁺   ≡ (El A)⁺ [σ⁺]
           (El (A [σ]))⁺ ≡ El A⁺ [σ⁺]
           El (A [σ])⁺   ≡ El (A⁺ [σ⁺])
    by ind. hypothesis OK
  case ((a : A) → B):
    goal : (((a : A) → B) [σ])⁺ ≡ ((a : A) → B)⁺ [σ⁺]
           ((a : A [σ]) → B [σ, a ↦ a])⁺ ≡ (Cl' A⁺ (λ {a}. B⁺)) [σ⁺]
           Cl' ((A [σ])⁺) (λ {a}. (B [σ, a ↦ a])⁺) ≡ (Cl' A⁺ (λ {a}. B⁺)) [σ⁺]
           Cl' ((A [σ])⁺) (λ {a}. (B [σ, a ↦ a])⁺) ≡ Cl' (A⁺ [σ⁺]) ((λ {a}. B⁺) [σ⁺])
           by ind. hyp: (A [σ])⁺ ≡ A⁺ [σ⁺]

    remaining goal:
      (λ {a}. (B [σ, a ↦ a])⁺) ≡ ((λ {a}. B⁺) [σ⁺])
      (λ {a}. B⁺ [σ⁺, a ↦ a])  ≡ ((λ {a}. B⁺) [σ⁺])        -- by ind hyp
      (λ {a}. B⁺ [σ⁺, a ↦ a])  ≡ ((λ {a}. B⁺ [σ⁺, a ↦ a])  -- by closure-sub lemma
      OK

lemma t[]⁺ : (t[σ])⁺ ≡ t⁺ [σ⁺]
  case x:
    goal (x[σ])⁺ ≡ x⁺[σ⁺] OK
  case t u:
    goal (t u [σ])⁺ ≡ (t u)⁺ [σ⁺]
         (t [σ])⁺ (u [σ])⁺ ≡ (t⁺ [σ⁺]) (u⁺ [σ]⁺)
         OK by ind. hyp

  case (λ a. t):
    goal ((λ a. t)[σ])⁺          ≡ (λ a. t)⁺ [σ⁺]        -- by def
         (λ a. t[σ, a ↦ a])⁺     ≡ (λ {a}.t⁺) [σ⁺]       -- by def and closure sub.
         (λ {a}. (t[σ, a ↦ a])⁺) ≡ (λ {a}.t⁺[σ⁺, a ↦ a]) -- OK by ind. hyp

quote ((a : A) → B)  = quote A →' (λ {a}. quote B)
quote (Cl (a : A) B) = Cl' (quote A) (λ {a}. quote B)
quote (a : A, B)     = (quote A ,' (λ a. quote B))


-- Translating equalities
--------------------------------------------------------------------------------

Γ ⊢ A ≡ B
─────────
Γ⁺ ⊢ A⁺ ≡ B⁺

 Γ ⊢ t ≡ u : A
─────────────────
Γ⁺ ⊢ t⁺ ≡ u⁺ : A⁺


Universe decoding (El U' ≡ U):
  goal : (El U')⁺ ≡ U⁺ OK

Function beta:

goal :
  ((λ a. t) u)⁺ ≡ (t [a ↦ u])⁺
  (λ a. t)⁺ u⁺  ≡ t⁺ [a ↦ u⁺]
  (λ {a}.t⁺) u⁺ ≡ t⁺ [a ↦ u⁺]
  (pack (quote Γ' vars (λ ea. t⁺ [uncurry (Γ', a : A)])) u⁺ ≡ t⁺ [a ↦ u⁺]
  (λ ea. t⁺ [uncurry (Γ', a : A)]) (vars, u⁺) ≡ t⁺ [a ↦ u⁺]
  t⁺ [uncurry (Γ', a : A)][ea ↦ (vars, u⁺)] ≡ t⁺ [a ↦ u⁺]  -- OK by uncurry-vars

Function eta:

hyp:
  Γ ⊢ t : (a : A) → B
  Γ⁺ ⊢ t⁺ : Cl (a : A⁺) B⁺
goal:
  t⁺ ≡ (λ a. t a)⁺
  t⁺ ≡ (λ {a}.t⁺ a)
  t⁺ ≡ pack (quote Γ') vars (λ ea. (t⁺ a) [uncurry (Γ', a : A)])
  t⁺ ≡ pack (quote Γ') vars (λ ea. (t⁺ [uncurry (Γ', a : A)]) (proj₂ ea))
  t⁺ ≡ pack (quote Γ') vars (λ (e, a). (t⁺ [uncurry Γ']) a)
  using closure eta
  t⁺ a ≡ (t⁺ [uncurry Γ'][e ↦ vars]) a  -- OK by uncurry-vars


```
