

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

Non-code types

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

Γ ⊢ A   Γ, a : A ⊢ B
────────────────────
   Γ ⊢ (a : A, B)

Γ ⊢ t : A   Γ, a : A ⊢ B   Γ ⊢ u : B[a ⊢> t]
────────────────────────────────────────────
         Γ ⊢ (t, u) : (t : A, B)

        Γ ⊢ t : (a : A, B)
──────────────────────────────────────
Γ ⊢ π₁ t : A   Γ ⊢ π₂ t : B[a ⊢> π₁ t]

π₁ (t, u) ≡ t
π₂ (t, u) ≡ u
t ≡ (π₁ t, π₂ t)

-- translucent functions

Γ ⊢ E  Γ ⊢ e* : E   Γ ⊢ A   Γ, a : A ⊢ B
────────────────────────────────────────
       Γ ⊢ [e* : E](a : A) → B

     Γ ⊢ e* : E   Γ ⊢ t : (ea : (e : E, A)) → B
───────────────────────────────────────────────────────────
Γ ⊢ pack e* t : [e* : E](a : A[e ⊢> e*]) → B[ea ⊢> (e*, a)]

Γ ⊢ t : [e* : E](a : A) → B   Γ ⊢ u : A
───────────────────────────────────────
    Γ ⊢ apply t u : B[a ⊢> u]

Γ ⊢ e* : E   Γ ⊢ t : (ea : (e : E, A)) → B   Γ ⊢ u : A
──────────────────────────────────────────────────────
         Γ ⊢ apply (pack t) u ≡ t (e*, u)


apply (pack e* t) u ≡ t (e*, u)

-- full closures
Clo (a : A) B := (E : U, [E](a : A) → B)

-- Codes (Strongly Tarski)


──────────
Γ ⊢ U' : U

El U' ≡ U

──────────
Γ ⊢ ⊤' : U

El ⊤' ≡ ⊤

Γ ⊢ A : U   Γ ⊢ B : El A → U
────────────────────────────
    Γ ⊢ A →' B : U

El (A →' B) ≡ (a : El A) → El (B a)

Γ ⊢ A : U   Γ ⊢ B : El A → U
─────────────────────────────
   Γ ⊢ (A; B) : U

El (A; B) ≡ (a : El A, El (B a))

Γ ⊢ E : U   Γ ⊢ A : U   Γ ⊢ B : Clo
───────────────────────────────────────────────────────────────────
                   Γ ⊢ [E] A →' B : U

El ([E] A →' B) ≡ [El E](a : El (A e*) → El (B (e*, a))

```

##### Closure conversion (TODO)

```

Γ ⊢
────
Γ⁺ ⊢

∙⁺          = ∙
(Γ, a : A)⁺ = (Γ⁺, a⁺ : A⁺)

Γ ⊢ A
───────
Γ⁺ ⊢ A⁺

U⁺      = U
(El A)⁺ = El A⁺

 Γ ⊢ t : A
────────────
Γ⁺ ⊢ t⁺ : A⁺

U'⁺ = U'

((a : A) → B)⁺ =
  hyp:
    Γ⁺ ⊢ A⁺ : U
    Γ⁺, a⁺ : El A⁺ ⊢ B⁺ : U
  goal:
    Γ⁺ ⊢ _ : U


λU⁺ definition:
  hyp:
    Γ, a : El A ⊢ t : U
    Γ⁺ ⊢ A⁺ : U
    Γ⁺, a⁺ : El A⁺ ⊢ t⁺ : U
  goal:
    Γ ⊢ _ : El A⁺ →⁺ U
    Γ ⊢ _ : (E : U, e* : El E, code: [e* : El E](a : El A⁺) → U)

    let E   : U    = quoteEnv Γ t
        e*  : El E = idEnv Γ t
        El E ⊢ t⁺' = uncurry Γ t⁺






(λ a. t)⁺      = ?
  hyp:
    Γ, a : El A ⊢ t : El B
    Γ⁺ ⊢ A⁺ : U
    Γ⁺, a⁺ : El A⁺ ⊢ B⁺ : U
    Γ⁺, a⁺ : El A⁺ ⊢ t⁺ : El B⁺
  goal:
    Γ⁺ ⊢ _ : (a : El A⁺) →⁺ El B⁺

(t u)⁺  = appᶜ(t⁺, u⁺)
x⁺      = x⁺


```

- We must be able to convert from types to codes, in an "inverse"
  operation to El. We need this because in every closure Γ must be
  reflected down to a code and stored there.

- We should be able to translate from a Russell-style U:U source
  language. There are still separate translations for types and
  codes, and we have to determine from context which one to use, in
  the absence of El. If we have this kind of source language, there is
  less back-and-forth "churn" in closure conversion, because
  types-as-types can be directly translated to types, instead of first
  translating to codes and the El-ing to types. However, translating
  types-as-codes to codes can't be avoided in general.

- (El ((a : A) → B)⁺) must be equal to ((a : A) →⁺ B).

- We must be able to trim contexts to the minimal dependencies of a term.
  It's not just FreeVars(t). We need to recursively consider variables, types of
  variables and variables inside types of variables.


-- Scratchpad
------------------------------------------------------------

-- (λ a. t)⁺
------------------------------------------------------------

Γ, a : El A ⊢ B : U
Γ, a : El A ⊢ t : El B
Γ⁺, a⁺ : El A⁺ ⊢ B⁺ : U
Γ⁺, a⁺ : El A⁺ ⊢ t⁺ : El B⁺

First without trimming

Goal type : `(E : U, e* : El E, code : [e* : El E](a : El A⁺) → El B⁺)`

  E := quote(Γ⁺)
  e* := vars(Γ⁺) : quote(Γ⁺)

Inner type of code:

  code : (x : (e : E, El A⁺[xᵢ ⊢> πᵢ e])) → El B⁺[xᵢ ⊢> πᵢ x]

Therefore:
```
  code :
    [vars(Γ⁺) : quote(Γ⁺)]
	(a : El (A⁺[xᵢ ⊢> πᵢ e][e ⊢> vars(Γ⁺)]))
	→ El (B⁺[xᵢ ⊢> πᵢ x][x ⊢> (vars(Γ⁺), a)])

  code :
    [vars(Γ⁺) : quote(Γ⁺)]
	(a : El (A⁺[xᵢ ⊢> πᵢ (vars(Γ⁺))]))
	→ El (B⁺[xᵢ ⊢> πᵢ x][x ⊢> (vars(Γ⁺), a)])
```


<!-- ##### Closure conversion (TODO) -->

<!-- ``` -->

<!-- Γ ⊢ -->
<!-- ──── -->
<!-- Γ⁺ ⊢ -->

<!-- ∙⁺          = ∙ -->
<!-- (Γ, a : A)⁺ = (Γ⁺, a⁺ : A⁺) -->

<!-- Γ ⊢ A -->
<!-- ─────── -->
<!-- Γ⁺ ⊢ A⁺ -->

<!-- U⁺      = U -->
<!-- (El A)⁺ = El A⁺ -->

<!--  Γ ⊢ t : A -->
<!-- ──────────── -->
<!-- Γ⁺ ⊢ t⁺ : A⁺ -->

<!-- x⁺    = x⁺ -->
<!-- ⊤⁺    = ⊤' -->
<!-- ⊥⁺    = ⊥' -->
<!-- U'⁺   = U' -->
<!-- Bool⁺ = Bool' -->

<!-- ((a : A) → B)⁺ = ? -->
<!-- (λ a. t)⁺      = ? -->
<!-- (a : A, B)⁺    = (A⁺; (λ a. B)⁺) -->
<!--                  (λ a . B) : El ((a : A) → U') -->


<!-- (t u)⁺         = appᶜ(t⁺, u⁺) -->

<!-- (π₁ t)⁺                  = π₁ t⁺ -->
<!-- (π₂ t)⁺                  = π₂ t⁺ -->
<!-- (t, u)⁺                  = (t⁺, u⁺) -->
<!-- true⁺                    = true -->
<!-- false⁺                   = false -->
<!-- (Bool-elim (x.B) t f b)⁺ = Bool-elim (x⁺.B⁺) t⁺ f⁺ b⁺ -->
<!-- ``` -->

<!-- - We must be able to convert from types to codes, in an "inverse" -->
<!--   operation to El. We need this because in every closure Γ must be -->
<!--   reflected down to a code and stored there. -->

<!-- - We should be able to translate from a Russell-style U:U source -->
<!--   language. There are still separate translations for types and -->
<!--   codes, and we have to determine from context which one to use, in -->
<!--   the absence of El. If we have this kind of source language, there is -->
<!--   less back-and-forth "churn" in closure conversion, because -->
<!--   types-as-types can be directly translated to types, instead of first -->
<!--   translating to codes and the El-ing to types. However, translating -->
<!--   types-as-codes to codes can't be avoided in general. -->

<!-- - (El ((a : A) → B)⁺) must be equal to ((a : A) →⁺ B). -->

<!-- - We must be able to trim contexts to the minimal dependencies of a term. -->
<!--   It's not just FreeVars(t). We need to recursively consider variables, types of -->
<!--   variables and variables inside types of variables. -->


<!-- -- Scratchpad -->
<!-- ------------------------------------------------------------ -->

<!-- -- (λ a. t)⁺ -->
<!-- ------------------------------------------------------------ -->

<!-- Γ, a : El A ⊢ B : U -->
<!-- Γ, a : El A ⊢ t : El B -->
<!-- Γ⁺, a⁺ : El A⁺ ⊢ B⁺ : U -->
<!-- Γ⁺, a⁺ : El A⁺ ⊢ t⁺ : El B⁺ -->

<!-- First without trimming -->

<!-- Goal type : `(E : U, e* : El E, code : [e* : El E](a : El A⁺) → El B⁺)` -->

<!--   E := quote(Γ⁺) -->
<!--   e* := vars(Γ⁺) : quote(Γ⁺) -->

<!-- Inner type of code: -->

<!--   code : (x : (e : E, El A⁺[xᵢ ⊢> πᵢ e])) → El B⁺[xᵢ ⊢> πᵢ x] -->

<!-- Therefore: -->
<!-- ``` -->
<!--   code : -->
<!--     [vars(Γ⁺) : quote(Γ⁺)] -->
<!-- 	(a : El (A⁺[xᵢ ⊢> πᵢ e][e ⊢> vars(Γ⁺)])) -->
<!-- 	→ El (B⁺[xᵢ ⊢> πᵢ x][x ⊢> (vars(Γ⁺), a)]) -->

<!--   code : -->
<!--     [vars(Γ⁺) : quote(Γ⁺)] -->
<!-- 	(a : El (A⁺[xᵢ ⊢> πᵢ (vars(Γ⁺))])) -->
<!-- 	→ El (B⁺[xᵢ ⊢> πᵢ x][x ⊢> (vars(Γ⁺), a)]) -->
<!-- ``` -->
