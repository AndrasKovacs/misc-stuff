

### Intermediate dependent type theories
#### For precise memory layout control / intensional polymorphism

Basic idea: [intensional
polymorphism](https://www.cs.cmu.edu/~rwh/papers/intensional/popl95.pdf)
with dependent types should be able to support very precise and
flexible memory layout control, even in garbage collected runtime
systems.

To make this work, we definitely need a closure converted intermediate
language, as well as closure conversion (CC from now) algorithm into
that language (from a source type theory). Getting these two right is
good starting step in any case.

William Bowman [is working
on](https://www.williamjbowman.com/resources/cccc-extended-abstract.pdf)
CC for Calculus of Constructions. His reasearch focus seems to be
compiler correctness for Coq. However, that likely entails type
erasing code generation, while I aim for type passing. Thus, I need to
CC runtime type codes, not just term-level functions.

The version presented here has type-in-type for simplicity's sake.
With proper universes, the output universe of a CC-d type can be
arbitrarily large, depending on the captured environment, and the
level would need to be computed as well. The following function
has type in `U0`, but would have closure type in `U1`.

```
(f : U0 → Bool) ⊢ λ (x : Bool). f Bool : Bool → Bool
```

Since the closure level depends on function type and body, we would
need something like an "existential level" for proper closure abstraction.

Following [Minamide et
al.](https://www.cs.cmu.edu/~rwh/papers/closures/tr.pdf), I use
translucent function type for closures. Although translucent functions are
non-standard type theory and violate unicity of typing, it seems to be simpler
than the alternative solution (that I've found so far), which uses propositional
equality with irrelevant quantification. On the long run, the alternative solution
might be better, since we'd like to have some form of robust erasure anyway.

We omit congruence closure and substitution
calculus rules below. Also, we leave weakening implicit and omit
inferable preconditions.

We do field access sugar for nested `Σ` projections. For example, if
`t : (a : A, b : B, c : C)`, then `t.b : B[a ⊢> t.a]`. Note that we
can also name the last field of a nested `Σ`.

NOTES:

- What `El` is good for ultimately, is that it marks when types behave
in type-like manner, and when they behave in term-like
manner. Syntactic translations become confusing in Russell style
because we lose track of the different behaviors. But! I should try to do
Russell style source theory with two different translation judements
for terms; one for actual terms and one for type terms, and see if I
can switch correctly without `El`.

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

─────────
Γ ⊢ ⊥ : U

Γ ⊢ A : U   Γ ⊢ t : El ⊥
────────────────────────
Γ ⊢ ⊥-elim A t : El A

─────────
Γ ⊢ ⊤ : U

─────────────
Γ ⊢ tt : El ⊤

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

Γ ⊢ A : U   Γ, a : El A ⊢ B : U
───────────────────────────────
     Γ ⊢ (a : A, B) : U

Γ ⊢ t : El A   Γ, a : El A ⊢ B : U   Γ ⊢ u : El (B[a ⊢> t])
───────────────────────────────────────────────────────────
          Γ ⊢ (t, u) : El (t : A, B)

         Γ ⊢ t : (a : A, B)
──────────────────────────────────────
Γ ⊢ π₁ t : El A   Γ ⊢ π₂ t : El (B[a ⊢> π₁ t])

π₁ (t, u) ≡ t   π₂ (t, u) ≡ u

────────────
Γ ⊢ Bool : U

──────────────────────────────────
Γ ⊢ true : El Bool   Γ ⊢ false : El Bool

            Γ, x : El Bool ⊢ B : U
Γ ⊢ t : El (B[x ⊢> true])   Γ ⊢ u : El (B[x ⊢> false])
            Γ ⊢ b : El Bool
────────────────────────────────────────────
   Γ ⊢ Bool-elim (x.B) t f b : El (B[x ⊢> b])

Bool-elim (x.B) t f true ≡ t
Bool-elim (x.B) t f false ≡ f

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

─────
Γ ⊢ ⊥

Γ ⊢ A  Γ ⊢ t : ⊥
─────────────────
Γ ⊢ ⊥-elim t : A

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

Γ ⊢ A   Γ, a : A ⊢ B
────────────────────
   Γ ⊢ (a : A, B)

Γ ⊢ t : A   Γ, a : A ⊢ B   Γ ⊢ u : B[a ⊢> t]
────────────────────────────────────────────
         Γ ⊢ (t, u) : (t : A, B)

        Γ ⊢ t : (a : A, B)
──────────────────────────────────────
Γ ⊢ π₁ t : A   Γ ⊢ π₂ t : B[a ⊢> π₁ t]

π₁ (t, u) ≡ t   π₂ (t, u) ≡ u

────────
Γ ⊢ Bool

──────────────────────────────────
Γ ⊢ true : Bool   Γ ⊢ false : Bool

               Γ, x : Bool ⊢ B
Γ ⊢ t : B[x ⊢> true]   Γ ⊢ f : B[x ⊢> false]
               Γ ⊢ b : Bool
────────────────────────────────────────────
   Γ ⊢ Bool-elim (x.B) t f b : B[x ⊢> b]

Bool-elim (x.B) t f true  ≡ t
Bool-elim (x.B) t f false ≡ f

Γ ⊢ E   Γ ⊢ e* : E   Γ ⊢ A   Γ, a : A ⊢ B
─────────────────────────────────────────
        Γ ⊢ [e* : E](a : A) → B

   Γ ⊢ e* : E   Γ ⊢ t : (x : (e : E, A)) → B
─────────────────────────────────────────────────
Γ ⊢ t : [e* : E](a : A[e ⊢> e*]) → B[x ⊢> (e*, a)]

Closure-converted functions

                   Γ ⊢ A   Γ, a : A ⊢ B
────────────────────────────────────────────────────────────────
(a : A) →⁺ B := (E : U, e* : El E, code: [e* : El E](a : A) → B)

   Γ ⊢ t : (a : A) →⁺ B   Γ ⊢ u : A
──────────────────────────────────────────
appᶜ(t, u) := t.code (t.e*, u) : B[a ⊢> u]

Codes (Strongly Tarski)

──────────
Γ ⊢ U' : U

El U' ≡ U

──────────
Γ ⊢ ⊤' : U

El ⊤' ≡ ⊤

──────────
Γ ⊢ ⊥' : U

El ⊥' ≡ ⊥

─────────────
Γ ⊢ Bool' : U

El Bool' ≡ Bool

Γ ⊢ A : U   Γ ⊢ B : El A →⁺ U
──────────────────────────
    Γ ⊢ A →' B : U

El (A →' B) ≡ (a : El A) → El appᶜ(B, a)

Γ ⊢ A : U   Γ ⊢ B : El A →⁺ U
──────────────────────────
   Γ ⊢ (a : A; B) : U

El (A; B) ≡ (a : El A, El appᶜ(B, a))

Γ ⊢ E : U   Γ ⊢ e* : El E   Γ ⊢ A : U   Γ ⊢ B : El A →⁺ U
─────────────────────────────────────────────────────────
             Γ ⊢ [e : E*] A →' B : U

El ([e* : E] A →' B : U) ≡ [e* : El E](a : El A) → El appᶜ(B, a)

```

##### Closure conversion

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

x⁺    = x⁺
⊤⁺    = ⊤'
⊥⁺    = ⊥'
U'⁺   = U'
Bool⁺ = Bool'

((a : A) → B)⁺ = ?
(λ a. t)⁺      = ?
(a : A, B)⁺    = (A⁺; (λ a. B)⁺)
                 (λ a . B) : El ((a : A) → U')


(t u)⁺         = appᶜ(t⁺, u⁺)

(π₁ t)⁺                  = π₁ t⁺
(π₂ t)⁺                  = π₂ t⁺
(t, u)⁺                  = (t⁺, u⁺)
true⁺                    = true
false⁺                   = false
(Bool-elim (x.B) t f b)⁺ = Bool-elim (x⁺.B⁺) t⁺ f⁺ b⁺
```

- We must be able to convert from types to codes, in an "inverse"
  operation to El. We need this because in every closure Γ must be
  reflected down to a code and stored there.

- We should be able to translate from a Russell-style U:U source
  language.  There are still separate translations for types and
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
