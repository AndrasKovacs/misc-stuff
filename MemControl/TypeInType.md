
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
level would need to be computed as well. A simplified example:

```
(F : U0 → U0) ⊢ F Bool → F Bool : U0
⊢ Σ (F : U0 → U0). F Bool → F Bool : U1
```
Following [Minamide et
al.](https://www.cs.cmu.edu/~rwh/papers/closures/tr.pdf), I use
translucent function type for closures. Although translucent functions are
non-standard type theory and violate unicity of typing, it seems to be simpler
than the alternative solution (that I've found so far), which is propositional
equality with irrelevant quantification. On the long run, the alternative solution
might be better, since we'd like to have some form of robust erasure in any case.

We omit context formation, congruence closure and substitution
calculus rules below. Also, we leave weakening implicit and omit
inferable preconditions.

##### Source language

```
Γ ⊢          Context formation
Γ ⊢ t : A    Typing

───
∙ ⊢

Γ ⊢   Γ ⊢ A
───────────
Γ, a : A ⊢

─────────
Γ ⊢ U : U

─────────
Γ ⊢ ⊥ : U

Γ ⊢ A : U   Γ ⊢ t : ⊥
─────────────────────
Γ ⊢ ⊥-elim A t : A

─────────
Γ ⊢ ⊤ : U

──────────
Γ ⊢ tt : ⊤

Γ ⊢ A : U   Γ, a : A ⊢ B : U
─────────────────────────────
     Γ ⊢ (a : A) → B : U

   Γ, a : A ⊢ t : B
────────────────────────
Γ ⊢ λ a. t : (a : A) → B

Γ ⊢ t : (a : A) → B   Γ ⊢ u : A
───────────────────────────────
    Γ ⊢ t u : B[a ⊢> u]

(λ a. t) u ≡ t[a ⊢> u]

Γ ⊢ A : U   Γ, a : A ⊢ B : U
────────────────────────────
     Γ ⊢ (a : A, B) : U

Γ ⊢ t : A   Γ, a : A ⊢ B : U   Γ ⊢ u : B[a ⊢> t]
────────────────────────────────────────────────
          Γ ⊢ (t, u) : (t : A, B)

         Γ ⊢ t : (a : A, B)
──────────────────────────────────────
Γ ⊢ π₁ t : A   Γ ⊢ π₂ t : B[a ⊢> π₁ t]

π₁ (t, u) ≡ t   π₂ (t, u) ≡ u

────────────
Γ ⊢ Bool : U

──────────────────────────────────
Γ ⊢ true : Bool   Γ ⊢ false : Bool

            Γ, x : Bool ⊢ B : U
Γ ⊢ t : B[x ⊢> true]   Γ ⊢ u : B[x ⊢> false]
            Γ ⊢ b : El Bool
────────────────────────────────────────────
   Γ ⊢ Bool-elim (x.B) t f b : B[x ⊢> b]

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

Γ ⊢ A : U   Γ ⊢ t : ⊥
─────────────────────
Γ ⊢ ⊥-elim t : El A

Γ ⊢ A : U   Γ, a : El A ⊢ B : U
───────────────────────────────
      Γ ⊢ (a : A) → B

 ∙, a : El A ⊢ t : El B
────────────────────────
Γ ⊢ λ a. t : (a : A) → B

Γ ⊢ t : (a : A) → B   Γ ⊢ u : El A
──────────────────────────────────
    Γ ⊢ t u : El (B[a ⊢> u])

Γ ⊢ A : U   Γ, a : El A ⊢ B : U
───────────────────────────────
      Γ ⊢ (a : A, B)

Γ ⊢ t : El A   Γ, a : El A ⊢ B : U   Γ ⊢ u : El (B[a ⊢> t])
───────────────────────────────────────────────────────────
             Γ ⊢ (t, u) : (t : A, B)

             Γ ⊢ t : (a : A, B)
─────────────────────────────────────────────
Γ ⊢ π₁ t : El A   Γ ⊢ π₂ t : El (B[a ⊢> π₁ t])

────────
Γ ⊢ Bool

──────────────────────────────────
Γ ⊢ true : Bool   Γ ⊢ false : Bool

                Γ, x : Bool ⊢ B : U
Γ ⊢ t : El (B[x ⊢> true])   Γ ⊢ u : El (B[x ⊢> false])
                 Γ ⊢ b : Bool
───────────────────────────────────────────────────────
    Γ ⊢ Bool-elim (x.B) t f b : El (B[x ⊢> b])


Γ ⊢ E : U   e* : El E   Γ ⊢ A : U   Γ, a : El A ⊢ B : U
───────────────────────────────────────────────────────
              Γ ⊢ [e* : E](a : A) → B

 Γ ⊢ e* : El E   Γ ⊢ t : (x : (e : E, A)) → B
────────────────────────────────────────────────
Γ ⊢ t : [e* : E](a : A[e ⊢> e*]) → B[x ⊢> (e*, a)]


Closure-converted functions

            Γ ⊢ A : U   Γ, a : El A ⊢ B : U
─────────────────────────────────────────────────────────
(a : A) →⁺ B := (E : U, e* : E, code: [e* : E](a : A) → B)

 Γ ⊢ t : (a : A) →⁺ B   Γ ⊢ u : El A
──────────────────────────────────────
(t u)⁺ := t.code (t.e*, u) : B[a ⊢> u]


Codes

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

Γ ⊢ A : U   Γ ⊢ B : A →⁺ U'
──────────────────────────
   Γ ⊢ A →' B : U

El (A →' B) ≡ ((a : A) → (B a)⁺)

Γ ⊢ A : U   Γ ⊢ B : A →⁺ U'
──────────────────────────
   Γ ⊢ (A; B) : U

El (A; B) ≡ (a : A, (B a)⁺)

Γ ⊢ E : U   Γ ⊢ e* : E   Γ ⊢ A : U   Γ ⊢ B : A →⁺ U'
───────────────────────────────────────────────────
       Γ ⊢ [e* : E] A →' B : U

El ([e* : E] A →' B) ≡ ([e* : E](a : A) → (B a)⁺)

```

Some example terms in the target theory.

```
idU : (A : U') → U'
idU = λ A. A

id : (x : (A : U'; (⊤', tt, λ y.π₂ y))) → π₁ x
id = λ x. π₂ x
```

##### Closure conversion

```

Γ ⊢
────
Γ⁺ ⊢

 Γ ⊢ t : A
────────────
Γ⁺ ⊢ t⁺ : A⁺


U⁺ := U'




```
