

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
than the alternative solution (that I've found so far), which uses propositional
equality with irrelevant quantification. On the long run, the alternative solution
might be better, since we'd like to have some form of robust erasure anyway.

We omit congruence closure and substitution
calculus rules below. Also, we leave weakening implicit and omit
inferable preconditions.

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
────────────────────────
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
────────────────────────────────────────────────────────    PROBLEM
(a : A) →⁺ B := (E : U, e* : E, code: [e* : E](a : A) → B)

 Γ ⊢ t : (a : A) →⁺ B   Γ ⊢ u : El A
──────────────────────────────────────
(t u)⁺ := t.code (t.e*, u) : El (B[a ⊢> u])


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
   Γ ⊢ (a : A; B) : U

El (A; B) ≡ (a : A, (B a)⁺)

Γ ⊢ E : U   Γ ⊢ e* : E   Γ ⊢ A : U   Γ ⊢ B : A →⁺ U'
───────────────────────────────────────────────────
       Γ ⊢ [e : E*] A →' B : U

El ([e* : E] A →' B : U) ≡ ([e* : E](a : A) → (B a)⁺)

```

Some examples in the target theory.

```
idU : (A : U') → U'
idU = λ A. A

id : (x : (A : U'; (⊤', tt, λ y.π₂ y))) → π₁ x
id = λ x. π₂ x

sum : (x : (A : U; (⊤', tt, λ _.U'))) → U'
sum =
  λ (A, B). (b : Bool';
         ((A : U; (⊤', tt, λ _.U')),
          (A, B),
          λ ((A, B), b). Bool-elim (x.U') A B b))

sum (Bool', Bool')
  ≡ (b : Bool'; ((A : U; (⊤', tt, λ _.U')),
                 (Bool', Bool'), λ ((A, B), b). Bool-elim (x.U') A B b))

(true, false) : El (sum (Bool', Bool'))

```

##### Closure conversion (TODO)

```
Quoting

      Γ ⊢
───────────────
∙ ⊢ quote Γ : U

               Γ ⊢ A
────────────────────────────────────
∙ ⊢ quote Γ A : (env : quote Γ) → U'

                   Γ ⊢ t : A
───────────────────────────────────────────────
∙ ⊢ quote Γ t : (env : quote Γ) → quote Γ A env

quote ∙          = ⊤'
quote (Γ, a : A) = (quote Γ; (⊤', tt, λ env. quote Γ A (π₂ env)))


Closure building

        Γ, a : A ⊢ B
──────────────────────────────
Γ ⊢ close Γ A B : (a : A) →⁺ U'

Environment trimming

        Γ ⊢ A
─────────────────────
fvs(A) ⊢   fvs(A) ⊢ A

                  Γ ⊢ t : A
───────────────────────────────────────────────
fvs(A, t) ⊢   fvs(A, t) ⊢ A   fvs(A, t) ⊢ t : A

Conversion

Γ ⊢
────
Γ⁺ ⊢

 Γ ⊢ A
───────
Γ⁺ ⊢ A⁺

 Γ ⊢ t : A
────────────
Γ⁺ ⊢ t⁺ : A⁺

∙⁺          = ∙
(Γ, a : A)⁺ = (Γ⁺, a⁺ : A⁺)

U⁺      = U
(El A)⁺ = El A⁺

⊤⁺    = ⊤'
⊥⁺    = ⊥'
Bool⁺ = Bool'
U'⁺   = U'

We want this to hold:
  El (quote Γ) = Σ Γ

Where Σ Γ is the iterated Σ type from Γ

Some handwaving in B⁺[xᵢ ⊢> πᵢ γ]. More precisely, we want to rename B⁺ to fvs(B⁺),
then uncurry to Σ (fvs(B⁺))
  (a : A, B)⁺ = (A⁺; (quote (fvs(λa.B⁺)), vars (fvs(λa.B⁺)), λ γ. B⁺[xᵢ ⊢> πᵢ γ]))


  ((a : A) → B)⁺ =



```




<!-- Γ ⊢ A -->
<!-- ───── -->
<!-- Γ ⊢  -->

<!-- Translation -->

<!-- ∙⁺          = ∙ -->
<!-- (Γ, a : A)⁺ = (Γ⁺, a⁺ : A⁺) -->

<!-- U⁺      = U -->
<!-- (El A)⁺ = El A⁺ -->

<!-- ⊤⁺    = ⊤' -->
<!-- ⊥⁺    = ⊥' -->
<!-- Bool⁺ = Bool' -->
<!-- U'⁺   = U' -->

<!-- (a : A, B)⁺ = (A⁺; close Γ B⁺) -->

<!-- ((a : A) → B)⁺ =  ? -->


<!-- Closing over the last free variable, in target theory -->

<!-- Γ ⊢ A   Γ ⊢ t : A -->
<!-- ───────────────── -->
<!--  fvs(Γ, A, t) ⊢  -->

<!--        Γ ⊢ -->
<!-- ────────────────── -->
<!-- ∙ ⊢ reflectCon Γ : U -->

<!-- reflectCon ∙          = ⊤ -->
<!-- reflectCon (Γ, a : A) = (reflectCon Γ; reflectTy Γ A) -->

<!--       Γ ⊢ -->
<!-- ─────────────── -->
<!-- ∙ ⊢ quote Γ : U -->

<!--                   Γ ⊢ t : A -->
<!-- ───────────────────────────────────────────────── -->
<!-- ∙ ⊢ close Γ t : (env : close Γ) → A[xᵢ ⊢> πᵢ env] -->


<!-- ((a : A) → B)⁺ =  -->

<!--   (E : U; (⊤', tt, λ (tt, E). -->
<!--    (e* : E; ((EnvA; U'), (envA, E), λ ((envA, E), e*). -->
<!--      [e* : E](a : close A⁺) →' ((EnvB; A⁺), (envB, a), λ (envb, _). close B⁺) -->

<!--   (U'; λ [E]. (e* : E -->


<!--    (e* : E; ((EnvA; U'), (envA, E), λ ((envA, E), e*). -->
<!--      [e* : E](a : close A⁺) →' close B⁺) -->
