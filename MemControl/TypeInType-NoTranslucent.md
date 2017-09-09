
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
Contrasting [Minamide et
al.](https://www.cs.cmu.edu/~rwh/papers/closures/tr.pdf), we do not use
"translucent" functions. Instead, we use propositional equality to represent them.
This has the major advantage of being a standard construction, and it also preserves
unicity of typing. However, the resulting closures contain extra computationally irrelevant
types. It's future work to make them erasible somehow.

We omit context formation, congruence closure and substitution
calculus rules below. Also, we leave weakening implicit and omit
inferable preconditions.

We do field access sugar for nested `Σ` projections. For example, if
`t : (a : A, b : B, c : C)`, then `t.b : B[a ⊢> t.a]`. Note that we
can also name the last field of a nested `Σ`.

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

Γ ⊢ A : U   Γ ⊢ t, u : A
─────────────────────────
     Γ ⊢ t = u : U

   Γ ⊢ t : A
──────────────────
Γ ⊢ refl t : t = t

Γ ⊢ eq : t = u   Γ, u : A, eq : t = u ⊢ P : U
      Γ ⊢ r : P[u ⊢> t, eq ⊢> refl t]
──────────────────────────────────────────────
    Γ ⊢ J t u eq (u.eq.P) r : P[u ⊢> u, eq ⊢> eq]

J t t (refl t) (u.eq.P) r ≡ r
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
───────────────────────────────────
      Γ ⊢ t u : El (B[a ⊢> u])

(λ a. t) u ≡ t[a ⊢> u]

Γ ⊢ A : U   Γ, a : El A ⊢ B : U
───────────────────────────────
      Γ ⊢ (a : A, B)

Γ ⊢ t : El A   Γ, a : El A ⊢ B : U   Γ ⊢ u : El (B[a ⊢> t])
───────────────────────────────────────────────────────────
             Γ ⊢ (t, u) : (t : A, B)

             Γ ⊢ t : (a : A, B)
─────────────────────────────────────────────
Γ ⊢ π₁ t : El A   Γ ⊢ π₂ t : El (B[a ⊢> π₁ t])

π₁ (t, u) ≡ t   π₂ (t, u) ≡ u

────────
Γ ⊢ Bool

──────────────────────────────────
Γ ⊢ true : Bool   Γ ⊢ false : Bool

                Γ, x : Bool ⊢ B : U
Γ ⊢ t : El (B[x ⊢> true])   Γ ⊢ u : El (B[x ⊢> false])
                 Γ ⊢ b : Bool
───────────────────────────────────────────────────────
    Γ ⊢ Bool-elim (x.B) t f b : El (B[x ⊢> b])

Bool-elim (x.B) t f true ≡ t
Bool-elim (x.B) t f false ≡ f

Γ ⊢ A : U   Γ ⊢ t, u : El A
───────────────────────────
     Γ ⊢ t = u : U

   Γ ⊢ t : El A
──────────────────
Γ ⊢ refl t : t = t

Γ ⊢ eq : t = u   Γ, u : El A, eq : t = u ⊢ P
      Γ ⊢ r : P[u ⊢> t, eq ⊢> refl t]
─────────────────────────────────────────────
Γ ⊢ J t u eq (u.eq.P) r : P[u ⊢> u, eq ⊢> eq]

J t t (refl t) (u.eq.P) r ≡ r

Coercion

Γ ⊢ A, B : U   Γ ⊢ eq : A = B   Γ ⊢ t : El A
─────────────────────────────────────────────
  coe eq t := J A B eq (u.eq.El u) t : El B

Transport

       Γ ⊢ eq : t = u   Γ, u : El A ⊢ P
              Γ ⊢ r : P[u ⊢> t]
─────────────────────────────────────────────────────
transp (u.P) eq r := J t u eq (u.eq.P) r : P[u ⊢> u]


Closure-converted function space

         Γ ⊢ A : U   Γ, a : El A ⊢ B : U
─────────────────────────────────────────────────────
(a : A) →⁺ B :=
  (E    : U,
   e*   : El E,
   A'   : E → U,
   B'   : (e : E, A' e) → U,
   eqA' : A = A' e*,
   <!-- eqB' : (a : A) → B [a ⊢> a] = B' (e*, transp (x.El x) eqA' a) -->
   <!-- eqB' : (λ a. B) = (λ a. B' (e*, transp (x.El x) eqA' a)),  -- !!!!! ISSUE -->
   code : (x : (e : E, A' e)) → B' x)

Closure application

Γ ⊢ t : (a : A) →⁺ B   Γ ⊢ u : El A
───────────────────────────────────
(t u)⁺ := let (E, e*, A', B', eqA', eqB', code) = t in

  code (e*, transp (x.El x) eqA' u) : El (B' (e* , transp (x.El x) eqA' u))


  El (B' (e* , transp (x.El x) eqA' u)) = El (B [a ⊢> u])

  transp (f. El (f u))

    <!-- transp (x.El x)  -->
    <!--   (transp (f. f u = B[a ⊢> u]) eqB' (refl (B[a ⊢> u])))  -->
      (code (e*, transp (x.El x) eqA' u))



  B' (e* , transp (x.El x) eqA' u)) = B [a ⊢> u]

eqB' : (λ a. B) = (λ a. B' (e*, transp (x.El x) eqA' a))
refl (B [a ⊢> u]) : B [a ⊢> u] = B [a ⊢> u]

transp (f. f u = B[a ⊢> u]) eqB' (refl (B[a ⊢> u])) :
  B' (e*, transp (x.El x) eqA' a) = B [a ⊢> u]


  <!-- J (λ a. B) (λ a. B' (e*, transp (x.El x) eqA' a)) eqB' -->
  <!--   (u.eq. -->

  <!--   J  -->

  <!--   <\!-- eqB ⁻¹ : (λ a. B' (e*, transp (x.El x) eqA' a)) = (λ a. B) -\-> -->

  <!--   <\!-- J (λ a. B) (λ a. B' (e*, transp (x.El x) eqA' a)) eqB (u.eq.  -\-> -->


  <!--   ap f p = J t u p (u.eq.  -->












Γ ⊢ t : (a : A) ~> B   Γ ⊢ u : A
────────────────────────────────
(t u)⁺ :=

Codes

──────────
Γ ⊢ ⊤' : U

El ⊤' ≡ ⊤

──────────
Γ ⊢ ⊥' : U

El ⊥' ≡ ⊥

─────────────
Γ ⊢ Bool' : U

El Bool' ≡ Bool

Γ ⊢ A : U   Γ ⊢ B : A ~> U
──────────────────────────









```
