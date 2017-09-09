
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

The source langage contains a Tarski-style universe closed under `Σ,
Π, ⊤, ⊥, Bool`. It also contains a code for _itself_, since on the
first iteration it is convenient to assume type-in-type.

The target language:
  - Only has closed functions, i. e. lambdas constructed in the empty context.
  - Has a Tarski-style universe of type codes, as well as type formers which
    codes decode to. The type formers are usual, however, type codes are
    CC-d, and decoding un-CC-s them.

Couldn't we only have CC-d types? As far as I see the answer is no.
The reason is that closure converted Π is defined in terms of Σ, but
closure converted Σ is defined in terms of closure converted
Π. Therefore we can't simultaneously define only CC-d Π and Σ.

In my previous research, I was experimenting with Π and Σ formers with
raw closed `El A → U` functions for codomains/second
projections. However, closedness is a severe limitation and I had a
hard time making things work that way.

##### Source language, Tarski-style
```
Γ ⊢          Context well-formedness
Γ ⊢ A        Type well-formedness
Γ ⊢ t : A    Typing

─────
Γ ⊢ U

─────────
Γ ⊢ ⊥ : U

Γ ⊢ A : U
─────────
Γ ⊢ El A

Γ ⊢ A   Γ ⊢ t : El ⊥
────────────────────
 Γ ⊢ ⊥-elim t : A

─────────
Γ ⊢ ⊤ : U

─────────────
Γ ⊢ tt : El ⊤

Γ ⊢ A : U   Γ, a : El A ⊢ B : U
───────────────────────────────
     Γ ⊢ (a : A) → B : U

Γ ⊢ A : U   Γ, a : El A ⊢ B : U
───────────────────────────────
     Γ ⊢ (a : A, B) : U

 Γ, a : El A ⊢ t : El B
────────────────────────
Γ ⊢ λ a. t : (a : A) → B

Γ ⊢ t : El A   Γ, a : El A ⊢ B : U   Γ ⊢ u : El (B[a ⊢> t])
─────────────────────────────────────────────────────────
           Γ ⊢ (t, u) : El (t : A, B)

Γ ⊢ t : El ((a : A) → B)   Γ ⊢ u : El A
───────────────────────────────────────
      Γ ⊢ t u : El (B[a ⊢> u])

        Γ ⊢ t : El (a : A, B)
───────────────────────────────────────
Γ ⊢ π₁ t : El A   Γ ⊢ π₂ t : El (B[a ⊢> π₁ t])

────────────
Γ ⊢ Bool : U

────────────────────────────────────────
Γ ⊢ true : El Bool   Γ ⊢ false : El Bool

                Γ, x : El Bool ⊢ B
Γ ⊢ t : El (B[x ⊢> true])   Γ ⊢ u : El (B[x ⊢> false])
                 Γ ⊢ b : El Bool
────────────────────────────────────────────────────────
       Γ ⊢ Bool-elim (x.B) t f b : B[x ⊢> b]
```

##### Source language, Russell-style

We can see this version just as a shorthand for the Tarski-style universes, with elided `El` noise


```
Γ ⊢          Context well-formedness
Γ ⊢ A        Type well-formedness
Γ ⊢ t : A    Typing

─────
Γ ⊢ U

Γ ⊢ A : U
─────────
Γ ⊢ A

─────────
Γ ⊢ ⊥ : U

Γ ⊢ A  Γ ⊢ t : ⊥
────────────────
Γ ⊢ ⊥-elim t : A

─────────
Γ ⊢ ⊤ : U

─────────────
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

Γ ⊢ A : U   Γ, a : A ⊢ B : U
────────────────────────────
     Γ ⊢ (a : A, B) : U

Γ ⊢ t : A   Γ, a : A ⊢ B : U   Γ ⊢ u : B[a ⊢> t]
────────────────────────────────────────────────
          Γ ⊢ (t, u) : (t : A, B)

         Γ ⊢ t : (a : A, B)
──────────────────────────────────────
Γ ⊢ π₁ t : A   Γ ⊢ π₂ t : B[a ⊢> π₁ t]

────────────
Γ ⊢ Bool : U

──────────────────────────────────
Γ ⊢ true : Bool   Γ ⊢ false : Bool

            Γ, x : Bool ⊢ B
Γ ⊢ t : B[x ⊢> true]   Γ ⊢ u : B[x ⊢> false]
            Γ ⊢ b : El Bool
────────────────────────────────────────────
   Γ ⊢ Bool-elim (x.B) t f b : B[x ⊢> b]
```

##### Target language

```
Γ ⊢          Context well-formedness
Γ ⊢ A        Type well-formedness
Γ ⊢ t : A    Typing

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

Γ ⊢ A   Γ ⊢ t : ⊥
─────────────────
Γ ⊢ ⊥-elim t : A

Γ ⊢ A : U   Γ, a : El A ⊢ B : U
───────────────────────────────
      Γ ⊢ (a : A) → B

Γ ⊢ A : U   Γ, a : El A ⊢ B : U
───────────────────────────────
      Γ ⊢ (a : A, B)

────────
Γ ⊢ Bool

──────────────────────────────────
Γ ⊢ true : Bool   Γ ⊢ false : Bool

                Γ, x : Bool ⊢ B
Γ ⊢ t : El (B[x ⊢> true])   Γ ⊢ u : El (B[x ⊢> false])
                 Γ ⊢ b : Bool
────────────────────────────────────────────────────────
       Γ ⊢ Bool-elim (x.B) t f b : B[x ⊢> b]









─────────
Γ ⊢ ⊤ : U



Γ ⊢ A : U   Γ, a : El A ⊢ B : U
───────────────────────────────
     Γ ⊢ (a : A) → B : U

Γ ⊢ A : U   Γ, a : El A ⊢ B : U
───────────────────────────────
     Γ ⊢ (a : A, B) : U

 Γ, a : El A ⊢ t : El B
────────────────────────
Γ ⊢ λ a. t : (a : A) → B

Γ ⊢ t : El A   Γ, a : El A ⊢ B : U   Γ ⊢ u : El (B[a ⊢> t])
─────────────────────────────────────────────────────────
           Γ ⊢ (t, u) : El (t : A, B)

Γ ⊢ t : El ((a : A) → B)   Γ ⊢ u : El A
───────────────────────────────────────
      Γ ⊢ t u : El (B[a ⊢> u])

        Γ ⊢ t : El (a : A, B)
───────────────────────────────────────
Γ ⊢ π₁ t : El A   Γ ⊢ π₂ t : El (B[a ⊢> π₁ t])

────────────
Γ ⊢ Bool : U

────────────────────────────────────────
Γ ⊢ true : El Bool   Γ ⊢ false : El Bool

                Γ, x : El Bool ⊢ B
Γ ⊢ t : El (B[x ⊢> true])   Γ ⊢ u : El (B[x ⊢> false])
                 Γ ⊢ b : El Bool
────────────────────────────────────────────────────────
       Γ ⊢ Bool-elim (x.B) t f b : B[x ⊢> b]
```
