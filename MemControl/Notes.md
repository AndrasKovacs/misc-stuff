
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

Formally: TODO

```
Source language

Judgements
    Γ ⊢          Context well-formedness
    Γ ⊢ A        Type well-formedness
    Γ ⊢ t : A    Typing
```
