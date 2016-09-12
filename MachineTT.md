## Near-machine type theory

Idea: have a dependent type theory that can be immediately compiled to machine code.

It would look like an extension of ["intensional polymorphism"](https://www.cs.cmu.edu/~rwh/papers/intensional/popl95.pdf) by [Harper](https://www.cs.cmu.edu/~rwh/papers/closures/tr.pdf) and [others](https://www.cs.cornell.edu/talc/papers/typepass.pdf) , with notable differences:

 - It's parametric, and there's no typecase at all. The purpose of the system is to allow non-uniform *memory representation* depending on type structure, but there's no reason to have non-uniform program behavior.
 - Full dependent types with much more representational freedom. In particular, we may have values of statically unknown sigma types represented as a contiguous piece of memory where the layout of the second projection is determined by a type function (also possibly statically unknown) and the value of the first projection.
 - Lots of crazy stuff (explanation pending).
 
The essence of the system is **having only closed functions**. We start from that and try to recover as much stuff from usual type theory as possible.
 
Main TODOs:

 - Sane account of dependently typed partial application and closure conversion.
  - Can we perform *some* open-environment type-level evaluation statically without sacrificing runtime closedness?
 - A final word on whether we really can get away with closed functions in reasonably complex systems.
 - A type universe that captures as much as possible memory-representational equality in judgemental equality.
  - For example, `Int x (Int x Int)` is representationally the same as `(Int x Int) x Int` with flat products, so we want to make them definitionally equal. One way to do it would be to have telescopes instead of binary products.
 - A sane account of levitated type representations.
 - Deciding whether we can and should make use of "extra" representational equivalences, such as weakening functions from telescopes to functions from larger telescopes (which is a bit like OOP subtyping). 
