### Closure conversion for simple type theory

#### Currently, we have 

- A source theory with `Bool` and finite products.
- A target theory with closed functions and closures (*not* existentials, a primitive closure type former is enough)
- An implementation of closure conversion from source to target
- A proof that closure conversion preserves term convertibility
- A proof that closure conversion preserves standard type-theoretic semantics
- A proof that closure conversion preserves observational equivalence, i. e. full abstraction

The code duplication is awful here. I have copy & pasted tons of code between the two slightly different theories, and also between the **four** bloody logical relations we have, two for obs. equivalence in source and target theories, and two for forward and backward translation correctness.

This directory was last checked with the https://github.com/agda/agda/commit/f6dd1f2 Agda version. Newer than 2018 february Agdas should work. 

#### TODO

- Add proofs that logical relational definitions of observational equivalence coincide with the contextual definitions. This should be a standard proof, from PFPL chapter 46.
- Decrease code duplication
