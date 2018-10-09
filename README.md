# `Impure`: importing OCaml functions as non-deterministic ones.

The principle of this library is to encode the type `A -> B` of an
OCaml function as a type `A -> ?? B` in Coq, where `?? B` is the type
of an axiomatized monad that can be interpreted as `B -> Prop`.  In
other word, this encoding abstracts an OCaml function as a function
returning a postcondition on its possible results (ie a relation between its
parameter and its result). Side-effects are simply ignored. And
reasoning on such a function is only possible in partial correctness.

A major feature of this cooperation between Coq and OCaml typechecker is to provide very simple [parametric proofs](http://homepages.inf.ed.ac.uk/wadler/topics/parametricity.html) about polymorphic OCaml functions.
They correspond here to prove, by reasoning only on their type, that these functions preserve some invariants.
As an example, we prove the partial correctness of a generic memoizing fixpoint operator: see `rec_correct` lemma at the end of [ImpExtern](ImpExtern.v).
This lemma is applied in [FibExample](FibExample.v) to prove the partial correctness of a memoized version of the naive Fibonacci function.
However, currently, the soundness of these parametric proofs is still a conjecture.

## Code Overview

- [ImpMonads](ImpMonads.v) axioms of "impure computations" and some Coq models of these axioms.

- [ImpConfig](ImpConfig.v) declares the `Impure` monad and defines its extraction.

- [ImpCore](ImpCore.v) defines notations for the `Impure` monad and a `wlp_simplify` tactic (to reason about `Impure` functions in a Hoare-logic style).

- [ImpPrelude](ImpPrelude.v) declares the data types exchanged with `Impure` oracles.

- [ImpIO](ImpIO.v), [ImpLoops](ImpLoops.v), [ImpHCons](ImpHCons.v) declare `Impure` oracles and define operators from these oracles.
  [ImpExtern](ImpExtern.v) exports all these impure operators.

- [ocaml/](ocaml/) subdirectory containing the OCaml implementations of `Impure` oracles.

