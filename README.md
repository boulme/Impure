# `Impure`: importing OCaml functions as non-deterministic ones.

The principle of this library is to encode the type `A -> B` of an
OCaml function as a type `A -> ?? B` in Coq, where `?? B` is the type
of an axiomatized monad that can be interpreted as `B -> Prop`.  In
other word, this encoding abstracts an OCaml function as a function
returning a postcondition on its possible results (ie a relation between its
parameter and its result). Side-effects are simply ignored. And
reasoning on such a function is only possible in partial correctness.

See further explanations and examples on [ImpureDemo](https://github.com/boulme/ImpureDemo).

## Credits

[Sylvain Boulmé](mailto:Sylvain.Boulme@univ-grenoble-alpes.fr).

## Code Overview

- [ImpMonads](ImpMonads.v) axioms of "impure computations" and some Coq models of these axioms.

- [ImpConfig](ImpConfig.v) declares the `Impure` monad and defines its extraction.

- [ImpCore](ImpCore.v) defines notations for the `Impure` monad and a `wlp_simplify` tactic (to reason about `Impure` functions in a Hoare-logic style).

- [ImpPrelude](ImpPrelude.v) declares the data types exchanged with `Impure` oracles.

- [ImpIO](ImpIO.v), [ImpLoops](ImpLoops.v), [ImpHCons](ImpHCons.v) declare `Impure` oracles and define operators from these oracles.
  [ImpExtern](ImpExtern.v) exports all these impure operators.

- [ocaml/](ocaml/) subdirectory containing the OCaml implementations of `Impure` oracles.

