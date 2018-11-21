(** Impure Config for UNTRUSTED backend !!! *)

Require Import ImpMonads.
Require Extraction.
(** Pure computations (used for extraction !) 

We keep module [Impure] opaque in order to check that Coq proof do not depend on 
the implementation of [Impure].

*)

Module Type ImpureView.

 Include MayReturnMonad.

(* WARNING: THIS IS REALLY UNSAFE TO DECOMMENT THE "UnsafeImpure" module !

   unsafe_coerce coerces an impure computation into a pure one !

*)

(*
 Module UnsafeImpure.

 Parameter unsafe_coerce: forall {A}, t A -> A.

 Parameter unsafe_coerce_not_really_correct: forall A (k: t A) (x:A), (unsafe_coerce k)=x -> mayRet k x. 

 End UnsafeImpure.
*)

End ImpureView.


Module Impure: ImpureView.

  Include IdentityMonad.

  Module UnsafeImpure.

  Definition unsafe_coerce {A} (x:t A) := x.

  Lemma unsafe_coerce_not_really_correct: forall A (k: t A) x, (unsafe_coerce k)=x -> mayRet k x.
  Proof.
    unfold unsafe_coerce, mayRet; auto.
  Qed.

  End UnsafeImpure.

End Impure.


(** Comment the above code and decomment this to test that coq proofs still work with an impure monad !

- this should fail only on extraction or if unsafe_coerce is used !

*)
(*
Module Impure: MayReturnMonad := PowerSetMonad.
*)

Export Impure.

Extraction Inline ret mk_annot.


(* WARNING. The following directive is unsound.

  Extraction Inline bind

For example, it may lead to extract the following code as "true" (instead of an error raising code)
  failwith "foo";;true

*)

Extract Inlined Constant bind => "(|>)".


Extract Constant t "" => "". (* This weird directive extracts [t] as "'a" instead of "'a t" *)
Extraction Inline t.

Global Opaque t.