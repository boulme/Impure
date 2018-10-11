(** Extension of Coq language with some IO and exception-handling operators.

TODO: integration with http://coq.io/ ?

*)

Require Export ImpPrelude.

Import Notations.
Local Open Scope impure.

(** Printing functions *)

Axiom print: pstring -> ?? unit.
Extract Constant print => "ImpIOOracles.print".

Axiom println: pstring -> ?? unit.
Extract Constant println => "ImpIOOracles.println".

Require Import ZArith.
Axiom string_of_Z: Z -> ?? pstring.
Extract Constant string_of_Z => "ImpIOOracles.string_of_Z".

(** timer *)

Axiom timer: forall {A B}, (A -> ?? B)*A -> ?? B.
Extract Constant timer => "ImpIOOracles.timer".

(** Exception Handling *)

Axiom exit_observer: Type.
Extract Constant exit_observer => "((unit -> unit) ref)".

Axiom new_exit_observer: (unit -> ??unit) -> ??exit_observer.
Extract Constant new_exit_observer => "ImpIOOracles.new_exit_observer".

Axiom set_exit_observer: exit_observer * (unit -> ??unit) -> ??unit.
Extract Constant set_exit_observer => "ImpIOOracles.set_exit_observer".

Axiom exn: Type.
Extract Inlined Constant exn => "exn".

Axiom raise: forall {A}, exn -> ?? A.
Extract Constant raise => "raise".

Axiom exn2string: exn -> ?? pstring.
Extract Constant exn2string => "ImpIOOracles.exn2string".

Axiom fail: forall {A}, pstring -> ?? A.
Extract Constant fail => "ImpIOOracles.fail".

Axiom try_with_fail: forall {A}, (unit -> ?? A) * (pstring -> exn -> ??A) -> ??A.
Extract Constant try_with_fail => "ImpIOOracles.try_with_fail".

Axiom try_with_any: forall {A}, (unit -> ?? A) * (exn -> ??A) -> ??A.
Extract Constant try_with_any => "ImpIOOracles.try_with_any".

Notation "'RAISE' e" := (DO r <~ raise (A:=False) e ;; RET (match r with end)) (at level 0): impure_scope.
Notation "'FAILWITH' msg" := (DO r <~ fail (A:=False) msg ;; RET (match r with end)) (at level 0): impure_scope.

Notation "'TRY' k1 'WITH_FAIL' s ',' e '=>' k2" := (try_with_fail (fun _ => k1, fun s e => k2))
    (at level 55, k1 at level 53, right associativity): impure_scope.

Notation "'TRY' k1 'WITH_ANY' e '=>' k2" := (try_with_any (fun _ => k1, fun e => k2))
    (at level 55, k1 at level 53, right associativity): impure_scope.

Program Definition assert_b (b: bool) (msg: pstring): ?? b=true :=
  match b with
  | true => RET _
  | false => FAILWITH msg
  end.

Lemma assert_wlp_true msg b: WHEN assert_b b msg ~> _ THEN b=true.
Proof.
  wlp_simplify.
Qed.

Lemma assert_false_wlp msg (P: Prop): WHEN assert_b false msg ~> _ THEN P.
Proof.
  simpl; wlp_simplify.
Qed.

Program Definition try_with_fail_ensure {A} (k1: unit -> ?? A) (k2: pstring -> exn -> ??A) (P: A -> Prop | wlp (k1 tt) P /\ (forall s e, wlp (k2 s e) P)): ?? { r | P r }
  := TRY
        DO r <~ callproof (k1 tt);; 
        RET (exist P r _)
     WITH_FAIL s, e => 
        DO r <~ callproof (k2 s e);;
        RET (exist P r _).
Obligation 2.
  unfold wlp in * |- *; eauto.
Qed.

Notation "'TRY' k1 'OR_FAIL' s ',' e '=>' k2 'ENSURE' P" := (try_with_fail_ensure (fun _ => k1) (fun s e => k2) (exist _ P _))
    (at level 55, k1 at level 53, right associativity): impure_scope.