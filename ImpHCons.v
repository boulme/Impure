Require Export ImpIO.

Import Notations.
Local Open Scope impure.

(********************************)
(* (Weak) HConsing              *)

Axiom string_of_hashcode: hashcode -> ?? caml_string.
Extract Constant string_of_hashcode => "string_of_int".

Axiom hash: forall {A}, A -> ?? hashcode.
Extract Constant hash => "Hashtbl.hash".

Axiom xhCons: forall {A}, ((A -> A -> ?? bool) * (pre_hashV A -> ?? hashV A)) -> ?? hashConsing A.
Extract Constant xhCons => "ImpHConsOracles.xhCons".

Definition hCons_eq_msg: pstring := "xhCons: hash_eq differs".

Definition hCons {A} (hash_eq: A -> A -> ?? bool) (unknownHash_msg: pre_hashV A -> ?? pstring): ?? (hashConsing A) :=
  DO hco <~ xhCons (hash_eq, fun v => DO s <~ unknownHash_msg v ;; FAILWITH s) ;;
  RET {|
      hC := fun x => 
       DO x' <~ hC hco x ;;
       DO b0 <~ hash_eq (pre_data x) (data x') ;;
       assert_b b0 hCons_eq_msg;;
       RET x';
      hC_known := fun x => 
       DO x' <~ hC_known hco x ;;
       DO b0 <~ hash_eq (pre_data x) (data x') ;;
       assert_b b0 hCons_eq_msg;;
       RET x';
      next_log := next_log hco;
      export := export hco;
      |}.

Lemma hCons_correct: forall A (hash_eq: A -> A -> ?? bool) msg,
  WHEN hCons hash_eq msg ~> hco THEN
    ((forall x y, WHEN hash_eq x y ~> b THEN b=true -> x=y) -> forall x, WHEN hC hco x ~> x' THEN (pre_data x)=(data x'))
 /\ ((forall x y, WHEN hash_eq x y ~> b THEN b=true -> x=y) -> forall x, WHEN hC_known hco x ~> x' THEN (pre_data x)=(data x')).
Proof.
  wlp_simplify.
Qed.
Global Opaque hCons.
Hint Resolve hCons_correct: wlp.

Definition hCons_spec {A} (hco: hashConsing A) :=
  (forall x, WHEN hC hco x ~> x' THEN (pre_data x)=(data x')) /\ (forall x, WHEN hC_known hco x ~> x' THEN (pre_data x)=(data x')).
