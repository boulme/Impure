Require Export ImpIO.

Import Notations.
Local Open Scope impure.

(********************************)
(* (Weak) HConsing              *)

Axiom string_of_hashcode: hashcode -> ?? caml_string.
Extract Constant string_of_hashcode => "string_of_int".

Axiom hash: forall {A}, A -> ?? hashcode.
Extract Constant hash => "Hashtbl.hash".



Module HConsing.

Export HConsingDefs.

(* NB: this axiom is NOT intended to be called directly, but only through [hCons...] functions below. *)
Axiom xhCons: forall {A}, (hashH A) -> ?? hashConsing A.
Extract Constant xhCons => "ImpHConsOracles.xhCons".

Definition hCons_eq_msg: pstring := "xhCons: hash eq differs".

Definition hCons {A} (hh: hashH A): ?? (hashConsing A) :=
  DO hco <~ xhCons hh ;;
  RET {|
      hC := (fun x =>
         DO x' <~ hC hco x ;;
         DO b0 <~ hash_eq hh x.(hdata) x' ;;
         assert_b b0 hCons_eq_msg;;
         RET x');
      next_hid := hco.(next_hid);
      next_log := hco.(next_log);
      export := hco.(export);
      remove := hco.(remove)
      |}.


Lemma hCons_correct A (hh: hashH A):
  WHEN hCons hh ~> hco THEN
    (forall x y, WHEN hh.(hash_eq) x y ~> b THEN b=true -> (ignore_hid hh x)=(ignore_hid hh y)) ->
    forall x, WHEN hco.(hC) x ~> x' THEN ignore_hid hh x.(hdata)=ignore_hid hh x'.
Proof.
  wlp_simplify.
Qed.
Global Opaque hCons.
Hint Resolve hCons_correct: wlp.



(* hashV: extending a given type with hash-consing *)
Record hashV {A:Type}:= {
  data: A;
  hid: hashcode
}.
Arguments hashV: clear implicits.

Definition hashV_C {A} (test_eq: A -> A -> ?? bool) : hashH (hashV A) := {|
  hash_eq := fun v1 v2 => test_eq v1.(data) v2.(data);
  get_hid := hid;
  set_hid := fun v id => {| data := v.(data); hid := id |}
|}.

Definition liftHV (x:nat) := {| data := x; hid := unknown_hid |}.

Definition hConsV {A} (hasheq: A -> A -> ?? bool): ?? (hashConsing (hashV A)) :=
  hCons (hashV_C hasheq).

Lemma hConsV_correct A (hasheq: A -> A -> ?? bool):
  WHEN hConsV hasheq ~> hco THEN
    (forall x y, WHEN hasheq x y ~> b THEN b=true -> x=y) -> 
    forall x, WHEN hco.(hC) x ~> x' THEN x.(hdata).(data)=x'.(data).
Proof.
  Local Hint Resolve f_equal2.
  wlp_simplify.
  exploit H; eauto.
  + wlp_simplify.
  + intros; congruence.
Qed.
Global Opaque hConsV.
Hint Resolve hConsV_correct: wlp.

Definition hC_known {A} (hco:hashConsing (hashV A)) (unknownHash_msg: hashinfo (hashV A) -> ?? pstring) (x:hashinfo (hashV A)): ?? hashV A :=
  DO clock <~ hco.(next_hid)();;
  DO x' <~ hco.(hC) x;;
  DO ok <~ hash_older x'.(hid) clock;;
  if ok 
  then RET x'
  else
    hco.(remove) x;; 
    DO msg <~ unknownHash_msg x;;
    FAILWITH msg.

Lemma hC_known_correct A (hco:hashConsing (hashV A)) msg x:
  WHEN hC_known hco msg x ~> x' THEN
    (forall x, WHEN hco.(hC) x ~> x' THEN x.(hdata).(data)=x'.(data)) ->
    x.(hdata).(data)=x'.(data).
Proof.
  wlp_simplify.
  unfold wlp in * |- ; eauto.
Qed.
Global Opaque hC_known.
Hint Resolve hC_known_correct: wlp.

End HConsing.
