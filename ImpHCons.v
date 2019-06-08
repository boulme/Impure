Require Export ImpIO.

Import Notations.
Local Open Scope impure.


Axiom string_of_hashcode: hashcode -> ?? caml_string.
Extract Constant string_of_hashcode => "string_of_int".

Axiom hash: forall {A}, A -> ?? hashcode.
Extract Constant hash => "Hashtbl.hash".

(**************************)
(* (Weak) Sets            *)


Import Dict.

Axiom make_dict: forall {A B}, (hash_params A) -> ?? Dict.t A B.
Extract Constant make_dict => "ImpHConsOracles.make_dict".


Module Sets.

Definition t {A} (mod: A -> Prop) := Dict.t A {x | mod x}.

Definition empty {A} (hp: hash_params A) {mod:A -> Prop}: ?? t mod :=
  make_dict hp.

Program Fixpoint add {A} (l: list A) {mod: A -> Prop} (d: t mod): forall {H:forall x, List.In x l -> mod x}, ?? unit :=
  match l with
  | nil => fun H => RET ()
  | x::l' => fun H =>
    d.(set)(x,x);;
    add l' d
  end.

Program Definition create {A} (hp: hash_params A) (l:list A): ?? t (fun x => List.In x l) :=
  DO d <~ empty hp (mod:=fun x => List.In x l);;
  add l (mod:=fun x => List.In x l) d (H:=_);;
  RET d.
Global Opaque create.

Definition is_present {A} (hp: hash_params A) (x:A) {mod} (d:t mod): ?? bool :=
  DO oy <~ (d.(get)) x;;
  match oy with
  | Some y => hp.(test_eq) x (`y)
  | None => RET false
  end.

Local Hint Resolve test_eq_correct: wlp.

Lemma is_present_correct A (hp: hash_params A) x mod (d:t mod):
 WHEN is_present hp x d ~> b THEN b=true -> mod x.
Proof.
  wlp_simplify; subst; eauto.
  - apply proj2_sig.
  - discriminate. 
Qed.
Hint Resolve is_present_correct: wlp.
Global Opaque is_present.

Definition msg_assert_incl: pstring := "Sets.assert_incl".

Fixpoint assert_incl {A} (hp: hash_params A) (l: list A) {mod} (d:t mod): ?? unit :=
  match l with
  | nil => RET ()
  | x::l' =>
    DO b <~ is_present hp x d;;
    if b then
      assert_incl hp l' d
    else (
      hp.(log) x;;
      FAILWITH msg_assert_incl
    )
  end.

Lemma assert_incl_correct A (hp: hash_params A) l mod (d:t mod):
 WHEN assert_incl hp l d ~> _ THEN forall x, List.In x l -> mod x.
Proof.
  induction l; wlp_simplify; subst; eauto.
Qed.
Hint Resolve assert_incl_correct: wlp.
Global Opaque assert_incl.

Definition assert_list_incl {A} (hp: hash_params A) (l1 l2: list A): ?? unit :=
  (* println "";;print("dict_create ");;*)
  DO d <~ create hp l2;;
  (*print("assert_incl ");;*)
  assert_incl hp l1 d.

Lemma assert_list_incl_correct A (hp: hash_params A) l1 l2:
 WHEN assert_list_incl hp l1 l2 ~> _ THEN List.incl l1 l2.
Proof.
  wlp_simplify.
Qed.
Global Opaque assert_list_incl.
Hint Resolve assert_list_incl_correct.

End Sets.




(********************************)
(* (Weak) HConsing              *)

Module HConsing.

Export HConsingDefs.

(* NB: this axiom is NOT intended to be called directly, but only through [hCons...] functions below. *)
Axiom xhCons: forall {A}, (hashP A) -> ?? hashConsing A.
Extract Constant xhCons => "ImpHConsOracles.xhCons".

Definition hCons_eq_msg: pstring := "xhCons: hash eq differs".

Definition hCons {A} (hp: hashP A): ?? (hashConsing A) :=
  DO hco <~ xhCons hp ;;
  RET {|
      hC := (fun x =>
         DO x' <~ hC hco x ;;
         DO b0 <~ hash_eq hp x.(hdata) x' ;;
         assert_b b0 hCons_eq_msg;;
         RET x');
      next_hid := hco.(next_hid);
      next_log := hco.(next_log);
      export := hco.(export);
      remove := hco.(remove)
      |}.


Lemma hCons_correct A (hp: hashP A):
  WHEN hCons hp ~> hco THEN
    (forall x y, WHEN hp.(hash_eq) x y ~> b THEN b=true -> (ignore_hid hp x)=(ignore_hid hp y)) ->
    forall x, WHEN hco.(hC) x ~> x' THEN ignore_hid hp x.(hdata)=ignore_hid hp x'.
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

Definition hashV_C {A} (test_eq: A -> A -> ?? bool) : hashP (hashV A) := {|
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
