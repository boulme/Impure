Require Export String.
Require Export List.
Require Extraction.
Require Import Ascii.
Require Import BinNums.
Require Export ImpCore.
Require Export PArith.


Import Notations.
Local Open Scope impure.

(** Impure lazy andb of booleans *)
Definition iandb (k1 k2: ??bool): ?? bool :=
  DO r1 <~ k1 ;;
  if r1 then k2 else RET false.

Extraction Inline iandb. (* Juste pour l'efficacité à l'extraction ! *)

(** Strings for pretty-printing *)

Axiom caml_string: Type.
Extract Constant caml_string => "string".

(* New line *)
Definition nl: string := String (ascii_of_pos 10%positive) EmptyString.

Inductive pstring: Type :=
  | Str: string -> pstring
  | CamlStr: caml_string -> pstring
  | Concat: pstring -> pstring -> pstring.

Coercion Str: string >-> pstring.
Bind Scope string_scope with pstring.

Notation "x +; y" := (Concat x y)
    (at level 65, left associativity): string_scope.

(** Coq references *)

Record cref {A} := {
  set: A -> ?? unit;
  get: unit -> ?? A
}.
Arguments cref: clear implicits.

Axiom make_cref: forall {A}, A -> ?? cref A.
Extract Constant make_cref => "(fun x -> let r = ref x in { set = (fun y -> r:=y); get = (fun () -> !r) })".


(** Data-structure for a logger *)

Record logger {A:Type} := {
  log_insert: A -> ?? unit;
  log_info: unit -> ?? pstring;
}.
Arguments logger: clear implicits.

Axiom count_logger: unit -> ?? logger unit.
Extract Constant count_logger => "(fun () -> let count = ref 0 in { log_insert = (fun () -> count := !count + 1); log_info = (fun () -> (CamlStr (string_of_int !count))) })".


(** Axioms of Physical equality  *)

Axiom phys_eq: forall {A}, A -> A -> ?? bool.

Axiom phys_eq_correct: forall A (x y:A), WHEN phys_eq x y ~> b THEN b=true -> x=y.


(* We only check here that above axioms are not trivially inconsistent...
   (but this does not prove the correctness of the extraction directive below).
 *)
Module PhysEqModel.

Definition phys_eq {A} (x y: A) := ret false.

Lemma phys_eq_correct: forall A (x y:A), WHEN phys_eq x y ~> b THEN b=true -> x=y.
Proof.
  wlp_simplify. discriminate.
Qed.

End PhysEqModel.

Extract Inlined Constant phys_eq => "(==)".
Hint Resolve phys_eq_correct: wlp.


Axiom struct_eq: forall {A}, A -> A -> ?? bool.
Axiom struct_eq_correct: forall A (x y:A), WHEN struct_eq x y ~> b THEN if b then x=y else x<>y.
Extract Inlined Constant struct_eq => "(=)".
Hint Resolve struct_eq_correct: wlp.


(** Data-structure for generic hash-consing *)

Axiom hashcode: Type.
Extract Constant hashcode => "int".

(* NB: hashConsing is assumed to generate hash-code in ascending order.
   This gives a way to check that a hash-consed value is older than an other one.
*)
Axiom hash_older: hashcode -> hashcode -> ?? bool.
Extract Inlined Constant hash_older => "(<)".

Module Dict.

Record hash_params {A:Type} := {
  test_eq: A -> A -> ??bool;
  test_eq_correct: forall x y, WHEN test_eq x y ~> r THEN r=true -> x=y;
  hashing: A -> ??hashcode;
  log: A -> ??unit (* for debugging only *)
}.
Arguments hash_params: clear implicits.


Record t {A B:Type} := {
  set: A * B -> ?? unit;
  get: A -> ?? option B
}.
Arguments t: clear implicits.

End Dict.

Module HConsingDefs.

Record hashinfo {A: Type} := {
  hdata: A;
  hcodes: list hashcode;
}.
Arguments hashinfo: clear implicits.

(* for inductive types with intrinsic hash-consing *)
Record hashP {A:Type}:= {
  hash_eq: A -> A -> ?? bool;
  get_hid: A -> hashcode;
  set_hid: A -> hashcode -> A; (* WARNING: should only be used by hash-consing machinery *)
}.
Arguments hashP: clear implicits.

Axiom unknown_hid: hashcode.
Extract Constant unknown_hid => "-1".

Definition ignore_hid {A} (hp: hashP A) (hv:A) := set_hid hp hv unknown_hid.

Record hashExport {A:Type}:= {
  get_info: hashcode -> ?? hashinfo A;
  iterall: ((list pstring) -> hashcode -> hashinfo A -> ?? unit) -> ?? unit; (* iter on all elements in the hashtbl, by order of creation *)
}.
Arguments hashExport: clear implicits.

Record hashConsing {A:Type}:= {
  hC: hashinfo A -> ?? A;
  (**** below: debugging or internal functions ****)
  next_hid: unit -> ?? hashcode; (* should be strictly less old than ignore_hid *)
  remove: hashinfo A -> ??unit; (* SHOULD NOT BE USED ! *)
  next_log: pstring -> ?? unit; (* insert a log info (for the next introduced element) -- regiven by [iterall export] below *)
  export: unit -> ?? hashExport A ; 
}.
Arguments hashConsing: clear implicits.

End HConsingDefs.

(** recMode: this is mainly for Tests ! *)
Inductive recMode:= StdRec | MemoRec | BareRec | BuggyRec.


(* This a copy-paste from definitions in CompCert/Lib/CoqLib.v *)
Lemma modusponens: forall (P Q: Prop), P -> (P -> Q) -> Q.
Proof. auto. Qed.

Ltac exploit x :=
    refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _) _)
 || refine (modusponens _ _ (x _ _) _)
 || refine (modusponens _ _ (x _) _).
