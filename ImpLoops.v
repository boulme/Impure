(** Extension of Coq language with generic loops. *)

Require Export ImpIO.

Import Notations.
Local Open Scope impure.


(** While-loop iterations *)

Axiom loop: forall {A B}, A * (A -> ?? (A+B)) -> ?? B.
Extract Constant loop => "ImpLoopOracles.loop".


Section While_Loop.

(** Local Definition of "while-loop-invariant" *)
Let wli {S} cond body (I: S -> Prop) := forall s, I s -> cond s = true -> WHEN (body s) ~> s' THEN I s'.

Program Definition while {S} cond body (I: S -> Prop | wli cond body I) s0: ?? {s | (I s0 -> I s) /\ cond s = false}
  := loop (A:={s | I s0 -> I s})
       (s0, 
          fun s =>
          match (cond s) with
          | true => 
             DO s' <~ mk_annot (body s) ;; 
             RET (inl (A:={s | I s0 -> I s }) s')
          | false => 
             RET (inr (B:={s | (I s0 -> I s) /\ cond s = false}) s)
          end).
Obligation 2.
  unfold wli, wlp in * |-; eauto.
Qed.
Extraction Inline while.

End While_Loop.


Section Loop_Until_None.
(** useful to demonstrate a UNSAT property *)

(** Local Definition of "loop-until-None-invariant" *)
Let luni {S} (body: S -> ?? (option S)) (I: S -> Prop) := forall s, I s -> WHEN (body s) ~> s' THEN match s' with Some s1 => I s1 | None => False end.

Program Definition loop_until_None {S} body (I: S -> Prop | luni body I) s0: ?? ~(I s0)
  := loop (A:={s | I s0 -> I s})
       (s0, 
          fun s =>
          DO s' <~ mk_annot (body s) ;;
          match s' with
          | Some s1 => RET (inl (A:={s | I s0 -> I s }) s1)
          | None => RET (inr (B:=~(I s0)) _)
          end).
Obligation 2.
  refine (H2 s _ _ H0). auto.
Qed.
Obligation 3.
  intros X; refine (H1 s _ _ H). auto.
Qed.
Extraction Inline loop_until_None.

End Loop_Until_None.


(*********************************************)
(* A generic fixpoint from an equality test  *)

Record answ {A B: Type} {R: A -> B -> Prop} := {
  input: A ;
  output: B ;
  correct: R input output
}.
Arguments answ {A B}.

Definition msg: pstring := "wapply fails".

Definition beq_correct {A} (beq: A -> A -> ?? bool) :=
  forall x y, WHEN beq x y ~> b THEN b=true -> x=y.

Definition wapply {A B} {R: A -> B -> Prop} (beq: A -> A -> ?? bool) (k: A -> ?? answ R) (x:A): ?? B :=
  DO a <~ k x;;
  DO b <~ beq x (input a) ;;
  assert_b b msg;;
  RET (output a).

Lemma wapply_correct A B (R: A -> B -> Prop) (beq: A -> A -> ?? bool) (k: A -> ?? answ R) x:
 beq_correct beq
 -> WHEN wapply beq k x ~> y THEN R x y.
Proof.
  unfold beq_correct; wlp_simplify.
  destruct exta; simpl; auto.
Qed.
Local Hint Resolve wapply_correct: wlp.
Global Opaque wapply.

Axiom xrec_set_option: recMode -> ?? unit.
Extract Constant xrec_set_option => "ImpLoopOracles.xrec_set_option".

(* TODO: generalizaton to get beq (and a Hash function ?) in parameters ? *)
Axiom xrec: forall {A B}, ((A -> ?? B) -> A -> ?? B) -> ?? (A -> ?? B).
Extract Constant xrec => "ImpLoopOracles.xrec".

Definition rec_preserv {A B} (recF: (A -> ?? B) -> A -> ?? B) (R: A -> B -> Prop) :=
  forall f x, WHEN recF f x ~> z THEN (forall x', WHEN f x' ~> y THEN R x' y) -> R x z.


Program Definition rec {A B} beq recF (R: A -> B -> Prop) (H1: rec_preserv recF R) (H2: beq_correct beq): ?? (A -> ?? B) :=
  DO f <~ xrec (B:=answ R) (fun f x =>
         DO y <~ mk_annot (recF (wapply beq f) x) ;;
         RET {| input := x; output := `y |});;
  RET (wapply beq f).
Obligation 1.
  eapply H1; eauto. clear H H1.
  wlp_simplify.
Qed.

Lemma rec_correct A B beq recF (R: A -> B -> Prop) (H1: rec_preserv recF R) (H2: beq_correct beq): 
  WHEN rec beq recF R H1 H2 ~> f THEN forall x, WHEN f x ~> y THEN R x y.
Proof.
  wlp_simplify.
Qed.
Hint Resolve rec_correct: wlp.
Global Opaque rec.
