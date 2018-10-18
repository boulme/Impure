(** Impure monad for interface with impure code

*)

Require Export Program.
Require Export ImpConfig.

(* Theory: bind + embed => dbind 

Program Definition dbind {A B} (k1: t A) (k2: forall (a:A), (mayRet k1 a) -> t B) : t B
  := bind (callproof k1) (fun a => k2 a _).

Lemma mayRet_dbind: forall (A B:Type) k1 k2 (b:B),
     mayRet (dbind k1 k2) b -> exists a:A, exists H: (mayRet k1 a), mayRet (k2 a H) b.
Proof.
  intros A B k1 k2 b H; decompose [ex and] (mayRet_bind _ _ _ _ _ H).
  eapply ex_intro.
  eapply ex_intro.
  eauto.
Qed.

*)

Definition wlp {A:Type} (k: t A) (P: A -> Prop): Prop
  := forall a, mayRet k a -> P a.

(* Notations *)

(* Print Grammar constr. *)

Module Notations.

  Bind Scope impure_scope with t.
  Delimit Scope impure_scope with impure.

  Notation "?? A" := (t A) (at level 0, A at level 95): impure_scope.

  Notation "k '~~>' a" := (mayRet k a) (at level 75, no associativity): impure_scope. 

  Notation "'RET' a" := (ret a) (at level 0): impure_scope.

  Notation "'DO' x '<~' k1 ';;' k2" := (bind k1 (fun x => k2))
    (at level 55, k1 at level 53, x at level 99, right associativity): impure_scope.

  Notation "k1 ';;'  k2" := (bind k1 (fun _ => k2))
    (at level 55, right associativity): impure_scope.

  Notation "'WHEN' k '~>' a 'THEN' R" := (wlp k (fun a => R))
    (at level 73, R at level 100, right associativity): impure_scope.

  Notation "'ASSERT' P" := (ret (A:=P) _) (at level 0, only parsing): impure_scope.

End Notations.

Import Notations.
Local Open Scope impure.

Goal ((?? list nat * ??nat -> nat) = ((?? ((list nat) * ?? nat) -> nat)))%type.
Proof.
  apply refl_equal.
Qed.


(* wlp lemmas for tactics *)

Lemma wlp_unfold A (k:??A)(P: A -> Prop):
   (forall a, k ~~> a -> P a)
    -> wlp k P.
Proof.
  auto.
Qed.

Lemma wlp_monotone A (k:?? A) (P1 P2: A -> Prop):
    wlp k P1
    -> (forall a, k ~~> a -> P1 a -> P2 a)
    -> wlp k P2.
Proof.
  unfold wlp; eauto.
Qed.

Lemma wlp_forall A B (k:?? A) (P: B -> A -> Prop):
   (forall x, wlp k (P x))
    -> wlp k (fun a => forall x, P x a).
Proof.
  unfold wlp; auto.
Qed.

Lemma wlp_ret A (P: A -> Prop) a:
   P a -> wlp (ret a) P.
Proof.
    unfold wlp.
    intros H b H0.
    rewrite <- (mayRet_ret _ a b H0).
    auto.
Qed.

Lemma wlp_bind A B (k1:??A) (k2: A -> ??B) (P: B -> Prop):
  wlp k1 (fun a => wlp (k2 a) P) -> wlp (bind k1 k2) P.
Proof.
    unfold wlp.
    intros H a H0.
    case (mayRet_bind _ _ _ _ _ H0); clear H0.
    intuition eauto.
Qed.

Lemma wlp_ifbool A (cond: bool) (k1 k2: ?? A) (P: A -> Prop):
 (cond=true -> wlp k1 P) -> (cond=false -> wlp k2 P) -> wlp (if cond then k1 else k2) P.
Proof.
  destruct cond; auto.
Qed.

Lemma wlp_letprod (A B C: Type) (p: A*B) (k: A -> B -> ??C) (P: C -> Prop):
  (wlp (k (fst p) (snd p)) P)
    -> (wlp (let (x,y):=p in (k x y)) P).
Proof.
  destruct p; simpl; auto.
Qed.

Lemma wlp_sum (A B C: Type) (x: A+B) (k1: A -> ??C) (k2: B -> ??C)  (P: C -> Prop):
  (forall a, x=inl a -> wlp (k1 a) P) -> 
  (forall b, x=inr b -> wlp (k2 b) P) -> 
     (wlp (match x with inl a => k1 a | inr b => k2 b end) P).
Proof.
  destruct x; simpl; auto.
Qed.

Lemma wlp_sumbool (A B:Prop) (C: Type) (x: {A}+{B}) (k1: A -> ??C) (k2: B -> ??C)  (P: C -> Prop):
  (forall a, x=left a -> wlp (k1 a) P) -> 
  (forall b, x=right b -> wlp (k2 b) P) -> 
     (wlp (match x with left a => k1 a | right b => k2 b end) P).
Proof.
  destruct x; simpl; auto.
Qed.

(* Tactics 

MAIN tactics:  
  - xtsimplify "base": simplification using from hints in "base" database (in particular "wlp" lemmas).
  - xtstep "base": only one step of simplification.

For good performance, it is recommanded to have several databases.

*)

Ltac introcomp :=
  let a:= fresh "exta" in
  let H:= fresh "Hexta" in
  intros a H.

(* decompose the current wlp goal using "introduction" rules *)
Ltac wlp_decompose :=
    apply wlp_ret
 || apply wlp_bind
 || apply wlp_ifbool
 || apply wlp_letprod
 || apply wlp_sum
 || apply wlp_sumbool
 .

(* this tactic simplifies the current "wlp" goal using any hint found via tactic "hint". *) 
Ltac apply_wlp_hint hint :=
    eapply wlp_monotone;
      [ hint; fail | idtac ] ;
      simpl; introcomp.

(* one step of wlp_xsimplify 
*)
Ltac wlp_step hint :=
    match goal with
      | |- (wlp _ _) => 
        wlp_decompose
        || apply_wlp_hint hint
        || (apply wlp_unfold; introcomp)
    end.

(* main general tactic 
WARNING: for the good behavior of "wlp_xsimplify", "hint" must at least perform a "eauto".

Example of use:
  wlp_xsimplify (intuition eauto with base).
*)
Ltac wlp_xsimplify hint := 
    repeat (intros; subst; wlp_step hint; simpl; (tauto || hint)).

Create HintDb wlp discriminated.

Ltac wlp_simplify := wlp_xsimplify ltac:(intuition eauto with wlp).


(*** Observational equivalence ***)

Require Export Setoid.
Require Export Relation_Definitions.
Require Export Morphisms.

Hint Rewrite @impeq_bind_ret_l @impeq_bind_ret_r @impeq_bind_assoc: impeq.
Hint Immediate (fun A x => @Equivalence_Reflexive _ _ (@impeq_equiv A) x).

Add Parametric Morphism (A:Type): (@wlp A) with
    signature (@impeq A) ==> (pointwise_relation A iff) ==> iff
    as wlp_compat.
Proof.
    intros k1 k2 H P Q H0. unfold pointwise_relation, iff in H.
    constructor 1; unfold wlp; intros.
    rewrite <- H in * |- ; firstorder.
    rewrite H in * |-; firstorder.
Qed.

Lemma List_fold_left_impeq_run (A B:Type) (f: B -> A -> ?? A) (l:list B) (i: ?? A):
   impeq (List.fold_left (fun k x => bind k (f x)) l i)
         (bind i (fun a => List.fold_left (fun k x => bind k (f x)) l (ret a))).
Proof.
    simpl. 
    generalize i.
    induction l as [| a0 l IHl]; simpl.
    - intros; autorewrite with impeq; auto.
    - intros; rewrite IHl.
      autorewrite with impeq.
      apply bind_eq_compat. 
      + auto.
      + intros a. rewrite IHl; auto;
           autorewrite with impeq; auto.  
Qed.

Lemma wlp_List_fold_left (A B:Type) (f: B -> A -> ?? A) (l:list B) (i: ?? A) (P: A -> Prop): 
    wlp i (fun a => wlp (List.fold_left (fun k x => bind k (f x)) l (ret a)) P)
     -> wlp (List.fold_left (fun k x => bind k (f x)) l i) P.
Proof.
  intros H; rewrite List_fold_left_impeq_run.
  apply wlp_bind. auto.
Qed.

Lemma impeq_seq_ret_tt_r (k: ?? unit): impeq (k;;RET()) k.
Proof.
  eapply Equivalence_Transitive. 2: apply impeq_bind_ret_r.
  eapply bind_eq_compat; eauto.
  intro x. destruct x; auto.
Qed.

Hint Rewrite impeq_seq_ret_tt_r: impeq.