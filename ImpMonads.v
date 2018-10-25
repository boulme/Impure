(** Impure monad for interface with impure code

*)

Require Export Setoid.
Require Export Relation_Definitions.
Require Export Morphisms.


Module Type MayReturnMonad.

  Axiom t: Type -> Type.

  Axiom mayRet: forall {A:Type}, t A -> A -> Prop.

  Axiom ret: forall {A}, A -> t A.

  Axiom bind: forall {A B}, (t A) -> (A -> t B) -> t B.

  Axiom mk_annot: forall {A} (k: t A), t { a: A | mayRet k a }.

  Axiom mayRet_ret: forall A (a b:A), 
     mayRet (ret a) b -> a=b.

  Axiom mayRet_bind: forall A B k1 k2 (b:B),
     mayRet (bind k1 k2) b -> exists a:A, mayRet k1 a /\ mayRet (k2 a) b.


 (* Observational Equivalence *)
 
  Axiom impeq: forall {A}, t A -> t A -> Prop.

  Declare Instance impeq_equiv A: Equivalence (@impeq A).
  Declare Instance mayRet_eq_compat A: Proper ((@impeq A) ==> Logic.eq ==> iff) (@mayRet A).
  Declare Instance bind_eq_compat A B: Proper ((@impeq A) ==> (pointwise_relation A (@impeq B)) ==> (@impeq B)) (@bind A B).

  Axiom impeq_bind_ret_l: forall (A B:Type) (k: A -> t B) (a:A),
     (impeq (bind (ret a) k) (k a)).

  Axiom impeq_bind_ret_r: forall (A:Type) (k: t A),
     (impeq (bind k (fun b => ret b)) k).

  Axiom impeq_bind_assoc: forall (A B C:Type) (k1: t A) (k2: A -> t B) (k3: B -> t C),
     (impeq (bind (bind k1 k2) (fun b => k3 b)) (bind k1 (fun a => bind (k2 a) (fun b => k3 b)))).

  Axiom impeq_bind_mk_annot: forall (A:Type) (k: t A),
     (impeq (bind (mk_annot k) (fun a => ret (proj1_sig a))) k).

End MayReturnMonad.



(** Model of impure computation as predicate *)
Module PowerSetMonad<: MayReturnMonad.
 
   Definition t (A:Type) := A -> Prop.

   Definition mayRet {A:Type} (k: t A) a: Prop := k a.

   Definition ret {A:Type} (a:A) := eq a.

   Definition bind {A B:Type} (k1: t A) (k2: A -> t B) := 
     fun b => exists a, k1 a /\ k2 a b.

   Definition mk_annot {A} (k: t A) : t { a | mayRet k a } := fun _ => True.

   Lemma mayRet_ret A (a b:A): mayRet (ret a) b -> a=b.
   Proof.
     unfold mayRet, ret. firstorder.
   Qed.

   Lemma mayRet_bind A B k1 k2 (b:B):
         mayRet (bind k1 k2) b -> exists (a:A), mayRet k1 a /\ mayRet (k2 a) b.
   Proof.
     unfold mayRet, bind. 
     firstorder.
   Qed.

   Definition impeq {A} (k1 k2: t A) := forall a, (k1 a) <-> (k2 a).

   Instance impeq_equiv A: Equivalence (@impeq A).
   Proof.
     unfold impeq; constructor 1; intro k.
     - intuition.
     - firstorder.
     - intros y z H H0 a. rewrite H. auto.
   Qed.

   Instance mayRet_eq_compat A: Proper ((@impeq A) ==> Logic.eq ==> iff) (@mayRet A).
   Proof.
     unfold impeq; intros k1 k2 H x y H0.
     subst; firstorder.
   Qed.

   Instance bind_eq_compat A B: Proper ((@impeq A) ==> (pointwise_relation A (@impeq B)) ==> (@impeq B)) (@bind A B).
   Proof.
    unfold impeq, pointwise_relation, bind; intros x y H f g H0 a.
    firstorder.
   Qed.

   Lemma impeq_bind_ret_l: forall (A B:Type) (k: A -> t B) (a:A), (impeq (bind (ret a) k) (k a)).
   Proof.
     unfold impeq, bind, ret; firstorder (subst; auto).
   Qed.

   Lemma impeq_bind_ret_r: forall (A:Type) (k: t A), (impeq (bind k (fun b => ret b)) k).
   Proof.
     unfold impeq, bind, ret; firstorder (subst; auto).
   Qed.

   Lemma impeq_bind_assoc: forall (A B C:Type) (k1: t A) (k2: A -> t B) (k3: B -> t C),
     (impeq (bind (bind k1 k2) (fun b => k3 b)) (bind k1 (fun a => bind (k2 a) (fun b => k3 b)))).
   Proof.
     unfold impeq, bind, ret; firstorder (subst; auto).
   Qed.

   Lemma impeq_bind_mk_annot: forall (A:Type) (k: t A),
     (impeq (bind (mk_annot k) (fun a => ret (proj1_sig a))) k).
   Proof.
     unfold impeq, bind, ret, mk_annot, mayRet. intros A k a; constructor 1.
     - intros [[x H] [H0 H1]]. subst; simpl; auto.
     - intros. constructor 1 with (x:=(exist _ _ H)). simpl; intuition.
   Qed.

End PowerSetMonad.


(** The identity interpretation *)
Module IdentityMonad<: MayReturnMonad.

   Definition t (A:Type) := A.

   (* may-return semantics of computations *)
   Definition mayRet {A:Type} (a b:A): Prop := a=b.

   Definition ret {A:Type} (a:A) := a.

   Definition bind {A B:Type} (k1: A) (k2: A -> B) := k2 k1.

   Definition mk_annot {A} (k: t A) : t { a: A | mayRet k a } 
    := exist _ k (eq_refl k) .

   Lemma mayRet_ret (A:Type) (a b:A): mayRet (ret a) b -> a=b.
   Proof.
     intuition.
   Qed.

   Lemma mayRet_bind (A B:Type) (k1:t A) k2 (b:B):
         mayRet (bind k1 k2) b -> exists (a:A), mayRet k1 a /\ mayRet (k2 a) b.
   Proof.
     firstorder.
   Qed.

   Definition impeq {A} (k1 k2: t A) := k1=k2.

   Instance impeq_equiv A: Equivalence (@impeq A).
   Proof.
     unfold impeq; constructor 1; intro k.
     - intuition.
     - firstorder.
     - intros; subst; auto.
   Qed.

   Instance mayRet_eq_compat A: Proper ((@impeq A) ==> Logic.eq ==> iff) (@mayRet A).
   Proof.
     unfold impeq; intros k1 k2 H x y H0.
     subst; firstorder.
   Qed.

   Instance bind_eq_compat A B: Proper ((@impeq A) ==> (pointwise_relation A (@impeq B)) ==> (@impeq B)) (@bind A B).
   Proof.
    unfold impeq, pointwise_relation, bind; intros x y H f g H0.
    subst; firstorder.
   Qed.

   Lemma impeq_bind_ret_l: forall (A B:Type) (k: A -> t B) (a:A), (impeq (bind (ret a) k) (k a)).
   Proof.
     unfold impeq, bind, ret; firstorder (subst; auto).
   Qed.

   Lemma impeq_bind_ret_r: forall (A:Type) (k: t A), (impeq (bind k (fun b => ret b)) k).
   Proof.
     unfold impeq, bind, ret; firstorder (subst; auto).
   Qed.

   Lemma impeq_bind_assoc: forall (A B C:Type) (k1: t A) (k2: A -> t B) (k3: B -> t C),
     (impeq (bind (bind k1 k2) (fun b => k3 b)) (bind k1 (fun a => bind (k2 a) (fun b => k3 b)))).
   Proof.
     unfold impeq, bind, ret; firstorder (subst; auto).
   Qed.

   Lemma impeq_bind_mk_annot: forall (A:Type) (k: t A),
     (impeq (bind (mk_annot k) (fun a => ret (proj1_sig a))) k).
   Proof.
     unfold impeq, bind, ret, mk_annot, mayRet. simpl. auto.
   Qed.

End IdentityMonad.


(** Model of impure computation as state-transformers *)
Module StateMonad<: MayReturnMonad.
 
   Parameter St: Type. (* A global state *)

   Definition t (A:Type) := St -> A * St.

   Definition mayRet {A:Type} (k: t A) a: Prop :=
     exists s, fst (k s)=a.

   Definition ret {A:Type} (a:A) := fun (s:St) => (a,s).

   Definition bind {A B:Type} (k1: t A) (k2: A -> t B) := 
     fun s0 => let r := k1 s0 in k2 (fst r) (snd r).

   Program Definition mk_annot {A} (k: t A) : t { a | mayRet k a } := 
     fun s0 => let r := k s0 in (exist _ (fst r) _, snd r).
   Obligation 1.
     unfold mayRet; eauto.
   Qed.

   Lemma mayRet_ret {A:Type} (a b:A): mayRet (ret a) b -> a=b.
   Proof.
     unfold mayRet, ret. firstorder.
   Qed.

   Lemma mayRet_bind {A B:Type} k1 k2 (b:B):
         mayRet (bind k1 k2) b -> exists (a:A), mayRet k1 a /\ mayRet (k2 a) b.
   Proof.
     unfold mayRet, bind. firstorder eauto.
   Qed. 

   Definition impeq {A} (k1 k2: t A) := forall s, k1 s=k2 s.

   Instance impeq_equiv A: Equivalence (@impeq A).
   Proof.
     unfold impeq; constructor 1; intro k.
     - intuition.
     - firstorder.
     - intros; subst; congruence.
   Qed.

   Instance mayRet_eq_compat A: Proper ((@impeq A) ==> Logic.eq ==> iff) (@mayRet A).
   Proof.
     unfold impeq, mayRet; intros k1 k2 H x y H0.
     subst. constructor 1; intros [s H0].
     rewrite (H s) in H0; eauto.
     rewrite <- (H s) in H0; eauto.
   Qed.

   Instance bind_eq_compat A B: Proper ((@impeq A) ==> (pointwise_relation A (@impeq B)) ==> (@impeq B)) (@bind A B).
   Proof.
    unfold impeq, pointwise_relation, bind; intros x y H f g H0.
    intros; congruence.
   Qed.

   Lemma impeq_bind_ret_l: forall (A B:Type) (k: A -> t B) (a:A), (impeq (bind (ret a) k) (k a)).
   Proof.
     unfold impeq, bind, ret. simpl; auto. 
   Qed.

   Lemma impeq_bind_ret_r: forall (A:Type) (k: t A), (impeq (bind k (fun b => ret b)) k).
   Proof.
     unfold impeq, bind, ret. intros A k s; destruct k; simpl; auto.
   Qed.

   Lemma impeq_bind_assoc: forall (A B C:Type) (k1: t A) (k2: A -> t B) (k3: B -> t C),
     (impeq (bind (bind k1 k2) (fun b => k3 b)) (bind k1 (fun a => bind (k2 a) (fun b => k3 b)))).
   Proof.
     unfold impeq, bind, ret. auto.
   Qed.

   Lemma impeq_bind_mk_annot: forall (A:Type) (k: t A),
     (impeq (bind (mk_annot k) (fun a => ret (proj1_sig a))) k).
   Proof.
     unfold impeq, bind, ret, mk_annot, mayRet.  simpl. intros A k s; destruct k; simpl; auto.
   Qed.

End StateMonad.