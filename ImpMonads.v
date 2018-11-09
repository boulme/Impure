(** Impure monad for interface with impure code
*)


Require Import Program.


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

End StateMonad.

(** The deferred interpretation *)
Module DeferredMonad<: MayReturnMonad.

   Definition t (A:Type) := unit -> A.

   (* may-return semantics of computations *)
   Definition mayRet {A:Type} (a: t A) (b:A): Prop := a tt=b.

   Definition ret {A:Type} (a:A) : t A := fun _ => a.

   Definition bind {A B:Type} (k1: t A) (k2: A -> t B) : t B := fun _ => k2 (k1 tt) tt.

   Definition mk_annot {A} (k: t A) : t { a: A | mayRet k a } 
    := fun _ => exist _ (k tt) (eq_refl (k tt)).

   Lemma mayRet_ret (A:Type) (a b: A): mayRet (ret a) b -> a=b.
   Proof.
     intuition.
   Qed.

   Lemma mayRet_bind (A B:Type) (k1:t A) k2 (b:B):
         mayRet (bind k1 k2) b -> exists (a:A), mayRet k1 a /\ mayRet (k2 a) b.
   Proof.
     firstorder.
   Qed.

End DeferredMonad.
