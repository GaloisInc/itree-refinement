
From ITree Require Export ITree.
From Paco Require Import paco.
Require Export Refinement.


(** * Refinement lemmas *)

Lemma padded_refines_ret E1 E2 R1 R2 RE REAns RR r1 r2 :
  (RR r1 r2 : Prop) ->
  @padded_refines E1 E2 R1 R2 RE REAns RR (Ret r1) (Ret r2).
Proof.
  intros Hr. red. repeat rewrite pad_ret. pstep. constructor. auto.
Qed.

Lemma padded_refines_vis E1 E2 R1 R2 A B 
        RE REAns RR (e1 : E1 A) (e2 : E2 B)
        (k1 : A -> itree_spec E1 R1) (k2 : B -> itree_spec E2 R2) : 
  (RE A B e1 e2 : Prop) -> 
  (forall a b, (REAns A B e1 e2 a b : Prop) -> padded_refines RE REAns RR (k1 a) (k2 b) ) ->
  padded_refines RE REAns RR (Vis (Spec_vis e1) k1) (Vis (Spec_vis e2) k2).
Proof.
  unfold padded_refines. setoid_rewrite pad_vis. intros.
  pstep. constructor; auto. intros. left. pstep. constructor.
  left. eapply H0; auto.
Qed.

Lemma padded_refines_if_l E1 E2 RE REAns R1 R2 RR (t1 t2 : itree_spec E1 R1) (t3 : itree_spec E2 R2) b :
  (b = true  -> padded_refines RE REAns RR t1 t3) ->
  (b = false -> padded_refines RE REAns RR t2 t3) ->
  padded_refines RE REAns RR (if b then t1 else t2) t3.
Proof.
  intros. destruct b; eauto.
Qed.

Lemma padded_refines_if_r E1 E2 RE REAns R1 R2 RR (t1 : itree_spec E1 R1) (t2 t3: itree_spec E2 R2) b :
  (b = true  -> padded_refines RE REAns RR t1 t2) ->
  (b = false -> padded_refines RE REAns RR t1 t3) ->
  padded_refines RE REAns RR t1 (if b then t2 else t3).
Proof.
  intros. destruct b; eauto.
Qed.
