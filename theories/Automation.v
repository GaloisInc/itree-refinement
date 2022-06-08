
From Coq Require Import ZArith.
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


(** * Hints *)

Create HintDb refines.

Hint Extern 999 (padded_refines _ _ _ _ _) => shelve : refines.

(** ** IntroArg *)

Inductive ArgName := Any | If.
Ltac argName n :=
  match n with
  | Any      => fresh "a"
  | If       => fresh "e_if"
  end.

Definition IntroArg (n : ArgName) A (goal : A -> Prop) := forall a, goal a.

Hint Opaque IntroArg : refines.

Lemma IntroArg_fold n A goal : forall a, IntroArg n A goal -> goal a.
Proof. intros a H; exact (H a). Qed.

(* Lemma IntroArg_unfold n A (goal : A -> Prop) : (forall a, goal a) -> IntroArg n A goal. *)
(* Proof. unfold IntroArg; intro H; exact H. Qed. *)

Ltac IntroArg_intro e := intro e.

Ltac IntroArg_forget := let e := fresh in intro e; clear e.

Ltac IntroArg_intro_dependent_destruction n :=
  let e := argName n in
    IntroArg_intro e; dependent destruction e.

Ltac IntroArg_base_tac n A g :=
  lazymatch A with
  | true  = true  => IntroArg_intro_dependent_destruction n
  | false = false => IntroArg_intro_dependent_destruction n
  | true  = false => IntroArg_intro_dependent_destruction n
  | false = true  => IntroArg_intro_dependent_destruction n
  end.

Hint Extern 1 (IntroArg ?n ?A ?g) => IntroArg_base_tac n A g : refines.

Ltac IntroArg_rewrite_bool_eq n :=
  let e := fresh in
    IntroArg_intro e; repeat rewrite e in *;
    apply (IntroArg_fold n _ _ e); clear e.

Hint Extern 2 (IntroArg ?n (@eq bool _ _) _) =>
  progress (IntroArg_rewrite_bool_eq n) : refines.

Hint Extern 5 (IntroArg ?n (?x = ?y) _) =>
  let e := argName n in IntroArg_intro e;
    try first [ is_var x; subst x | is_var y; subst y ] : refines.
Hint Extern 6 (IntroArg ?n _ _) =>
  let e := argName n in IntroArg_intro e : refines.

(** ** Main refinement rules *)

Definition padded_refines_if_l_IntroArg E1 E2 RE REAns R1 R2 RR t1 t2 t3 b :
  (IntroArg If (b = true) (fun _ => padded_refines RE REAns RR t1 t3)) ->
  (IntroArg If (b = false) (fun _ => padded_refines RE REAns RR t2 t3)) ->
  padded_refines RE REAns RR (if b then t1 else t2) t3 :=
  padded_refines_if_l E1 E2 RE REAns R1 R2 RR t1 t2 t3 b.
Definition padded_refines_if_r_IntroArg E1 E2 RE REAns R1 R2 RR t1 t2 t3 b :
  (IntroArg If (b = true) (fun _ => padded_refines RE REAns RR t1 t2)) ->
  (IntroArg If (b = false) (fun _ => padded_refines RE REAns RR t1 t3)) ->
  padded_refines RE REAns RR t1 (if b then t2 else t3) :=
  padded_refines_if_r E1 E2 RE REAns R1 R2 RR t1 t2 t3 b.

Hint Extern 1 (padded_refines _ _ _ (if _ then _ else _) _) =>
  apply padded_refines_if_l_IntroArg : refines.
Hint Extern 1 (padded_refines _ _ _ _ (if _ then _ else _)) =>
  apply padded_refines_if_r_IntroArg : refines.

Hint Extern 3 (padded_refines _ _ _ (Ret _) (Ret _)) =>
  apply padded_refines_ret; (reflexivity || shelve) : refines.


(** * Tactics *)

Ltac prove_refinement := unshelve (typeclasses eauto with refines).


(** * Examples *)

Open Scope Z_scope.

Lemma test E x :
  @padded_refines E E _ _ eqE eqEAns eq
                  (if x >=? 0 then if x <? 256 then Ret 1 else Ret 0 else Ret 0)
                  (if x <? 256 then if x >=? 0 then Ret 1 else Ret 0 else Ret 0).
Proof.
  prove_refinement.
Qed.
