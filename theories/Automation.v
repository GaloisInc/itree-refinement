
From Coq Require Import ZArith.
From ITree Require Export ITree.
From Paco Require Import paco.
Require Export Refinement.
Require Import Merge.


(** * Basic Refinement Lemmas *)

Lemma padded_refines_ret_lr E1 E2 R1 R2 RE REAns RR r1 r2 :
  (RR r1 r2 : Prop) ->
  @padded_refines E1 E2 R1 R2 RE REAns RR (Ret r1) (Ret r2).
Proof.
  intros Hr. red. repeat rewrite pad_ret. pstep. constructor. auto.
Qed.

Lemma padded_refines_vis_lr E1 E2 R1 R2 A B 
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

Lemma padded_refines_trigger_lr E1 E2 R1 R2
      RE REAns RR (e1 : E1 R1) (e2 : E2 R2) :
  (RE R1 R2 e1 e2 : Prop) ->
  (forall r1 r2, (REAns R1 R2 e1 e2 r1 r2: Prop) -> RR r1 r2 : Prop) ->
  padded_refines RE REAns RR (ITree.trigger (Spec_vis e1)) (ITree.trigger (Spec_vis e2)).
Proof.
  intros. apply padded_refines_vis_lr; eauto.
  intros. apply padded_refines_ret_lr; eauto.
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


(** * Refinement Lemmas About Recursion *)

Section Rec.

Context (E1 E2 : Type -> Type) (A1 A2 R1 R2 : Type).
Context (RE : relationEH E1 E2) (REAns : relationEAns E1 E2) (RR : R1 -> R2 -> Prop).

Context (precond : A1 -> A2 -> Prop)
        (postcond : A1 -> A2 -> forall r1 r2, RR r1 r2 -> Prop).

Variant padded_refines_rec_REInv : relationEH (callE A1 R1) (callE A2 R2) :=
  | padded_refines_rec_REInv_i a1 a2 : precond a1 a2 ->
    padded_refines_rec_REInv R1 R2 (Call a1) (Call a2).

Variant padded_refines_rec_REAnsInv : relationEAns (callE A1 R1) (callE A2 R2) :=
  | padded_refines_rec_REAnsInv_i a1 a2 r1 r2 : dep_prod_rel RR (postcond a1 a2) r1 r2 ->
    padded_refines_rec_REAnsInv R1 R2 (Call a1) (Call a2) r1 r2.

Context (body1 : A1 -> itree_spec (callE A1 R1 +' E1) R1)
        (body2 : A2 -> itree_spec (callE A2 R2 +' E2) R2).

Lemma padded_refines_rec_lr (a1 : A1) (a2 : A2) :
  precond a1 a2 ->
  (forall a1 a2, precond a1 a2 ->
     padded_refines (sum_relE padded_refines_rec_REInv RE)
                    (sum_relEAns padded_refines_rec_REAnsInv REAns)
                    (dep_prod_rel RR (postcond a1 a2))
                    (body1 a1) (body2 a2)) ->
  padded_refines RE REAns RR (mrec_spec (calling' body1) (Call a1))
                             (mrec_spec (calling' body2) (Call a2)).
Proof.
  intros.
  eapply padded_refines_monot with
    (RR1 := padded_refines_rec_REAnsInv R1 R2 (Call a1) (Call a2)); eauto.
  { intros. inv PR. destruct H7. inj_existT. subst. auto. }
  eapply padded_refines_mrec with (REInv := padded_refines_rec_REInv)
                                  (REAnsInv := padded_refines_rec_REAnsInv).
  - intros A B [] [] []. unfold calling'.
    eapply padded_refines_monot with (RR1 := dep_prod_rel RR (postcond a3 a4)); eauto.
    intros. constructor; eauto.
  - constructor; eauto.
Qed.

End Rec.


(** * Hint Database Definitions *)

Create HintDb refines.
Create HintDb prepostcond.

Hint Extern 999 (padded_refines _ _ _ _ _) => shelve : refines.

Definition Halt (goal : Type) := goal.
Definition RelGoal (goal : Prop) := goal.

Hint Opaque Halt : refines.
Hint Opaque RelGoal : refines.

Hint Extern 999 (Halt _) => unfold Halt; shelve : refines.
Hint Extern 999 (RelGoal _) =>
  unfold RelGoal; (reflexivity || shelve) : refines.


(** * IntroArg Definition and Hints *)

Inductive ArgName := Any | RetAny | Hyp | If.
Ltac argName n :=
  match n with
  | Any      => fresh "a"
  | RetAny   => fresh "r"
  | Hyp      => fresh "H"
  | If       => fresh "e_if"
  end.

Definition IntroArg (n : ArgName) A (goal : A -> Type) := forall a, goal a.

Hint Opaque IntroArg : refines prepostcond.

Lemma IntroArg_fold n A goal : forall a, IntroArg n A goal -> goal a.
Proof. intros a H; exact (H a). Qed.

(* Lemma IntroArg_unfold n A (goal : A -> Prop) : (forall a, goal a) -> IntroArg n A goal. *)
(* Proof. unfold IntroArg; intro H; exact H. Qed. *)

Ltac IntroArg_intro e := intro e.

Ltac IntroArg_forget := let e := fresh in intro e; clear e.

Lemma IntroArg_sum_relE_inl n E1 E2 F1 F2 (REE : relationEH E1 E2) (REF : relationEH F1 F2)
                            A B e1 e2 (goal : _ -> Prop) :
  IntroArg n (REE A B e1 e2) (fun p => goal (sum_relE_inl _ _ _ _ _ _ p)) ->
  IntroArg n (@sum_relE E1 E2 F1 F2 REE REF A B (inl1 e1) (inl1 e2)) goal.
Proof. intros ?H ?H; dependent destruction H0; apply H. Qed.
Lemma IntroArg_sum_relE_inr n E1 E2 F1 F2 (REE : relationEH E1 E2) (REF : relationEH F1 F2)
                            A B f1 f2 (goal : _ -> Prop) :
  IntroArg n (REF A B f1 f2) (fun p => goal (sum_relE_inr _ _ _ _ _ _ p)) ->
  IntroArg n (@sum_relE E1 E2 F1 F2 REE REF A B (inr1 f1) (inr1 f2)) goal.
Proof. intros ?H ?H; dependent destruction H0; apply H. Qed.

Lemma IntroArg_sum_relEAns_inl n E1 E2 F1 F2 (REE : relationEAns E1 E2) (REF : relationEAns F1 F2)
                               A B e1 e2 a b (goal : _ -> Prop) :
  IntroArg n (REE A B e1 e2 a b) (fun p => goal (sum_relEAns_inl _ _ _ _ _ _ _ _ p)) ->
  IntroArg n (@sum_relEAns E1 E2 F1 F2 REE REF A B (inl1 e1) (inl1 e2) a b) goal.
Proof. intros ?H ?H; dependent destruction H0; apply H. Qed.
Lemma IntroArg_sum_relEAns_inr n E1 E2 F1 F2 (REE : relationEAns E1 E2) (REF : relationEAns F1 F2)
                               A B f1 f2 a b (goal : _ -> Prop) :
  IntroArg n (REF A B f1 f2 a b) (fun p => goal (sum_relEAns_inr _ _ _ _ _ _ _ _ p)) ->
  IntroArg n (@sum_relEAns E1 E2 F1 F2 REE REF A B (inr1 f1) (inr1 f2) a b) goal.
Proof. intros ?H ?H; dependent destruction H0; apply H. Qed.

Lemma IntroArg_padded_refines_rec_REInv_i n A1 A2 R1 R2 (precond : A1 -> A2 -> Prop)
                                          a1 a2 (goal : _ -> Prop) :
  IntroArg n (precond a1 a2) (fun p => goal (padded_refines_rec_REInv_i _ _ _ _ _ _ _ p)) ->
  IntroArg n (padded_refines_rec_REInv A1 A2 R1 R2 precond R1 R2 (Call a1) (Call a2)) goal.
Proof. intros ?H ?H; dependent destruction H0; apply H. Qed.

Lemma IntroArg_padded_refines_rec_REAnsInv_i n A1 A2 R1 R2 (RR : R1 -> R2 -> Prop)
                                             (postcond : A1 -> A2 -> forall (r1 : R1) (r2 : R2), RR r1 r2 -> Prop)
                                             a1 a2 r1 r2 (goal : _ -> Prop) :
  IntroArg n (RR r1 r2) (fun p1 => IntroArg n (postcond a1 a2 r1 r2 p1) (fun p2 =>
    goal (padded_refines_rec_REAnsInv_i _ _ _ _ _ _ _ _ _ _ (exist _ p1 p2)))) ->
  IntroArg n (padded_refines_rec_REAnsInv A1 A2 R1 R2 RR postcond R1 R2 (Call a1) (Call a2) r1 r2) goal.
Proof. intros ?H ?H; dependent destruction H0; dependent destruction d; apply H. Qed.

Ltac IntroArg_intro_dependent_destruction n :=
  let e := argName n in
    IntroArg_intro e; dependent destruction e.

Check dep_prod_rel.

Ltac IntroArg_base_tac n A g :=
  lazymatch A with
  | sum_relE _ _ _ _ (inl1 _) (inl1 _) => simple apply IntroArg_sum_relE_inl
  | sum_relE _ _ _ _ (inr1 _) (inr1 _) => simple apply IntroArg_sum_relE_inr
  | sum_relE _ _ _ _ (inl1 _) (inr1 _) => IntroArg_intro_dependent_destruction n
  | sum_relE _ _ _ _ (inr1 _) (inl1 _) => IntroArg_intro_dependent_destruction n
  | sum_relEAns _ _ _ _ (inl1 _) (inl1 _) _ _ => simple apply IntroArg_sum_relEAns_inl
  | sum_relEAns _ _ _ _ (inr1 _) (inr1 _) _ _ => simple apply IntroArg_sum_relEAns_inr
  | sum_relEAns _ _ _ _ (inl1 _) (inr1 _) _ _ => IntroArg_intro_dependent_destruction n
  | sum_relEAns _ _ _ _ (inr1 _) (inl1 _) _ _ => IntroArg_intro_dependent_destruction n
  | padded_refines_rec_REInv _ _ _ _ _ _ _ (Call _) (Call _) => simple apply IntroArg_padded_refines_rec_REInv_i
  | padded_refines_rec_REAnsInv _ _ _ _ _ _ _ _ (Call _) (Call _) _ _ => simple apply IntroArg_padded_refines_rec_REAnsInv_i
  | true  = true  => IntroArg_intro_dependent_destruction n
  | false = false => IntroArg_intro_dependent_destruction n
  | true  = false => IntroArg_intro_dependent_destruction n
  | false = true  => IntroArg_intro_dependent_destruction n
  end.

Hint Extern 101 (IntroArg ?n ?A ?g) => IntroArg_base_tac n A g : refines prepostcond.

Ltac IntroArg_rewrite_bool_eq n :=
  let e := fresh in
    IntroArg_intro e; repeat rewrite e in *;
    apply (IntroArg_fold n _ _ e); clear e.

Hint Extern 102 (IntroArg ?n (@eq bool _ _) _) =>
  progress (IntroArg_rewrite_bool_eq n) : refines prepostcond.

Hint Extern 105 (IntroArg ?n (?x = ?y) _) =>
  let e := argName n in IntroArg_intro e;
    try first [ is_var x; subst x | is_var y; subst y ] : refinesprepostcond .
Hint Extern 106 (IntroArg ?n _ _) =>
  let e := argName n in IntroArg_intro e : refines prepostcond.


(** * Hints for Relation Goals *)

Lemma RelGoal_sum_relE_inl E1 E2 F1 F2 (REE : relationEH E1 E2) (REF : relationEH F1 F2)
                           A B e1 e2 :
  RelGoal (REE A B e1 e2) ->
  RelGoal (@sum_relE E1 E2 F1 F2 REE REF A B (inl1 e1) (inl1 e2)).
Proof. constructor; eauto. Qed.
Lemma RelGoal_sum_relE_inr E1 E2 F1 F2 (REE : relationEH E1 E2) (REF : relationEH F1 F2)
                           A B f1 f2 :
  RelGoal (REF A B f1 f2) ->
  RelGoal (@sum_relE E1 E2 F1 F2 REE REF A B (inr1 f1) (inr1 f2)).
Proof. constructor; eauto. Qed.

Hint Extern 101 (RelGoal (sum_relE _ _ _ _ (inl1 _) (inl1 _))) =>
  simple apply RelGoal_sum_relE_inl : refines.
Hint Extern 101 (RelGoal (sum_relE _ _ _ _ (inr1 _) (inr1 _))) =>
  simple apply RelGoal_sum_relE_inr : refines.


Lemma RelGoal_sum_relEAns_inl E1 E2 F1 F2 (REE : relationEAns E1 E2) (REF : relationEAns F1 F2)
                              A B e1 e2 a b :
  RelGoal (REE A B e1 e2 a b) ->
  RelGoal (@sum_relEAns E1 E2 F1 F2 REE REF A B (inl1 e1) (inl1 e2) a b).
Proof. constructor; eauto. Qed.
Lemma RelGoal_sum_relEAns_inr E1 E2 F1 F2 (REE : relationEAns E1 E2) (REF : relationEAns F1 F2)
                              A B f1 f2 a b :
  RelGoal (REF A B f1 f2 a b) ->
  RelGoal (@sum_relEAns E1 E2 F1 F2 REE REF A B (inr1 f1) (inr1 f2) a b).
Proof. constructor; eauto. Qed.

Hint Extern 101 (RelGoal (sum_relEAns _ _ _ _ (inl1 _) (inl1 _) _ _)) =>
  simple apply RelGoal_sum_relEAns_inl : refines.
Hint Extern 101 (RelGoal (sum_relEAns _ _ _ _ (inr1 _) (inr1 _) _ _)) =>
  simple apply RelGoal_sum_relEAns_inr : refines.

Lemma RelGoal_padded_refines_rec_REInv_i A1 A2 R1 R2 (precond : A1 -> A2 -> Prop)
                                         a1 a2 :
  RelGoal (precond a1 a2) ->
  RelGoal (padded_refines_rec_REInv A1 A2 R1 R2 precond R1 R2 (Call a1) (Call a2)).
Proof. constructor; eauto. Qed.

Hint Extern 101 (RelGoal (padded_refines_rec_REInv _ _ _ _ _ _ _ (Call _) (Call _))) =>
  simple apply RelGoal_padded_refines_rec_REInv_i : refines.

Lemma RelGoal_padded_refines_rec_REAnsInv_i A1 A2 R1 R2 (RR : R1 -> R2 -> Prop)
                                            (postcond : A1 -> A2 -> forall (r1 : R1) (r2 : R2), RR r1 r2 -> Prop)
                                            a1 a2 r1 r2 :
  forall (p1 : RelGoal (RR r1 r2)), RelGoal (postcond a1 a2 r1 r2 p1) ->
  RelGoal (padded_refines_rec_REAnsInv A1 A2 R1 R2 RR postcond R1 R2 (Call a1) (Call a2) r1 r2).
Proof. constructor; econstructor; eauto. Qed.

Hint Extern 101 (RelGoal (padded_refines_rec_REAnsInv _ _ _ _ _ _ _ _ (Call _) (Call _) _ _)) =>
  simple apply RelGoal_padded_refines_rec_REAnsInv_i : refines.

Lemma RelGoal_dep_prod_rel {R1 R2} (RR1 : R1 -> R2 -> Prop) (RR2 : forall r1 r2, RR1 r1 r2 -> Prop) r1 r2 :
  forall (p1 : RelGoal (RR1 r1 r2)), RelGoal (RR2 r1 r2 p1) ->
  RelGoal (@dep_prod_rel R1 R2 RR1 RR2 r1 r2).
Proof. econstructor; eauto. Qed.

Hint Extern 101 (RelGoal (dep_prod_rel _ _ _ _)) =>
  simple apply RelGoal_dep_prod_rel : refines.


(** * Basic Refinement Hints *)

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

Hint Extern 101 (padded_refines _ _ _ (if _ then _ else _) _) =>
  apply padded_refines_if_l_IntroArg : refines.
Hint Extern 101 (padded_refines _ _ _ _ (if _ then _ else _)) =>
  apply padded_refines_if_r_IntroArg : refines.

Definition padded_refines_ret_lr_IntroArg E1 E2 R1 R2 RE REAns RR r1 r2 :
  (RelGoal (RR r1 r2 : Prop)) ->
  @padded_refines E1 E2 R1 R2 RE REAns RR (Ret r1) (Ret r2) :=
  padded_refines_ret_lr E1 E2 R1 R2 RE REAns RR r1 r2.

Hint Extern 103 (padded_refines _ _ _ (Ret _) (Ret _)) =>
  apply padded_refines_ret_lr_IntroArg : refines.

Definition padded_refines_vis_lr_IntroArg E1 E2 R1 R2 A B
        RE REAns RR (e1 : E1 A) (e2 : E2 B)
        (k1 : A -> itree_spec E1 R1) (k2 : B -> itree_spec E2 R2) :
  (RelGoal (RE A B e1 e2 : Prop)) ->
  (IntroArg Any A (fun a => IntroArg Any B (fun b =>
     IntroArg Hyp (REAns A B e1 e2 a b : Prop) (fun _ =>
       padded_refines RE REAns RR (k1 a) (k2 b))))) ->
  padded_refines RE REAns RR (Vis (Spec_vis e1) k1) (Vis (Spec_vis e2) k2) :=
  padded_refines_vis_lr E1 E2 R1 R2 A B RE REAns RR e1 e2 k1 k2.

Hint Extern 104 (padded_refines _ _ _ (Vis (Spec_vis _) _) (Vis (Spec_vis _) _)) =>
  apply padded_refines_vis_lr_IntroArg : refines.

Definition padded_refines_trigger_lr_IntroArg E1 E2 R1 R2
      RE REAns RR (e1 : E1 R1) (e2 : E2 R2) :
  (RelGoal (RE R1 R2 e1 e2 : Prop)) ->
  (IntroArg RetAny R1 (fun r1 => IntroArg RetAny R2 (fun r2 =>
     IntroArg Hyp (REAns R1 R2 e1 e2 r1 r2 : Prop) (fun _ =>
       RelGoal (RR r1 r2 : Prop))))) ->
  padded_refines RE REAns RR (ITree.trigger (Spec_vis e1)) (ITree.trigger (Spec_vis e2)) :=
  padded_refines_trigger_lr E1 E2 R1 R2 RE REAns RR e1 e2.

Hint Extern 103 (padded_refines _ _ _ (ITree.trigger (Spec_vis _)) (ITree.trigger (Spec_vis _))) =>
  apply padded_refines_trigger_lr_IntroArg : refines.


(** * Refinement Hints About Recursion *)

Definition Precondition {A1 A2} (a1 : A1) (a2 : A2) := Prop.
Definition Postcondition {A1 A2 R1 R2 RR} (a1 : A1) (a2 : A2)
                         (r1 : R1) (r2 : R2) (H : (RR r1 r2 : Prop)) := Prop.

Hint Opaque Precondition : prepostcond.
Hint Opaque Postcondition : prepostcond.

Hint Extern 999 (Precondition _ _) => shelve : prepostcond.
Hint Extern 999 (Postcondition _ _ _ _ _) => shelve : prepostcond.

Definition padded_refines_rec_lr_IntroArg
           E1 E2 A1 A2 R1 R2 RE REAns (RR : R1 -> R2 -> Prop) body1 body2 a1 a2
           (precond : IntroArg Any A1 (fun a1 => IntroArg Any A2 (fun a2 => Precondition a1 a2)))
           (postcond : IntroArg Any A1 (fun a1 => IntroArg Any A2 (fun a1 =>
                       IntroArg RetAny R1 (fun r1 => IntroArg RetAny R2 (fun r2 =>
                       IntroArg Hyp (RR r1 r2) (fun H => Postcondition a1 a2 r1 r2 H)))))) :
  precond a1 a2 ->
  (IntroArg Any A1 (fun a1 => IntroArg Any A2 (fun a2 =>
   IntroArg Hyp (precond a1 a2) (fun _ => Halt (
     padded_refines (sum_relE _ RE)
                    (sum_relEAns _ REAns)
                    (dep_prod_rel RR (postcond a1 a2))
                    (body1 a1) (body2 a2)))))) ->
  padded_refines RE REAns RR (mrec_spec (calling' body1) (Call a1))
                 (mrec_spec (calling' body2) (Call a2)) :=
  padded_refines_rec_lr E1 E2 A1 A2 R1 R2 RE REAns RR precond postcond body1 body2 a1 a2.

Ltac padded_refines_rec := eapply padded_refines_rec_lr_IntroArg; [shelve | idtac].

Hint Extern 101 (padded_refines _ _ _ (mrec_spec (calling' _) (Call _))
                                      (mrec_spec (calling' _) (Call _))) =>
  padded_refines_rec : refines.
Hint Extern 101 (padded_refines _ _ _ (rec_spec _ _) (rec_spec _ _)) =>
  padded_refines_rec : refines.
Hint Extern 101 (padded_refines _ _ _ (rec_fix_spec _ _) (rec_fix_spec _ _)) =>
  padded_refines_rec : refines.

Hint Extern 101 (padded_refines _ _ _ (call_spec _) (call_spec _)) =>
  apply padded_refines_trigger_lr_IntroArg : refines.


(** * Tactics *)

Ltac prove_refinement_eauto :=
  unshelve (typeclasses eauto with refines).

Ltac prove_refinement_prepostcond :=
  try (unshelve (typeclasses eauto with prepostcond)).

Ltac prove_refinement :=
  prove_refinement_eauto; prove_refinement_prepostcond.


(** * Examples *)

Open Scope Z_scope.

Lemma test_ifs E x :
  @padded_refines E E _ _ eqE eqEAns eq
                  (if x >=? 0 then if x <? 256 then Ret 1 else Ret 0 else Ret 0)
                  (if x <? 256 then if x >=? 0 then Ret 1 else Ret 0 else Ret 0).
Proof.
  prove_refinement.
Qed.

Lemma test_spins E (x : Z) :
  @padded_refines E E Z Z eqE eqEAns eq
                  (rec_fix_spec (fun rec a => rec a) x)
                  (rec_fix_spec (fun rec a => rec a) x).
Proof.
  prove_refinement.
  - exact True.
  - exact True.
  - easy.
  - prove_refinement.
Qed.
