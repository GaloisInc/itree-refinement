Require Import Coq.Lists.List Coq.Sorting.Permutation.

From Coq Require Import ZArith.
From ITree Require Export ITree.
From Paco Require Import paco.
Require Import Lia.
Require Export Refinement Merge MergePartial.

Import Monads.
Import MonadNotation.
Local Open Scope monad_scope.


(** * Basic Refinement Lemmas *)

Lemma padded_refines_ret E1 E2 R1 R2 RPre RPost RR r1 r2 :
  (RR r1 r2 : Prop) ->
  @padded_refines E1 E2 R1 R2 RPre RPost RR (Ret r1) (Ret r2).
Proof.
  apply padded_refines_ret.
Qed.

Lemma padded_refines_vis E1 E2 R1 R2 A B
        RPre RPost RR (e1 : E1 A) (e2 : E2 B)
        (k1 : A -> itree_spec E1 R1) (k2 : B -> itree_spec E2 R2) :
  (RPre A B e1 e2 : Prop) ->
  (forall a b, (RPost A B e1 e2 a b : Prop) -> padded_refines RPre RPost RR (k1 a) (k2 b)) ->
  padded_refines RPre RPost RR (Vis (Spec_vis e1) k1) (Vis (Spec_vis e2) k2).
Proof.
  apply padded_refines_vis.
Qed.

Lemma padded_refines_exists_r E1 E2 R1 R2 A
      RPre RPost RR (phi : itree_spec E1 R1) (kphi : A -> itree_spec E2 R2) a :
  padded_refines RPre RPost RR phi (kphi a) ->
  padded_refines RPre RPost RR phi (Vis Spec_exists kphi).
Proof.
  setoid_rewrite <- bind_trigger.
  apply padded_exists_spec_elim.
Qed.
Lemma padded_refines_exists_l E1 E2 R1 R2 A
      RPre RPost RR (phi : itree_spec E2 R2) (kphi : A -> itree_spec E1 R1) :
  (forall a, padded_refines RPre RPost RR (kphi a) phi) ->
  padded_refines RPre RPost RR (Vis Spec_exists kphi) phi.
Proof.
  setoid_rewrite <- bind_trigger.
  apply padded_exists_spec_eliml.
Qed.

Lemma padded_refines_forall_r E1 E2 R1 R2 A
      RPre RPost RR (phi : itree_spec E1 R1) (kphi : A -> itree_spec E2 R2) :
  (forall a, padded_refines RPre RPost RR phi (kphi a)) ->
  padded_refines RPre RPost RR phi (Vis Spec_forall kphi).
Proof.
  setoid_rewrite <- bind_trigger.
  apply padded_forall_spec_elim.
Qed.
Lemma padded_refines_forall_l E1 E2 R1 R2 A
      RPre RPost RR (phi : itree_spec E2 R2) (kphi : A -> itree_spec E1 R1) a :
  padded_refines RPre RPost RR (kphi a) phi ->
  padded_refines RPre RPost RR (Vis Spec_forall kphi) phi.
Proof.
  setoid_rewrite <- bind_trigger.
  apply padded_forall_spec_eliml.
Qed.

Lemma padded_refines_if_r E1 E2 RPre RPost R1 R2 RR (t1 : itree_spec E1 R1) (t2 t3: itree_spec E2 R2) b :
  (b = true  -> padded_refines RPre RPost RR t1 t2) ->
  (b = false -> padded_refines RPre RPost RR t1 t3) ->
  padded_refines RPre RPost RR t1 (if b then t2 else t3).
Proof.
  intros. destruct b; eauto.
Qed.
Lemma padded_refines_if_l E1 E2 RPre RPost R1 R2 RR (t1 t2 : itree_spec E1 R1) (t3 : itree_spec E2 R2) b :
  (b = true  -> padded_refines RPre RPost RR t1 t3) ->
  (b = false -> padded_refines RPre RPost RR t2 t3) ->
  padded_refines RPre RPost RR (if b then t1 else t2) t3.
Proof.
  intros. destruct b; eauto.
Qed.

Lemma padded_refines_if_bind_r A E1 E2 RPre RPost R1 R2 RR
      (t1 : itree_spec E1 R1) (t2 t3 : itree_spec E2 A)
      (t4 : A -> itree_spec E2 R2) (b : bool) :
  padded_refines RPre RPost RR t1 (if b then t2 >>= t4 else t3 >>= t4) ->
  padded_refines RPre RPost RR t1 ((if b then t2 else t3) >>= t4).
Proof.
  intros. destruct b; eauto.
Qed.
Lemma padded_refines_if_bind_l A E1 E2 RPre RPost R1 R2 RR
      (t1 t2 : itree_spec E1 A) (t3 : A -> itree_spec E1 R1)
      (t4 : itree_spec E2 R2) (b : bool) :
  padded_refines RPre RPost RR (if b then t1 >>= t3 else t2 >>= t3) t4 ->
  padded_refines RPre RPost RR ((if b then t1 else t2) >>= t3) t4.
Proof.
  intros. destruct b; eauto.
Qed.

Lemma padded_refines_match_list_r E1 E2 RPre RPost R1 R2 RR A (t1 : itree_spec E1 R1)
      (t2 : A -> list A -> itree_spec E2 R2) (t3 : itree_spec E2 R2) xs :
  (forall x xs', xs = x :: xs' -> padded_refines RPre RPost RR t1 (t2 x xs')) ->
  (xs = nil -> padded_refines RPre RPost RR t1 t3) ->
  padded_refines RPre RPost RR t1 (match xs with | x :: xs' => t2 x xs' | nil => t3 end).
Proof.
  intros. destruct xs; eauto.
Qed.
Lemma padded_refines_match_list_l E1 E2 RPre RPost R1 R2 RR A (t3 : itree_spec E2 R2)
      (t1 : A -> list A -> itree_spec E1 R1) (t2 : itree_spec E1 R1) xs :
  (forall x xs', xs = x :: xs' -> padded_refines RPre RPost RR (t1 x xs') t3) ->
  (xs = nil -> padded_refines RPre RPost RR t2 t3) ->
  padded_refines RPre RPost RR (match xs with | x :: xs' => t1 x xs' | nil => t2 end) t3.
Proof.
  intros. destruct xs; eauto.
Qed.

Lemma padded_refines_match_list_bind_r B E1 E2 RPre RPost R1 R2 RR A (t1 : itree_spec E1 R1)
      (t2 : A -> list A -> itree_spec E2 B) (t3 : itree_spec E2 B)
      (t4 : B -> itree_spec E2 R2) xs :
  padded_refines RPre RPost RR t1 (match xs with | x :: xs' => t2 x xs' >>= t4 | nil => t3 >>= t4 end) ->
  padded_refines RPre RPost RR t1 ((match xs with | x :: xs' => t2 x xs' | nil => t3 end) >>= t4).
Proof.
  intros. destruct xs; eauto.
Qed.
Lemma padded_refines_match_list_bind_l B E1 E2 RPre RPost R1 R2 RR A (t3 : itree_spec E2 R2)
      (t1 : A -> list A -> itree_spec E1 B) (t2 : itree_spec E1 B)
      (t4 : B -> itree_spec E1 R1) xs :
  padded_refines RPre RPost RR (match xs with | x :: xs' => t1 x xs' >>= t4 | nil => t2 >>= t4 end) t3 ->
  padded_refines RPre RPost RR ((match xs with | x :: xs' => t1 x xs' | nil => t2 end) >>= t4) t3.
Proof.
  intros. destruct xs; eauto.
Qed.

Lemma padded_refines_match_pair_r E1 E2 RPre RPost R1 R2 RR A B
      (t1 : itree_spec E1 R1) (t2 : A -> B -> itree_spec E2 R2) pr :
  (forall x y, pr = (x, y) -> padded_refines RPre RPost RR t1 (t2 x y)) ->
  padded_refines RPre RPost RR t1 (match pr with | (x,y) => t2 x y end).
Proof.
  intros. destruct pr; eauto.
Qed.
Lemma padded_refines_match_pair_l E1 E2 RPre RPost R1 R2 RR A B
      (t1 : A -> B -> itree_spec E1 R1) (t2 : itree_spec E2 R2) pr :
  (forall x y, pr = (x, y) -> padded_refines RPre RPost RR (t1 x y) t2) ->
  padded_refines RPre RPost RR (match pr with | (x,y) => t1 x y end) t2.
Proof.
  intros. destruct pr; eauto.
Qed.

Lemma padded_refines_match_pair_bind_r C E1 E2 RPre RPost R1 R2 RR A B
      (t1 : itree_spec E1 R1) (t2 : A -> B -> itree_spec E2 C)
      (t3 : C -> itree_spec E2 R2) pr :
  padded_refines RPre RPost RR t1 (match pr with | (x,y) => t2 x y >>= t3 end) ->
  padded_refines RPre RPost RR t1 ((match pr with | (x,y) => t2 x y end) >>= t3).
Proof.
  intros. destruct pr; eauto.
Qed.
Lemma padded_refines_match_pair_bind_l C E1 E2 RPre RPost R1 R2 RR A B
      (t1 : A -> B -> itree_spec E1 C) (t2 : itree_spec E2 R2)
      (t3 : C -> itree_spec E1 R1) pr :
  padded_refines RPre RPost RR (match pr with | (x,y) => t1 x y >>= t3 end) t2 ->
  padded_refines RPre RPost RR ((match pr with | (x,y) => t1 x y end) >>= t3) t2.
Proof.
  intros. destruct pr; eauto.
Qed.

Lemma padded_refines_ret_bind_r E1 E2 R1 R2 A
      RPre RPost RR (phi : itree_spec E1 R1) r (kphi : A -> itree_spec E2 R2) :
  padded_refines RPre RPost RR phi (kphi r) ->
  padded_refines RPre RPost RR phi (Ret r >>= kphi).
Proof.
  setoid_rewrite bind_ret_l; eauto.
Qed.
Lemma padded_refines_ret_bind_l E1 E2 R1 R2 A
      RPre RPost RR (phi : itree_spec E2 R2) r (kphi : A -> itree_spec E1 R1) :
  padded_refines RPre RPost RR (kphi r) phi ->
  padded_refines RPre RPost RR (Ret r >>= kphi) phi.
Proof.
  setoid_rewrite bind_ret_l; eauto.
Qed.

Lemma padded_refines_trigger_bind_r E1 E2 R1 R2 A
      RPre RPost RR (phi : itree_spec E1 R1) e (kphi : A -> itree_spec E2 R2) :
  padded_refines RPre RPost RR phi (Vis e kphi) ->
  padded_refines RPre RPost RR phi (ITree.trigger e >>= kphi).
Proof.
  setoid_rewrite bind_trigger; eauto.
Qed.
Lemma padded_refines_trigger_bind_l E1 E2 R1 R2 A
      RPre RPost RR (phi : itree_spec E2 R2) e (kphi : A -> itree_spec E1 R1) :
  padded_refines RPre RPost RR (Vis e kphi) phi ->
  padded_refines RPre RPost RR (ITree.trigger e >>= kphi) phi.
Proof.
  setoid_rewrite bind_trigger; eauto.
Qed.

Lemma padded_refines_vis_bind_r E1 E2 R1 R2 A1 A2
      RPre RPost RR (phi : itree_spec E1 R1) e
      (kphi1 : A1 -> itree_spec E2 A2) (kphi2 : A2 -> itree_spec E2 R2) :
  padded_refines RPre RPost RR phi (Vis e (fun a => kphi1 a >>= kphi2)) ->
  padded_refines RPre RPost RR phi (Vis e kphi1 >>= kphi2).
Proof.
  setoid_rewrite bind_vis; eauto.
Qed.
Lemma padded_refines_vis_bind_l E1 E2 R1 R2 A1 A2
      RPre RPost RR (phi : itree_spec E2 R2) e
      (kphi1 : A1 -> itree_spec E1 A2) (kphi2 : A2 -> itree_spec E1 R1) :
  padded_refines RPre RPost RR (Vis e (fun a => kphi1 a >>= kphi2)) phi ->
  padded_refines RPre RPost RR (Vis e kphi1 >>= kphi2) phi.
Proof.
  setoid_rewrite bind_vis; eauto.
Qed.

Lemma padded_refines_bind_bind_r E1 E2 R1 R2 A1 A2
      RPre RPost RR (phi1 : itree_spec E1 R1) (phi2 : itree_spec E2 A1)
      (kphi1 : A1 -> itree_spec E2 A2) (kphi2 : A2 -> itree_spec E2 R2) :
  padded_refines RPre RPost RR phi1 (phi2 >>= (fun a => kphi1 a >>= kphi2)) ->
  padded_refines RPre RPost RR phi1 ((phi2 >>= kphi1) >>= kphi2).
Proof.
  setoid_rewrite bind_bind; eauto.
Qed.
Lemma padded_refines_bind_bind_l E1 E2 R1 R2 A1 A2
      RPre RPost RR (phi1 : itree_spec E2 A1) (phi2 : itree_spec E1 R1)
      (kphi1 : A1 -> itree_spec E2 A2) (kphi2 : A2 -> itree_spec E2 R2) :
  padded_refines RPre RPost RR (phi1 >>= (fun a => kphi1 a >>= kphi2)) phi2 ->
  padded_refines RPre RPost RR ((phi1 >>= kphi1) >>= kphi2) phi2.
Proof.
  setoid_rewrite bind_bind; eauto.
Qed.


(** * Refinement Lemmas About Recursion *)

Section Rec.

Context (E1 E2 : Type -> Type) (A1 A2 R1 R2 : Type).
Context (RPre : PreRel E1 E2) (RPost : PostRel E1 E2) (RR : R1 -> R2 -> Prop).

Context (precond : A1 -> A2 -> Prop)
        (postcond : forall a1 a2, precond a1 a2 -> forall r1 r2, RR r1 r2 -> Prop).

Variant OnCallPreRel : PreRel (callE A1 R1) (callE A2 R2) :=
  | OnCallPreRel_i a1 a2 : precond a1 a2 ->
    OnCallPreRel R1 R2 (Call a1) (Call a2).

Variant OnCallPostRel : PostRel (callE A1 R1) (callE A2 R2) :=
  | OnCallPostRel_i a1 a2 r1 r2 p : depProdRel RR (postcond a1 a2 p) r1 r2 ->
    OnCallPostRel R1 R2 (Call a1) (Call a2) r1 r2.

Context (body1 : A1 -> itree_spec (callE A1 R1 +' E1) R1).

Section RecRec.
Context (body2 : A2 -> itree_spec (callE A2 R2 +' E2) R2).

Lemma padded_refines_rec (a1 : A1) (a2 : A2) :
  precond a1 a2 ->
  (forall a1 a2 (p : precond a1 a2),
     padded_refines (sumPreRel OnCallPreRel RPre)
                    (sumPostRel OnCallPostRel RPost)
                    (depProdRel RR (postcond a1 a2 p))
                    (body1 a1) (body2 a2)) ->
  padded_refines RPre RPost RR (mrec_spec (calling' body1) (Call a1))
                             (mrec_spec (calling' body2) (Call a2)).
Proof.
  intros.
  eapply padded_refines_monot with
    (RR1 := OnCallPostRel R1 R2 (Call a1) (Call a2)); eauto.
  { intros. inv PR. destruct H7. inj_existT. subst. auto. }
  eapply padded_refines_mrec with (RPreInv := OnCallPreRel)
                                  (RPostInv := OnCallPostRel).
  - intros A B [] [] []. unfold calling'.
    eapply padded_refines_monot with (RR1 := depProdRel RR (postcond a3 a4 H1)); eauto.
    intros. econstructor; eauto.
  - constructor; eauto.
Qed.

End RecRec.

Context (Pre : A2 -> Prop) (Post : A2 -> R2 -> Prop).
Context (rdec : A2 -> A2 -> Prop).

Definition total_spec_fix_body (a : A2) : itree_spec (callE A2 R2 +' E2) R2 :=
  assume_spec (Pre a);;
  (
    n <- exists_spec nat;;
    trepeat n (a' <- exists_spec A2;; assert_spec (Pre a' /\ rdec a' a);; call_spec a')
  );;
  b <- exists_spec R2;;
  assert_spec (Post a b);;
  Ret b.

Lemma padded_refines_total_spec (a1 : A1) (a2 : A2) :
  well_founded rdec ->
  precond a1 a2 ->
  (forall a1 a2 (p : precond a1 a2),
     padded_refines (sumPreRel OnCallPreRel RPre)
                    (sumPostRel OnCallPostRel RPost)
                    (depProdRel RR (postcond a1 a2 p))
                    (body1 a1) (total_spec_fix_body a2)) ->
  padded_refines RPre RPost RR (mrec_spec (calling' body1) (Call a1))
                             (total_spec Pre Post a2).
Proof.
  intro; rewrite <- total_spec_fix_total; eauto.
  apply padded_refines_rec.
Qed.

End Rec.

Lemma padded_refines_trepeat_zero_r E1 E2 R1 R2 RPre RPost RR
      (t1 : itree_spec E1 R1) (t2 : itree_spec E2 R2) :
  padded_refines RPre RPost RR t1 (Ret tt) ->
  padded_refines RPre RPost RR t1 (trepeat 0 t2).
Proof. eauto. Qed.

Lemma padded_refines_trepeat_suc_r E1 E2 R1 R2 RPre RPost RR
      (t1 : itree_spec E1 R1) n (t2 : itree_spec E2 R2) :
  padded_refines RPre RPost RR t1 (t2 ;; trepeat n t2) ->
  padded_refines RPre RPost RR t1 (trepeat (S n) t2).
Proof. eauto. Qed.

Lemma padded_refines_trepeat_bind_zero_r E1 E2 R1 R2 R3 RPre RPost RR
      (t1 : itree_spec E1 R1) (t2 : itree_spec E2 R2) (t3 : unit -> itree_spec E2 R3) :
  padded_refines RPre RPost RR t1 (t3 tt) ->
  padded_refines RPre RPost RR t1 (trepeat 0 t2 >>= t3).
Proof. eauto. Qed.

Lemma padded_refines_trepeat_bind_suc_r E1 E2 R1 R2 R3 RPre RPost RR
      (t1 : itree_spec E1 R1) n (t2 : itree_spec E2 R2) (t3 : unit -> itree_spec E2 R3) :
  padded_refines RPre RPost RR t1 (t2 ;; (trepeat n t2 >>= t3)) ->
  padded_refines RPre RPost RR t1 (trepeat (S n) t2 >>= t3).
Proof. simpl; rewrite bind_bind; eauto. Qed.


(** * Hint Database Definitions *)

Create HintDb refines.
Create HintDb prepostcond.

Hint Extern 999 (padded_refines _ _ _ _ _) => shelve : refines.

Definition RelGoal (goal : Prop) := goal.

Hint Opaque RelGoal : refines.

Hint Extern 999 (RelGoal _) =>
  unfold RelGoal; (reflexivity || shelve) : refines.

Lemma padded_refines_eq_unfold E R1 R2 RR (t1 : itree_spec E R1) (t2 : itree_spec E R2) :
  padded_refines eqPreRel eqPostRel RR t1 t2 ->
  padded_refines_eq RR t1 t2.
Proof. eauto. Qed.

Hint Extern 100 (padded_refines_eq _ _ _) =>
  simple apply padded_refines_eq_unfold : refines.


(** * IntroArg Definition and Hints *)

Inductive ArgName := Any | RetAny | Hyp | Exists | Forall | If | Match.
Ltac argName n :=
  match n with
  | Any      => fresh "a"
  | RetAny   => fresh "r"
  | Hyp      => fresh "H"
  | Exists   => fresh "e_exists"
  | Forall   => fresh "e_forall"
  | If       => fresh "e_if"
  | Match    => fresh "e_match"
  end.

Polymorphic Definition IntroArg (n : ArgName) A (goal : A -> Type) := forall a, goal a.

Hint Opaque IntroArg : refines prepostcond.

Polymorphic Lemma IntroArg_fold n A goal : forall a, IntroArg n A goal -> goal a.
Proof. intros a H; exact (H a). Qed.

(* Polymorphic Lemma IntroArg_unfold n A (goal : A -> Prop) : (forall a, goal a) -> IntroArg n A goal. *)
(* Proof. unfold IntroArg; intro H; exact H. Qed. *)

Ltac IntroArg_intro e := intro e.

Ltac IntroArg_forget := let e := fresh in intro e; clear e.

Polymorphic Lemma IntroArg_eta n A (f : A -> Type) x goal :
  IntroArg n (f x) goal ->
  IntroArg n ((fun x' => f x') x) goal.
Proof. eauto. Qed.

Polymorphic Lemma IntroArg_and n P Q (goal : P /\ Q -> Prop)
  : IntroArg n P (fun p => IntroArg n Q (fun q => goal (conj p q))) -> IntroArg n _ goal.
Proof. intros H [ p q ]; apply H. Qed.

Polymorphic Lemma IntroArg_sumPreRel_inl n E1 E2 F1 F2
                  (RPreE : PreRel E1 E2) (RPreF : PreRel F1 F2)
                  A B e1 e2 (goal : _ -> Prop) :
  IntroArg n (RPreE A B e1 e2) (fun p => goal (sumPreRel_inl _ _ _ _ _ _ p)) ->
  IntroArg n (@sumPreRel E1 E2 F1 F2 RPreE RPreF A B (inl1 e1) (inl1 e2)) goal.
Proof. intros ?H ?H; dependent destruction H0; apply H. Qed.
Polymorphic Lemma IntroArg_sumPreRel_inr n E1 E2 F1 F2
                  (RPreE : PreRel E1 E2) (RPreF : PreRel F1 F2)
                  A B f1 f2 (goal : _ -> Prop) :
  IntroArg n (RPreF A B f1 f2) (fun p => goal (sumPreRel_inr _ _ _ _ _ _ p)) ->
  IntroArg n (@sumPreRel E1 E2 F1 F2 RPreE RPreF A B (inr1 f1) (inr1 f2)) goal.
Proof. intros ?H ?H; dependent destruction H0; apply H. Qed.

Polymorphic Lemma IntroArg_sumPostRel_inl n E1 E2 F1 F2
                  (RPreE : PostRel E1 E2) (RPreF : PostRel F1 F2)
                  A B e1 e2 a b (goal : _ -> Prop) :
  IntroArg n (RPreE A B e1 e2 a b) (fun p => goal (sumPostRel_inl _ _ _ _ _ _ _ _ p)) ->
  IntroArg n (@sumPostRel E1 E2 F1 F2 RPreE RPreF A B (inl1 e1) (inl1 e2) a b) goal.
Proof. intros ?H ?H; dependent destruction H0; apply H. Qed.
Polymorphic Lemma IntroArg_sumPostRel_inr n E1 E2 F1 F2
                  (RPreE : PostRel E1 E2) (RPreF : PostRel F1 F2)
                  A B f1 f2 a b (goal : _ -> Prop) :
  IntroArg n (RPreF A B f1 f2 a b) (fun p => goal (sumPostRel_inr _ _ _ _ _ _ _ _ p)) ->
  IntroArg n (@sumPostRel E1 E2 F1 F2 RPreE RPreF A B (inr1 f1) (inr1 f2) a b) goal.
Proof. intros ?H ?H; dependent destruction H0; apply H. Qed.

Polymorphic Lemma IntroArg_eqPostRel n E A e a1 a2 (goal : _ -> Prop) :
  IntroArg n (a1 = a2) (fun p => goal (eq_rect _ _ (eqPostRel_refl A e a1) _ p)) ->
  IntroArg n (@eqPostRel E A A e e a1 a2) goal.
Proof.
  intros ?H ?H; dependent destruction H0.
  apply (fun H => H eq_refl) in H.
  erewrite eq_rect_eq; eauto.
Qed.

Polymorphic Lemma IntroArg_OnCallPreRel_i n A1 A2 R1 R2
                  (precond : A1 -> A2 -> Prop) a1 a2 (goal : _ -> Prop) :
  IntroArg n (precond a1 a2) (fun p => goal (OnCallPreRel_i _ _ _ _ _ _ _ p)) ->
  IntroArg n (OnCallPreRel A1 A2 R1 R2 precond R1 R2 (Call a1) (Call a2)) goal.
Proof. intros ?H ?H; dependent destruction H0; apply H. Qed.

Polymorphic Lemma IntroArg_OnCallPostRel_i n A1 A2 R1 R2
                  (RR : R1 -> R2 -> Prop) (precond : A1 -> A2 -> Prop)
                  (postcond : forall a1 a2, precond a1 a2 -> forall (r1 : R1) (r2 : R2), RR r1 r2 -> Prop)
                  a1 a2 r1 r2 (goal : _ -> Prop) :
  IntroArg n (precond a1 a2) (fun p0 => IntroArg n (RR r1 r2) (fun p1 =>
  IntroArg n (postcond a1 a2 p0 r1 r2 p1) (fun p2 =>
    goal (OnCallPostRel_i _ _ _ _ _ _ _ _ _ _ _ p0 (exist _ p1 p2))))) ->
  IntroArg n (OnCallPostRel A1 A2 R1 R2 RR precond postcond R1 R2 (Call a1) (Call a2) r1 r2) goal.
Proof. intros ?H ?H; dependent destruction H0; dependent destruction d; apply H. Qed.

Ltac IntroArg_intro_dependent_destruction n :=
  let e := argName n in
    IntroArg_intro e; dependent destruction e.

Ltac IntroArg_base_tac n A g :=
  lazymatch A with
  | (fun _ => _) _ => simple apply IntroArg_eta
  | _ /\ _ => simple apply IntroArg_and
  | sumPreRel _ _ _ _ (inl1 _) (inl1 _) => simple apply IntroArg_sumPreRel_inl
  | sumPreRel _ _ _ _ (inl1 _) (ReSum_inl _ _ _ _ _ _ _) => apply IntroArg_sumPreRel_inl
  | sumPreRel _ _ _ _ (ReSum_inl _ _ _ _ _ _ _) (inl1 _) => apply IntroArg_sumPreRel_inl
  | sumPreRel _ _ _ _ (ReSum_inl _ _ _ _ _ _ _) (ReSum_inl _ _ _ _ _ _ _) => apply IntroArg_sumPreRel_inl
  | sumPreRel _ _ _ _ (inr1 _) (inr1 _) => simple apply IntroArg_sumPreRel_inr
  | sumPreRel _ _ _ _ (inr1 _) (ReSum_inr _ _ _ _ _ _ _) => apply IntroArg_sumPreRel_inr
  | sumPreRel _ _ _ _ (ReSum_inr _ _ _ _ _ _ _) (inr1 _) => apply IntroArg_sumPreRel_inr
  | sumPreRel _ _ _ _ (ReSum_inr _ _ _ _ _ _ _) (ReSum_inr _ _ _ _ _ _ _) => apply IntroArg_sumPreRel_inr
  | sumPreRel _ _ _ _ (inl1 _) (inr1 _) => IntroArg_intro_dependent_destruction n
  | sumPreRel _ _ _ _ (inl1 _) (ReSum_inr _ _ _ _ _ _ _) => IntroArg_intro_dependent_destruction n
  | sumPreRel _ _ _ _ (ReSum_inl _ _ _ _ _ _ _) (inr1 _) => IntroArg_intro_dependent_destruction n
  | sumPreRel _ _ _ _ (ReSum_inl _ _ _ _ _ _ _) (ReSum_inr _ _ _ _ _ _ _) => IntroArg_intro_dependent_destruction n
  | sumPreRel _ _ _ _ (inr1 _) (inl1 _) => IntroArg_intro_dependent_destruction n
  | sumPreRel _ _ _ _ (inr1 _) (ReSum_inl _ _ _ _ _ _ _) => IntroArg_intro_dependent_destruction n
  | sumPreRel _ _ _ _ (ReSum_inr _ _ _ _ _ _ _) (inl1 _) => IntroArg_intro_dependent_destruction n
  | sumPreRel _ _ _ _ (ReSum_inr _ _ _ _ _ _ _) (ReSum_inl _ _ _ _ _ _ _) => IntroArg_intro_dependent_destruction n
  | sumPostRel _ _ _ _ (inl1 _) (inl1 _) _ _ => simple apply IntroArg_sumPostRel_inl
  | sumPostRel _ _ _ _ (inl1 _) (ReSum_inl _ _ _ _ _ _ _) _ _ => apply IntroArg_sumPostRel_inl
  | sumPostRel _ _ _ _ (ReSum_inl _ _ _ _ _ _ _) (inl1 _) _ _ => apply IntroArg_sumPostRel_inl
  | sumPostRel _ _ _ _ (ReSum_inl _ _ _ _ _ _ _) (ReSum_inl _ _ _ _ _ _ _) _ _ => apply IntroArg_sumPostRel_inl
  | sumPostRel _ _ _ _ (inr1 _) (inr1 _) _ _ => simple apply IntroArg_sumPostRel_inr
  | sumPostRel _ _ _ _ (inr1 _) (ReSum_inr _ _ _ _ _ _ _) _ _ => apply IntroArg_sumPostRel_inr
  | sumPostRel _ _ _ _ (ReSum_inr _ _ _ _ _ _ _) (inr1 _) _ _ => apply IntroArg_sumPostRel_inr
  | sumPostRel _ _ _ _ (ReSum_inr _ _ _ _ _ _ _) (ReSum_inr _ _ _ _ _ _ _) _ _ => apply IntroArg_sumPostRel_inr
  | sumPostRel _ _ _ _ (inl1 _) (inr1 _) _ _ => IntroArg_intro_dependent_destruction n
  | sumPostRel _ _ _ _ (inl1 _) (ReSum_inr _ _ _ _ _ _ _) _ _ => IntroArg_intro_dependent_destruction n
  | sumPostRel _ _ _ _ (ReSum_inl _ _ _ _ _ _ _) (inr1 _) _ _ => IntroArg_intro_dependent_destruction n
  | sumPostRel _ _ _ _ (ReSum_inl _ _ _ _ _ _ _) (ReSum_inr _ _ _ _ _ _ _) _ _ => IntroArg_intro_dependent_destruction n
  | sumPostRel _ _ _ _ (inr1 _) (inl1 _) _ _ => IntroArg_intro_dependent_destruction n
  | sumPostRel _ _ _ _ (inr1 _) (ReSum_inl _ _ _ _ _ _ _) _ _ => IntroArg_intro_dependent_destruction n
  | sumPostRel _ _ _ _ (ReSum_inr _ _ _ _ _ _ _) (inl1 _) _ _ => IntroArg_intro_dependent_destruction n
  | sumPostRel _ _ _ _ (ReSum_inr _ _ _ _ _ _ _) (ReSum_inl _ _ _ _ _ _ _) _ _ => IntroArg_intro_dependent_destruction n
  | eqPostRel _ _ _ _ _ _ => apply IntroArg_eqPostRel
  | OnCallPreRel _ _ _ _ _ _ _ (Call _) (Call _) => simple apply IntroArg_OnCallPreRel_i
  | OnCallPostRel _ _ _ _ _ _ _ _ _ (Call _) (Call _) _ _ => simple apply IntroArg_OnCallPostRel_i
  | true  = true  => IntroArg_intro_dependent_destruction n
  | false = false => IntroArg_intro_dependent_destruction n
  | true  = false => IntroArg_intro_dependent_destruction n
  | false = true  => IntroArg_intro_dependent_destruction n
  end.

Hint Extern 101 (IntroArg ?n ?A ?g) => IntroArg_base_tac n A g : refines prepostcond.

Hint Extern 102 (IntroArg ?n (@eq bool _ _) _) =>
  let e := argName n in IntroArg_intro e; rewrite e in * : refines prepostcond.

Hint Extern 199 (IntroArg ?n (?x = ?y) _) =>
  let e := argName n in IntroArg_intro e;
    try first [ is_var x; subst x | is_var y; subst y ] : refines.

Hint Extern 999 (IntroArg ?n _ _) =>
  let e := argName n in IntroArg_intro e : refines prepostcond.


(** * Hints for Relation Goals *)

Lemma RelGoal_eta A (f : A -> Prop) x :
  RelGoal (f x) -> RelGoal ((fun x' => f x') x).
Proof. eauto. Qed.

Hint Extern 101 (RelGoal ((fun _ => _) _)) =>
  simple apply RelGoal_eta.

Lemma RelGoal_sumPreRel_inl E1 E2 F1 F2 (RPreE : PreRel E1 E2) (RPreF : PreRel F1 F2)
                           A B e1 e2 :
  RelGoal (RPreE A B e1 e2) ->
  RelGoal (@sumPreRel E1 E2 F1 F2 RPreE RPreF A B (inl1 e1) (inl1 e2)).
Proof. constructor; eauto. Qed.
Lemma RelGoal_sumPreRel_inr E1 E2 F1 F2 (RPreE : PreRel E1 E2) (RPreF : PreRel F1 F2)
                           A B f1 f2 :
  RelGoal (RPreF A B f1 f2) ->
  RelGoal (@sumPreRel E1 E2 F1 F2 RPreE RPreF A B (inr1 f1) (inr1 f2)).
Proof. constructor; eauto. Qed.

Hint Extern 101 (RelGoal (sumPreRel _ _ _ _ (inl1 _) (inl1 _))) =>
  simple apply RelGoal_sumPreRel_inl : refines.
Hint Extern 101 (RelGoal (sumPreRel _ _ _ _ (inl1 _) (ReSum_inl _ _ _ _ _ _ _))) =>
  apply RelGoal_sumPreRel_inl : refines.
Hint Extern 101 (RelGoal (sumPreRel _ _ _ _ (ReSum_inl _ _ _ _ _ _ _) (inl1 _))) =>
  apply RelGoal_sumPreRel_inl : refines.
Hint Extern 101 (RelGoal (sumPreRel _ _ _ _ (ReSum_inl _ _ _ _ _ _ _) (ReSum_inl _ _ _ _ _ _ _))) =>
  apply RelGoal_sumPreRel_inl : refines.
Hint Extern 101 (RelGoal (sumPreRel _ _ _ _ (inr1 _) (inr1 _))) =>
  simple apply RelGoal_sumPreRel_inr : refines.
Hint Extern 101 (RelGoal (sumPreRel _ _ _ _ (inr1 _) (ReSum_inr _ _ _ _ _ _ _))) =>
  apply RelGoal_sumPreRel_inr : refines.
Hint Extern 101 (RelGoal (sumPreRel _ _ _ _ (ReSum_inr _ _ _ _ _ _ _) (inr1 _))) =>
  apply RelGoal_sumPreRel_inr : refines.
Hint Extern 101 (RelGoal (sumPreRel _ _ _ _ (ReSum_inr _ _ _ _ _ _ _) (ReSum_inr _ _ _ _ _ _ _))) =>
  apply RelGoal_sumPreRel_inr : refines.

Lemma RelGoal_sumPostRel_inl E1 E2 F1 F2 (RPreE : PostRel E1 E2) (RPreF : PostRel F1 F2)
                              A B e1 e2 a b :
  RelGoal (RPreE A B e1 e2 a b) ->
  RelGoal (@sumPostRel E1 E2 F1 F2 RPreE RPreF A B (inl1 e1) (inl1 e2) a b).
Proof. constructor; eauto. Qed.
Lemma RelGoal_sumPostRel_inr E1 E2 F1 F2 (RPreE : PostRel E1 E2) (RPreF : PostRel F1 F2)
                              A B f1 f2 a b :
  RelGoal (RPreF A B f1 f2 a b) ->
  RelGoal (@sumPostRel E1 E2 F1 F2 RPreE RPreF A B (inr1 f1) (inr1 f2) a b).
Proof. constructor; eauto. Qed.

Hint Extern 101 (RelGoal (sumPostRel _ _ _ _ (inl1 _) (inl1 _) _ _)) =>
  simple apply RelGoal_sumPostRel_inl : refines.
Hint Extern 101 (RelGoal (sumPostRel _ _ _ _ (inl1 _) (ReSum_inl _ _ _ _ _ _ _) _ _)) =>
  apply RelGoal_sumPostRel_inl : refines.
Hint Extern 101 (RelGoal (sumPostRel _ _ _ _ (ReSum_inl _ _ _ _ _ _ _) (inl1 _) _ _)) =>
  apply RelGoal_sumPostRel_inl : refines.
Hint Extern 101 (RelGoal (sumPostRel _ _ _ _ (ReSum_inl _ _ _ _ _ _ _) (ReSum_inl _ _ _ _ _ _ _) _ _)) =>
  apply RelGoal_sumPostRel_inl : refines.
Hint Extern 101 (RelGoal (sumPostRel _ _ _ _ (inr1 _) (inr1 _) _ _)) =>
  simple apply RelGoal_sumPostRel_inr : refines.
Hint Extern 101 (RelGoal (sumPostRel _ _ _ _ (inr1 _) (ReSum_inr _ _ _ _ _ _ _) _ _)) =>
  apply RelGoal_sumPostRel_inr : refines.
Hint Extern 101 (RelGoal (sumPostRel _ _ _ _ (ReSum_inr _ _ _ _ _ _ _) (inr1 _) _ _)) =>
  apply RelGoal_sumPostRel_inr : refines.
Hint Extern 101 (RelGoal (sumPostRel _ _ _ _ (ReSum_inr _ _ _ _ _ _ _) (ReSum_inr _ _ _ _ _ _ _) _ _)) =>
  apply RelGoal_sumPostRel_inr : refines.

Lemma RelGoal_OnCallPreRel_i A1 A2 R1 R2
      (precond : A1 -> A2 -> Prop)  a1 a2 :
  RelGoal (precond a1 a2) ->
  RelGoal (OnCallPreRel A1 A2 R1 R2 precond R1 R2 (Call a1) (Call a2)).
Proof. constructor; eauto. Qed.

Hint Extern 101 (RelGoal (OnCallPreRel _ _ _ _ _ _ _ (Call _) (Call _))) =>
  simple apply RelGoal_OnCallPreRel_i : refines.

Lemma RelGoal_OnCallPostRel_i A1 A2 R1 R2
      (RR : R1 -> R2 -> Prop) (precond : A1 -> A2 -> Prop)
      (postcond : forall a1 a2, precond a1 a2 -> forall (r1 : R1) (r2 : R2), RR r1 r2 -> Prop)
      a1 a2 r1 r2 :
  forall (p0 : RelGoal (precond a1 a2)) (p1 : RelGoal (RR r1 r2)),
  RelGoal (postcond a1 a2 p0 r1 r2 p1) ->
  RelGoal (OnCallPostRel A1 A2 R1 R2 RR precond postcond R1 R2 (Call a1) (Call a2) r1 r2).
Proof. econstructor; econstructor; eauto. Qed.

Hint Extern 101 (RelGoal (OnCallPostRel _ _ _ _ _ _ _ _ _ (Call _) (Call _) _ _)) =>
  simple apply RelGoal_OnCallPostRel_i : refines.

Lemma RelGoal_depProdRel {R1 R2} (RR1 : R1 -> R2 -> Prop) (RR2 : forall r1 r2, RR1 r1 r2 -> Prop) r1 r2 :
  forall (p1 : RelGoal (RR1 r1 r2)), RelGoal (RR2 r1 r2 p1) ->
  RelGoal (@depProdRel R1 R2 RR1 RR2 r1 r2).
Proof. econstructor; eauto. Qed.

Hint Extern 101 (RelGoal (depProdRel _ _ _ _)) =>
  simple apply RelGoal_depProdRel : refines.

Lemma RelGoal_eqPreRel_refl {E A e} :
  RelGoal (@eqPreRel E A A e e).
Proof. constructor. Qed.

Hint Extern 101 (RelGoal (eqPreRel _ _ _ _)) =>
  apply RelGoal_eqPreRel_refl : refines.


(** * Basic Refinement Hints *)

Definition padded_refines_ret_IntroArg E1 E2 R1 R2 RPre RPost RR r1 r2 :
  (RelGoal (RR r1 r2 : Prop)) ->
  @padded_refines E1 E2 R1 R2 RPre RPost RR (Ret r1) (Ret r2) :=
  padded_refines_ret E1 E2 R1 R2 RPre RPost RR r1 r2.

Hint Extern 102 (padded_refines _ _ _ (Ret _) (Ret _)) =>
  apply padded_refines_ret_IntroArg : refines.

Definition padded_refines_vis_IntroArg E1 E2 R1 R2 A B
        RPre RPost RR (e1 : E1 A) (e2 : E2 B)
        (k1 : A -> itree_spec E1 R1) (k2 : B -> itree_spec E2 R2) :
  (RelGoal (RPre A B e1 e2 : Prop)) ->
  (IntroArg Any A (fun a => IntroArg Any B (fun b =>
     IntroArg Hyp (RPost A B e1 e2 a b : Prop) (fun _ =>
       padded_refines RPre RPost RR (k1 a) (k2 b))))) ->
  padded_refines RPre RPost RR (Vis (Spec_vis e1) k1) (Vis (Spec_vis e2) k2) :=
  padded_refines_vis E1 E2 R1 R2 A B RPre RPost RR e1 e2 k1 k2.

Hint Extern 102 (padded_refines _ _ _ (Vis (Spec_vis _) _) (Vis (Spec_vis _) _)) =>
  apply padded_refines_vis_IntroArg : refines.
Hint Extern 102 (padded_refines _ _ _ (vis (Spec_vis _) _) (Vis (Spec_vis _) _)) =>
  apply padded_refines_vis_IntroArg : refines.
Hint Extern 102 (padded_refines _ _ _ (Vis (Spec_vis _) _) (vis (Spec_vis _) _)) =>
  apply padded_refines_vis_IntroArg : refines.
Hint Extern 102 (padded_refines _ _ _ (vis (Spec_vis _) _) (vis (Spec_vis _) _)) =>
  apply padded_refines_vis_IntroArg : refines.
Hint Extern 103 (padded_refines _ _ _ (vis _ _) (vis _ _)) =>
  apply padded_refines_vis_IntroArg : refines.

Definition padded_refines_exists_l_IntroArg E1 E2 R1 R2 A
      RPre RPost RR (phi : itree_spec E2 R2) (kphi : A -> itree_spec E1 R1) :
  (IntroArg Exists A (fun a => padded_refines RPre RPost RR (kphi a) phi)) ->
  padded_refines RPre RPost RR (Vis Spec_exists kphi) phi :=
  padded_refines_exists_l E1 E2 R1 R2 A RPre RPost RR phi kphi.
Definition padded_refines_forall_r_IntroArg E1 E2 R1 R2 A
      RPre RPost RR (phi : itree_spec E1 R1) (kphi : A -> itree_spec E2 R2) :
  (IntroArg Forall A (fun a => padded_refines RPre RPost RR phi (kphi a))) ->
  padded_refines RPre RPost RR phi (Vis Spec_forall kphi) :=
  padded_refines_forall_r E1 E2 R1 R2 A RPre RPost RR phi kphi.

Hint Extern 101 (padded_refines _ _ _ _ (Vis Spec_forall _)) =>
  simple apply padded_refines_forall_r_IntroArg : refines.
Hint Extern 101 (padded_refines _ _ _ _ (vis Spec_forall _)) =>
  apply padded_refines_forall_r_IntroArg : refines.
Hint Extern 101 (padded_refines _ _ _ (Vis Spec_exists _) _) =>
  simple apply padded_refines_exists_l_IntroArg : refines.
Hint Extern 101 (padded_refines _ _ _ (vis Spec_exists _) _) =>
  apply padded_refines_exists_l_IntroArg : refines.

Hint Extern 102 (padded_refines _ _ _ _ (Vis Spec_exists _)) =>
  unshelve (simple eapply padded_refines_exists_r); [shelve|] : refines.
Hint Extern 102 (padded_refines _ _ _ _ (vis Spec_exists _)) =>
  unshelve (eapply padded_refines_exists_r); [shelve|] : refines.
Hint Extern 102 (padded_refines _ _ _ (Vis Spec_forall _) _) =>
  unshelve (simple eapply padded_refines_forall_l); [shelve|] : refines.
Hint Extern 102 (padded_refines _ _ _ (vis Spec_forall _) _) =>
  unshelve (eapply padded_refines_forall_l); [shelve|] : refines.

Definition padded_refines_if_r_IntroArg E1 E2 RPre RPost R1 R2 RR t1 t2 t3 b :
  (IntroArg If (b = true) (fun _ => padded_refines RPre RPost RR t1 t2)) ->
  (IntroArg If (b = false) (fun _ => padded_refines RPre RPost RR t1 t3)) ->
  padded_refines RPre RPost RR t1 (if b then t2 else t3) :=
  padded_refines_if_r E1 E2 RPre RPost R1 R2 RR t1 t2 t3 b.
Definition padded_refines_if_l_IntroArg E1 E2 RPre RPost R1 R2 RR t1 t2 t3 b :
  (IntroArg If (b = true) (fun _ => padded_refines RPre RPost RR t1 t3)) ->
  (IntroArg If (b = false) (fun _ => padded_refines RPre RPost RR t2 t3)) ->
  padded_refines RPre RPost RR (if b then t1 else t2) t3 :=
  padded_refines_if_l E1 E2 RPre RPost R1 R2 RR t1 t2 t3 b.

Hint Extern 101 (padded_refines _ _ _ _ (if _ then _ else _)) =>
  apply padded_refines_if_r_IntroArg : refines.
Hint Extern 101 (padded_refines _ _ _ (if _ then _ else _) _) =>
  apply padded_refines_if_l_IntroArg : refines.

Hint Extern 101 (padded_refines _ _ _ _ ((if _ then _ else _) >>= _)) =>
  apply padded_refines_if_bind_r : refines.
Hint Extern 101 (padded_refines _ _ _ ((if _ then _ else _) >>= _) _) =>
  apply padded_refines_if_bind_l : refines.

Definition padded_refines_match_list_r_IntroArg E1 E2 RPre RPost R1 R2 RR A (t1 : itree_spec E1 R1)
      (t2 : A -> list A -> itree_spec E2 R2) (t3 : itree_spec E2 R2) xs :
  (IntroArg Any A (fun x => IntroArg Any (list A) (fun xs' =>
   IntroArg Match (xs = x :: xs') (fun _ => padded_refines RPre RPost RR t1 (t2 x xs'))))) ->
  (IntroArg Match (xs = nil) (fun _ => padded_refines RPre RPost RR t1 t3)) ->
  padded_refines RPre RPost RR t1 (match xs with | x :: xs' => t2 x xs' | nil => t3 end) :=
  padded_refines_match_list_r E1 E2 RPre RPost R1 R2 RR A t1 t2 t3 xs.
Definition padded_refines_match_list_l_IntroArg E1 E2 RPre RPost R1 R2 RR A (t3 : itree_spec E2 R2)
      (t1 : A -> list A -> itree_spec E1 R1) (t2 : itree_spec E1 R1) xs :
  (IntroArg Any A (fun x => IntroArg Any (list A) (fun xs' =>
   IntroArg Match (xs = x :: xs') (fun _ => padded_refines RPre RPost RR (t1 x xs') t3)))) ->
  (IntroArg Match (xs = nil) (fun _ => padded_refines RPre RPost RR t2 t3)) ->
  padded_refines RPre RPost RR (match xs with | x :: xs' => t1 x xs' | nil => t2 end) t3 :=
  padded_refines_match_list_l E1 E2 RPre RPost R1 R2 RR A t3 t1 t2 xs.

Hint Extern 101 (padded_refines _ _ _ _ (match _ with | _ :: _ => _ | nil => _ end)) =>
  apply padded_refines_match_list_r_IntroArg : refines.
Hint Extern 101 (padded_refines _ _ _ (match _ with | _ :: _ => _ | nil => _ end) _) =>
  apply padded_refines_match_list_l_IntroArg : refines.

Hint Extern 101 (padded_refines _ _ _ _ ((match _ with | _ :: _ => _ | nil => _ end) >>= _)) =>
  apply padded_refines_match_list_bind_r : refines.
Hint Extern 101 (padded_refines _ _ _ ((match _ with | _ :: _ => _ | nil => _ end) >>= _) _) =>
  apply padded_refines_match_list_bind_l : refines.

Definition padded_refines_match_pair_r_IntroArg E1 E2 RPre RPost R1 R2 RR A B
      (t1 : itree_spec E1 R1) (t2 : A -> B -> itree_spec E2 R2) pr :
  (IntroArg Any A (fun x => IntroArg Any B (fun y =>
   IntroArg Match (pr = (x, y)) (fun _ => padded_refines RPre RPost RR t1 (t2 x y))))) ->
  padded_refines RPre RPost RR t1 (match pr with | (x,y) => t2 x y end) :=
  padded_refines_match_pair_r E1 E2 RPre RPost R1 R2 RR A B t1 t2 pr.
Definition padded_refines_match_pair_l_IntroArg E1 E2 RPre RPost R1 R2 RR A B
      (t1 : A -> B -> itree_spec E1 R1) (t2 : itree_spec E2 R2) pr :
  (IntroArg Any A (fun x => IntroArg Any B (fun y =>
   IntroArg Match (pr = (x, y)) (fun _ => padded_refines RPre RPost RR (t1 x y) t2)))) ->
  padded_refines RPre RPost RR (match pr with | (x,y) => t1 x y end) t2 :=
  padded_refines_match_pair_l E1 E2 RPre RPost R1 R2 RR A B t1 t2 pr.

Hint Extern 101 (padded_refines _ _ _ _ (match _ with | (_,_) => _ end)) =>
  apply padded_refines_match_pair_r_IntroArg : refines.
Hint Extern 101 (padded_refines _ _ _ (match _ with | (_,_) => _ end) _) =>
  apply padded_refines_match_pair_l_IntroArg : refines.

Hint Extern 101 (padded_refines _ _ _ _ ((match _ with | (_,_) => _ end) >>= _)) =>
  apply padded_refines_match_pair_bind_r : refines.
Hint Extern 101 (padded_refines _ _ _ ((match _ with | (_,_) => _ end) >>= _) _) =>
  apply padded_refines_match_pair_bind_l : refines.

Hint Extern 101 (padded_refines _ _ _ _ (Ret _ >>= _)) =>
  simple apply padded_refines_ret_bind_r : refines.
Hint Extern 101 (padded_refines _ _ _ (Ret _ >>= _) _) =>
  simple apply padded_refines_ret_bind_l : refines.

Hint Extern 101 (padded_refines _ _ _ _ (ITree.trigger _ >>= _)) =>
  simple apply padded_refines_trigger_bind_r : refines.
Hint Extern 101 (padded_refines _ _ _ (ITree.trigger _ >>= _) _) =>
  simple apply padded_refines_trigger_bind_l : refines.

Hint Extern 101 (padded_refines _ _ _ _ (Vis _ _ >>= _)) =>
  simple apply padded_refines_vis_bind_r : refines.
Hint Extern 101 (padded_refines _ _ _ _ (vis _ _ >>= _)) =>
  apply padded_refines_vis_bind_r : refines.
Hint Extern 101 (padded_refines _ _ _ (Vis _ _ >>= _) _) =>
  simple apply padded_refines_vis_bind_l : refines.
Hint Extern 101 (padded_refines _ _ _ (vis _ _ >>= _) _) =>
  apply padded_refines_vis_bind_l : refines.

Hint Extern 101 (padded_refines _ _ _ _ ((_ >>= _) >>= _)) =>
  simple apply padded_refines_bind_bind_r : refines.
Hint Extern 101 (padded_refines _ _ _ ((_ >>= _) >>= _) _) =>
  simple apply padded_refines_bind_bind_l : refines.

Definition padded_refines_trigger_r E1 E2 R1 R2 RPre RPost RR phi e :
  padded_refines RPre RPost RR phi (Vis e (fun x => Ret x)) ->
  @padded_refines E1 E2 R1 R2 RPre RPost RR phi (ITree.trigger e) :=
  fun r => r.
Definition padded_refines_trigger_l E1 E2 R1 R2 RPre RPost RR phi e :
  padded_refines RPre RPost RR (Vis e (fun x => Ret x)) phi ->
  @padded_refines E1 E2 R1 R2 RPre RPost RR (ITree.trigger e) phi :=
  fun r => r.

Hint Extern 101 (padded_refines _ _ _ _ (ITree.trigger _)) =>
  simple apply padded_refines_trigger_r : refines.
Hint Extern 101 (padded_refines _ _ _ (ITree.trigger _) _) =>
  simple apply padded_refines_trigger_l : refines.

(* assert_spec _ := trigger _ ;; _ *)
Hint Extern 101 (padded_refines _ _ _ _ (assert_spec _)) =>
  apply padded_refines_trigger_bind_r : refines.
Hint Extern 101 (padded_refines _ _ _ (assert_spec _) _) =>
  apply padded_refines_trigger_bind_l : refines.
Hint Extern 101 (padded_refines _ _ _ _ (assert_spec _ >>= _)) =>
  apply padded_refines_bind_bind_r : refines.
Hint Extern 101 (padded_refines _ _ _ (assert_spec _ >>= _) _) =>
  apply padded_refines_bind_bind_l : refines.

(* assume_spec _ := trigger _ ;; _ *)
Hint Extern 101 (padded_refines _ _ _ _ (assume_spec _)) =>
  apply padded_refines_trigger_bind_r : refines.
Hint Extern 101 (padded_refines _ _ _ (assume_spec _) _) =>
  apply padded_refines_trigger_bind_l : refines.
Hint Extern 101 (padded_refines _ _ _ _ (assume_spec _ >>= _)) =>
  apply padded_refines_bind_bind_r : refines.
Hint Extern 101 (padded_refines _ _ _ (assume_spec _ >>= _) _) =>
  apply padded_refines_bind_bind_l : refines.

(* exists_spec _ := trigger _ *)
Hint Extern 101 (padded_refines _ _ _ _ (exists_spec _)) =>
  apply padded_refines_trigger_r : refines.
Hint Extern 101 (padded_refines _ _ _ (exists_spec _) _) =>
  apply padded_refines_trigger_l : refines.
Hint Extern 101 (padded_refines _ _ _ _ (exists_spec _ >>= _)) =>
  apply padded_refines_trigger_bind_r : refines.
Hint Extern 101 (padded_refines _ _ _ (exists_spec _ >>= _) _) =>
  apply padded_refines_trigger_bind_l : refines.

(* forall_spec _ := trigger _ *)
Hint Extern 101 (padded_refines _ _ _ _ (forall_spec _)) =>
  apply padded_refines_trigger_r : refines.
Hint Extern 101 (padded_refines _ _ _ (forall_spec _) _) =>
  apply padded_refines_trigger_l : refines.
Hint Extern 101 (padded_refines _ _ _ _ (forall_spec _ >>= _)) =>
  apply padded_refines_trigger_bind_r : refines.
Hint Extern 101 (padded_refines _ _ _ (forall_spec _ >>= _) _) =>
  apply padded_refines_trigger_bind_l : refines.


(** * Refinement Hints About Recursion *)

Definition WellFounded {A1} (a a2 : A1) := Prop.
Definition Precondition {A1 A2} (a1 : A1) (a2 : A2) := Prop.
Definition Postcondition {A1 A2 R1 R2 precond RR} (a1 : A1) (a2 : A2) (H : precond a1 a2)
                         (r1 : R1) (r2 : R2) (H0 : (RR r1 r2 : Prop)) := Prop.
Definition Continue (precond : Prop) (goal : Type) := (precond * goal)%type.

Hint Opaque WellFounded : refines prepostcond.
Hint Opaque Precondition : refines prepostcond.
Hint Opaque Postcondition : refines prepostcond.
Hint Opaque well_founded : refines prepostcond.
Hint Opaque Continue : refines prepostcond.

Lemma Continue_unfold precond goal :
  RelGoal precond -> goal -> Continue precond goal.
Proof. split; eauto. Qed.

Hint Extern 999 (WellFounded _ _) => shelve : prepostcond.
Hint Extern 999 (Precondition _ _) => shelve : prepostcond.
Hint Extern 999 (Postcondition _ _ _ _ _ _) => shelve : prepostcond.
Hint Extern 999 (well_founded _) => shelve : refines.
Hint Extern 999 (Continue _ _) => shelve : refines.

Definition padded_refines_rec_IntroArg
           E1 E2 A1 A2 R1 R2 RPre RPost (RR : R1 -> R2 -> Prop) body1 body2 a1 a2
           (precond : IntroArg Any A1 (fun a1 => IntroArg Any A2 (fun a2 => Precondition a1 a2)))
           (postcond : IntroArg Any A1 (fun a1 => IntroArg Any A2 (fun a2 =>
                       IntroArg Hyp (precond a1 a2) (fun H =>
                       IntroArg RetAny R1 (fun r1 => IntroArg RetAny R2 (fun r2 =>
                       IntroArg Hyp (RR r1 r2) (fun H0 => Postcondition a1 a2 H r1 r2 H0))))))) :
  Continue (precond a1 a2)
           (IntroArg Any A1 (fun a1 => IntroArg Any A2 (fun a2 =>
            IntroArg Hyp (precond a1 a2) (fun p =>
            padded_refines (sumPreRel _ RPre)
                           (sumPostRel _ RPost)
                           (depProdRel RR (postcond a1 a2 p))
                           (body1 a1) (body2 a2))))) ->
  padded_refines RPre RPost RR (mrec_spec (calling' body1) (Call a1))
                             (mrec_spec (calling' body2) (Call a2)) := fun pr =>
  match pr with
  | (p, q) => padded_refines_rec E1 E2 A1 A2 R1 R2 RPre RPost RR precond postcond body1 body2 a1 a2 p q
  end.

Ltac padded_refines_rec := eapply padded_refines_rec_IntroArg.

Hint Extern 101 (padded_refines _ _ _ (mrec_spec (calling' _) (Call _))
                                      (mrec_spec (calling' _) (Call _))) =>
  padded_refines_rec : refines.
Hint Extern 101 (padded_refines _ _ _ (rec_spec _ _) (rec_spec _ _)) =>
  padded_refines_rec : refines.
Hint Extern 101 (padded_refines _ _ _ (rec_fix_spec _ _) (rec_fix_spec _ _)) =>
  padded_refines_rec : refines.

Definition padded_refines_total_spec_IntroArg
           E1 E2 A1 A2 R1 R2 RPre RPost (RR : R1 -> R2 -> Prop) body1 a1 a2 Pre Post
           (precond : IntroArg Any A1 (fun a1 => IntroArg Any A2 (fun a2 => Precondition a1 a2)))
           (postcond : IntroArg Any A1 (fun a1 => IntroArg Any A2 (fun a2 =>
                       IntroArg Hyp (precond a1 a2) (fun H =>
                       IntroArg RetAny R1 (fun r1 => IntroArg RetAny R2 (fun r2 =>
                       IntroArg Hyp (RR r1 r2) (fun H0 => Postcondition a1 a2 H r1 r2 H0)))))))
           (rdec : IntroArg Any A2 (fun a1 => IntroArg Any A2 (fun a2 => WellFounded a1 a2))) :
  well_founded rdec ->
  Continue (precond a1 a2)
           (IntroArg Any A1 (fun a1 => IntroArg Any A2 (fun a2 =>
            IntroArg Hyp (precond a1 a2) (fun p =>
            padded_refines (sumPreRel _ RPre)
                           (sumPostRel _ RPost)
                           (depProdRel RR (postcond a1 a2 p))
                           (body1 a1) (total_spec_fix_body _ _ _ Pre Post rdec a2))))) ->
  padded_refines RPre RPost RR (mrec_spec (calling' body1) (Call a1))
                             (total_spec Pre Post a2) := fun pf pr =>
  match pr with
  | (p, q) => padded_refines_total_spec E1 E2 A1 A2 R1 R2 RPre RPost RR precond postcond body1 Pre Post rdec a1 a2 pf p q
  end.

Ltac padded_refines_total_spec :=
  eapply padded_refines_total_spec_IntroArg;
  unfold total_spec_fix_body.

Hint Extern 101 (padded_refines _ _ _ (mrec_spec (calling' _) (Call _)) (total_spec _ _ _)) =>
  padded_refines_total_spec : refines.
Hint Extern 101 (padded_refines _ _ _ (rec_spec _ _) (total_spec _ _ _)) =>
  padded_refines_total_spec : refines.
Hint Extern 101 (padded_refines _ _ _ (rec_fix_spec _ _) (total_spec _ _ _)) =>
  padded_refines_total_spec : refines.

Hint Extern 101 (padded_refines _ _ _ (call_spec _) (call_spec _)) =>
  apply padded_refines_trigger_l, padded_refines_trigger_r : refines.
Hint Extern 101 (padded_refines _ _ _ _ (call_spec _ >>= _)) =>
  apply padded_refines_trigger_bind_r : refines.
Hint Extern 101 (padded_refines _ _ _ (call_spec _ >>= _) _) =>
  apply padded_refines_trigger_bind_l : refines.

Hint Extern 991 (padded_refines _ _ _ (Vis (Spec_vis (inl1 (Call _))) _) (trepeat _ _)) =>
  simple apply padded_refines_trepeat_suc_r : refines.
Hint Extern 991 (padded_refines _ _ _ (vis (Spec_vis (inl1 (Call _))) _) (trepeat _ _)) =>
  simple apply padded_refines_trepeat_suc_r : refines.
Hint Extern 991 (padded_refines _ _ _ (Vis (Spec_vis (inl1 (Call _))) _) (trepeat _ _ >>= _)) =>
  simple apply padded_refines_trepeat_bind_suc_r : refines.
Hint Extern 991 (padded_refines _ _ _ (vis (Spec_vis (inl1 (Call _))) _) (trepeat _ _ >>= _)) =>
  simple apply padded_refines_trepeat_bind_suc_r : refines.

Hint Extern 992 (padded_refines _ _ _ _ (trepeat _ _)) =>
  simple apply padded_refines_trepeat_zero_r : refines.
Hint Extern 992 (padded_refines _ _ _ _ (trepeat _ _ >>= _)) =>
  simple apply padded_refines_trepeat_bind_zero_r : refines.

Hint Extern 101 (padded_refines _ _ _ (total_spec _ _ _) _) =>
  unfold total_spec at 1 : refines.
Hint Extern 101 (padded_refines _ _ _ (total_spec _ _ _ >>= _) _) =>
  unfold total_spec at 1 : refines.


(** * Tactics *)

Ltac prove_refinement_eauto :=
  unshelve (typeclasses eauto with refines).

Ltac prove_refinement_prepostcond :=
  try (unshelve (typeclasses eauto with prepostcond)).

Ltac prove_refinement :=
  prove_refinement_eauto; prove_refinement_prepostcond.

Ltac prove_refinement_continue :=
  apply Continue_unfold; prove_refinement.


(** * Examples *)

Open Scope Z_scope.

Lemma test_ifs E x :
  @padded_refines E E _ _ eqPreRel eqPostRel eq
                  (if x >=? 0 then if x <? 256 then Ret 1 else Ret 0 else Ret 0)
                  (if x <? 256 then if x >=? 0 then Ret 1 else Ret 0 else Ret 0).
Proof.
  prove_refinement.
Qed.

Lemma test_spins E (x : Z) :
  @padded_refines E E Z Z eqPreRel eqPostRel eq
                  (rec_fix_spec (fun rec a => rec a) x)
                  (rec_fix_spec (fun rec a => rec a) x).
Proof.
  prove_refinement.
  - exact True.
  - exact True.
  - prove_refinement_continue.
Qed.

Lemma test_exists E (x : Z) :
  @padded_refines E E Z Z eqPreRel eqPostRel eq
                  (if x >=? 0 then Ret x else Ret (-1 * x))
                  (r <- exists_spec Z ;; Ret r).
Proof.
  prove_refinement.
Qed.

Lemma test_halve_refl E xs :
  padded_refines_eq eq (@halve E xs) (@halve E xs).
Proof.
  unfold padded_refines_eq, halve.
  prove_refinement.
  - exact (a = a0).
  - exact True.
  - prove_refinement_continue.
Qed.

Open Scope nat_scope.

Lemma halve_refines_spec E l :
  padded_refines_eq eq (@halve E l) (@halve_spec_fix E l).
Proof.
  unfold halve, halve_spec_fix, halve_spec.
  prove_refinement.
  - exact (a = a0).
  - exact ((Permutation a (fst r ++ snd r)) /\
           (length (fst r) >= length (snd r) /\ (length a > length (fst r) \/ length a <= 1))).
  - prove_refinement_continue.
    all: cbn; cbn in *.
    all: try split; try easy; try lia.
    + rewrite Permutation_app_comm. cbn.
      rewrite H0. rewrite Permutation_app_comm. reflexivity.
    + rewrite H0. repeat rewrite app_length. lia.
    + rewrite Permutation_app_comm. cbn.
      rewrite H0. rewrite Permutation_app_comm. reflexivity.
    + repeat rewrite H0. repeat rewrite app_length. lia.
Qed.
