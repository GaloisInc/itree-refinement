
From Coq Require Export Morphisms RelationClasses Setoid Program.Equality.
From ITree Require Export ITree ITreeFacts Eq.Rutt Props.Finite.
From Paco Require Import paco.
From Coq Require Export Eqdep EqdepFacts Logic.Classical.
Require Import Lia.
Require Export HeterogeneousEventRelations Refinement ConcreteRefinement ConvergentRefinement.

Import Monads.
Import MonadNotation.
Local Open Scope monad_scope.
Locate MonadNotation.
Open Scope list_scope.


(** * rec_fix_spec *)

Definition call_spec {E A B} (a : A) : itree_spec (callE A B +' E) B :=
  ITree.trigger (Spec_vis (inl1 (Call a))).

Definition rec_spec {E A B} (body : A -> itree_spec (callE A B +' E) B) (a : A) :
  itree_spec E B :=
  mrec_spec (calling' body) (Call a).

Definition rec_fix_spec {E A B}
(body : (A -> itree_spec (callE A B +' E) B) ->
        A -> itree_spec (callE A B +' E) B)  :
  A -> itree_spec E B := rec_spec (body call_spec).


(** * assert_spec, assume_spec, exists_spec, forall_spec *)

Definition assert_spec {E} (P : Type) : itree_spec E unit :=
  trigger (@Spec_exists E P);; Ret tt.

Lemma padded_assert_pad_elim {E1 E2} RPre RPost R1 R2 RR P
      (phi : itree_spec E1 R1) (kphi : unit -> itree_spec E2 R2) :
  P -> padded_refines RPre RPost RR phi (kphi tt) ->
  padded_refines RPre RPost RR phi (ITree.bind (assert_spec P) kphi).
Proof.
  intros. setoid_rewrite bind_trigger.
  unfold padded_refines in *. rewrite pad_bind, pad_vis.
  setoid_rewrite pad_ret. rewrite bind_vis. setoid_rewrite bind_tau.
  setoid_rewrite bind_ret_l. pstep. constructor. auto. constructor. pstep_reverse.
Qed.

Lemma padded_assert_pad_eliml {E1 E2} RPre RPost R1 R2 RR P
      (phi : itree_spec E1 R1) (kphi : unit -> itree_spec E2 R2) :
  (P -> padded_refines RPre RPost RR (kphi tt) phi) ->
  padded_refines RPre RPost RR (ITree.bind (assert_spec P) kphi) phi.
Proof.
  intros. setoid_rewrite bind_trigger.
  unfold padded_refines in *. rewrite pad_bind, pad_vis.
  setoid_rewrite pad_ret. rewrite bind_vis. setoid_rewrite bind_tau.
  setoid_rewrite bind_ret_l. pstep. constructor.
  intros HP. specialize (H HP). constructor. pstep_reverse.
Qed.

Definition assume_spec {E} (P : Type) : itree_spec E unit :=
  trigger (@Spec_forall E P);; Ret tt.

Lemma padded_assume_pad_elim {E1 E2} RPre RPost R1 R2 RR P
      (phi : itree_spec E1 R1) (kphi : unit -> itree_spec E2 R2) :
  (P -> padded_refines RPre RPost RR phi (kphi tt)) ->
  padded_refines RPre RPost RR phi (ITree.bind (assume_spec P) kphi).
Proof.
  intros. setoid_rewrite bind_trigger.
  unfold padded_refines in *. rewrite pad_bind, pad_vis.
  setoid_rewrite pad_ret. rewrite bind_vis. setoid_rewrite bind_tau.
  setoid_rewrite bind_ret_l. pstep. constructor.
  intros HP. specialize (H HP). constructor. pstep_reverse.
Qed.

Lemma padded_assume_pad_eliml {E1 E2} RPre RPost R1 R2 RR P
      (phi : itree_spec E1 R1) (kphi : unit -> itree_spec E2 R2) :
  P -> padded_refines RPre RPost RR (kphi tt) phi ->
  padded_refines RPre RPost RR (ITree.bind (assume_spec P) kphi) phi.
Proof.
  intros. setoid_rewrite bind_trigger.
  unfold padded_refines in *. rewrite pad_bind, pad_vis.
  setoid_rewrite pad_ret. rewrite bind_vis. setoid_rewrite bind_tau.
  setoid_rewrite bind_ret_l. pstep. constructor. auto. constructor. pstep_reverse.
Qed.

Definition exists_spec {E} (T : Type) : itree_spec E T :=
  trigger (@Spec_exists E T).

(**)
Lemma exists_spec_elim {E1 E2} S1 R2 S2 RPre RPost RR (phi : itree_spec E1 S1)
      (kphi : R2 -> itree_spec E2 S2) r :
  refines RPre RPost RR phi (kphi r) ->
  refines RPre RPost RR phi (ITree.bind (exists_spec R2) kphi).
Proof.
  intros. unfold exists_spec. setoid_rewrite bind_trigger.
  pstep. econstructor. pstep_reverse.
Qed.

(*maybe there is a simpler way to derive this proof from the previous one*)
Lemma padded_exists_spec_elim {E1 E2} S1 R2 S2 RPre RPost RR (phi : itree_spec E1 S1)
      (kphi : R2 -> itree_spec E2 S2) r :
  padded_refines RPre RPost RR phi (kphi r) ->
  padded_refines RPre RPost RR phi (ITree.bind (exists_spec R2) kphi).
Proof.
  intros.  unfold padded_refines in *. rewrite pad_bind. setoid_rewrite pad_vis.
  rewrite bind_vis.
  setoid_rewrite pad_ret. setoid_rewrite bind_tau. setoid_rewrite bind_ret_l.
  pstep. econstructor. Unshelve. all : auto. constructor. pstep_reverse.
Qed.

Lemma padded_exists_spec_eliml {E1 E2} S1 R2 S2 RPre RPost RR (phi : itree_spec E1 S1)
      (kphi : R2 -> itree_spec E2 S2) :
  (forall r, padded_refines RPre RPost RR (kphi r) phi) ->
  padded_refines RPre RPost RR (ITree.bind (exists_spec R2) kphi) phi .
Proof.
  intros.  unfold padded_refines in *. rewrite pad_bind. setoid_rewrite pad_vis.
  rewrite bind_vis.
  setoid_rewrite pad_ret. setoid_rewrite bind_tau. setoid_rewrite bind_ret_l.
  pstep. econstructor. intros. constructor. pstep_reverse. apply H.
Qed.

Ltac existssr a := apply padded_exists_spec_elim with (r := a).

Ltac eexistssr := eapply padded_exists_spec_elim.

Ltac existssl := apply padded_exists_spec_eliml.

Ltac assumesr := apply padded_assume_pad_elim.
Ltac assumesl := apply padded_assume_pad_eliml.
Ltac assertsr := apply padded_assert_pad_elim.
Ltac assertsl := apply padded_assert_pad_eliml.

Lemma conv_ref_exists_spec E R :
  @conv_ref E R (exists_spec R).
Proof.
  pstep. red. cbn. constructor.
  intros. left. pstep. constructor.
Qed.

Definition forall_spec {E} (T : Type) : itree_spec E T :=
  trigger (@Spec_forall E T).

Lemma forall_spec_elim {E1 E2} S1 R2 S2 RPre RPost RR (phi : itree_spec E1 S1)
      (kphi : R2 -> itree_spec E2 S2) :
  (forall r, refines RPre RPost RR phi (kphi r)) ->
  refines RPre RPost RR phi (ITree.bind (forall_spec R2) kphi).
Proof.
  intros. unfold forall_spec. rewrite bind_trigger.
  pstep. constructor. intros. pstep_reverse. apply H.
Qed.

Lemma padded_forall_spec_elim {E1 E2} S1 R2 S2 RPre RPost RR (phi : itree_spec E1 S1)
      (kphi : R2 -> itree_spec E2 S2):
  (forall r, padded_refines RPre RPost RR phi (kphi r)) ->
  padded_refines RPre RPost RR phi (ITree.bind (forall_spec R2) kphi).
Proof.
  intros.  unfold padded_refines in *. rewrite pad_bind. setoid_rewrite pad_vis.
  rewrite bind_vis.
  setoid_rewrite pad_ret. setoid_rewrite bind_tau. setoid_rewrite bind_ret_l.
  pstep. constructor. intros.  constructor. pstep_reverse.
  apply H.
Qed.

Lemma padded_forall_spec_eliml {E1 E2} S1 R2 S2 RPre RPost RR (phi : itree_spec E1 S1)
      (kphi : R2 -> itree_spec E2 S2) r:
  padded_refines RPre RPost RR (kphi r) phi ->
  padded_refines RPre RPost RR (ITree.bind (forall_spec R2) kphi) phi.
Proof.
  intros.  unfold padded_refines in *. rewrite pad_bind. setoid_rewrite pad_vis.
  rewrite bind_vis.
  setoid_rewrite pad_ret. setoid_rewrite bind_tau. setoid_rewrite bind_ret_l.
  pstep. econstructor. constructor. pstep_reverse.
Qed.


(** * padded_refines_eq *)

Definition padded_refines_eq {E R1 R2} RR (phi1 : itree_spec E R1) (phi2 : itree_spec E R2) :=
  padded_refines eqPreRel eqPostRel RR phi1 phi2.

Global Instance padded_refines_eq_refl {E R} : Reflexive (@padded_refines_eq E R R eq).
Proof.
  red. intros. unfold padded_refines_eq, padded_refines. apply refl_refines; auto.
  - red. intros. constructor.
  - red. intros. inv H. inj_existT. subst. auto.
  - apply pad_is_padded.
Qed.

Global Instance refines_proper_bind E R S :
  Proper (@padded_refines_eq E R R eq ==> pointwise_relation _ (padded_refines_eq eq) ==> @padded_refines_eq E S S eq) ITree.bind.
Proof.
  repeat intro. subst. unfold padded_refines_eq in *. eapply padded_refines_bind; eauto.
  intros; subst. auto.
Qed.

Global Instance refines_proper_subst E R S (k : R -> itree_spec E S) :
  Proper (@padded_refines_eq E R R eq ==> padded_refines_eq eq) (ITree.subst k).
Proof.
  repeat intro. eapply refines_proper_bind. auto. intro. reflexivity.
Qed.

Global Instance refines_proper_bind_eq E R S :
  Proper (@padded_refines_eq E R R eq ==> eq ==> @padded_refines_eq E S S eq) ITree.bind.
Proof.
  repeat intro. eapply refines_proper_bind. auto. subst. intro. reflexivity.
Qed.

Global Instance  padded_refines_eq_gen E1 E2 R1 R2 RPre RPost RR :
  Proper (padded_refines_eq eq ==> flip (padded_refines_eq eq) ==> flip impl)
         (@padded_refines E1 E2 R1 R2 RPre RPost RR).
Proof.
  intros t1 t2 Ht12 t3 t4 Ht43. red in Ht43. intro.
  unfold padded_refines_eq, padded_refines in *. rename H into H24.
  specialize @refinesTrans with (E1 := E1) (E2 := E1) (E3 := E2) (RPre1 := eqPreRel) (RPre2 := RPre) as Htrans.
  eapply Htrans in Ht12; eauto; try apply pad_is_padded. clear Htrans.
  specialize @refinesTrans with (E1 := E1) (E2 := E2) (E3 := E2) (RPre1 := rcomposePreRel eqPreRel RPre) (RPre2 := eqPreRel) as Htrans.
  eapply Htrans in Ht12; eauto; try apply pad_is_padded. eapply refines_monot; try eapply Ht12.
  { intros. destruct PR. destruct H. eqPreRel_inv H. eqPreRel_inv H0. auto. }
  { intros. econstructor. intros. destruct H. eqPreRel_inv H0.
    inv H. inj_existT. subst. eqPreRel_inv H4. exists x1. split. 2 : constructor.
    constructor. intros. destruct H. eqPreRel_inv H. exists x0. split; auto. constructor.
  }
  { intros. inv PR. inv REL1. auto. }
Qed.

Global Instance padded_refines_eq_trans {E R} : Transitive (@padded_refines_eq E R R eq).
Proof.
  intros phi1 phi2 phi3 Hphi12 Hphi23. unfold padded_refines_eq, padded_refines in *.
  eapply refines_monot; try eapply refinesTrans; eauto with solve_padded; try apply pad_is_padded.
  - intros A B ea eb PR. assert (A = B). inv PR. inv H3. inv H4. auto. subst.
    assert (ea = eb). inv PR. inj_existT.
    subst. assert (B = B0). inv H3. auto. subst. inv H4. inj_existT. subst. inv H3. inj_existT.
    subst. auto. subst. constructor.
  - intros.
    assert (A = B). inv PR. auto. subst. assert (ea = eb). inv PR. inj_existT. subst. auto.
    subst. constructor. intros. destruct H. assert (x0 = x1). inv PR. inj_existT. subst. auto.
    subst. assert (B = B0). inv H. auto. subst. exists x1.
    assert (e2 = eb). inv H. inj_existT. subst. auto. subst. repeat constructor.
  - intros. inv PR. auto.
Qed.

Global Instance refines_proper_interp_mrec_spec E D R :
  Proper ((fun ctx1 ctx2 => forall T d, padded_refines_eq  eq (ctx1 T d) (ctx2 T d)) ==> @padded_refines_eq (D +' E) R R eq ==> @padded_refines_eq E R R eq)
         (fun ctx => @interp_mrec_spec D E ctx R).
Proof.
  repeat intro. subst. unfold padded_refines_eq in *.
  eapply padded_refines_interp_mrec with (RPreInv := eqPreRel) (RPostInv := eqPostRel) ; eauto.
  - intros.
    eqPreRel_inv H1.
    eapply refines_monot; try eapply H.
    + intros.  eqPreRel_inv PR. destruct x2; repeat constructor.
    + intros. inv PR; inj_existT; subst; eqPostRel_inv H7; constructor.
    + intros. subst. constructor.
  - eapply refines_monot; try eapply H0.
    + intros. eqPreRel_inv PR. destruct x2; repeat constructor.
    + intros. inv PR; inj_existT; subst; eqPostRel_inv H7; constructor.
    + auto.
Qed.

Global Instance refines_proper_interp_mrec_spec_eq E D R :
  Proper (eq ==> @padded_refines_eq (D +' E) R R eq ==> @padded_refines_eq E R R eq)
         (fun ctx => @interp_mrec_spec D E ctx R).
Proof.
  repeat intro.
  apply refines_proper_interp_mrec_spec; auto.
  intros. subst. reflexivity.
Qed.

(*
Global Instance padded_refines_eq_bind_proper  E1 E2 RPre RPost R1 R2 RR :
  Proper (padded_refines_eq eq ==> eq ==> @padded_refines E1 E2 R1 R2 RPre RPost RR) ITree.bind.
*)
(*from there there is a bit more *)

(*need at least bind and ret rules for interp_mrec_spec *)


(** * more lemmas about interp_mrec *)

Lemma interp_mrec_ret :
  forall {D E : Type -> Type} (ctx : forall T : Type, D T -> itree (D +' E) T) R (r :R),
    interp_mrec ctx (Ret r) ≅ Ret r.
Proof.
  intros. setoid_rewrite unfold_iter. cbn. rewrite bind_ret_l. reflexivity.
Qed.

Lemma interp_mrec_exists_spec E D T (ctx : forall T, D T -> itree_spec (D +' E) T) :
  interp_mrec_spec ctx (exists_spec T) ≈ exists_spec T.
Proof.
  setoid_rewrite interp_mrec_spec'_exists.
  cbn. apply eqit_Vis. intros.  pstep. red. cbn. constructor. auto.
Qed.

Lemma interp_mrec_forall_spec E D T (ctx : forall T, D T -> itree_spec (D +' E) T) :
  interp_mrec_spec ctx (forall_spec T) ≈ forall_spec T.
Proof.
  setoid_rewrite interp_mrec_spec'_forall.
  cbn. apply eqit_Vis. intros.  pstep. red. cbn. constructor. auto.
Qed.

Lemma interp_mrec_spec_assume E D T (ctx : forall T, D T -> itree_spec (D +' E) T) :
  interp_mrec_spec ctx (assume_spec T) ≈ assume_spec T.
Proof.
  cbn. setoid_rewrite interp_mrec_spec_bind.
  setoid_rewrite interp_mrec_spec'_forall. rewrite bind_vis, bind_trigger.
  apply eqit_Vis. intros. setoid_rewrite interp_mrec_spec_ret. rewrite bind_ret_l.
  reflexivity.
Qed.

Lemma interp_mrec_spec_assert E D T (ctx : forall T, D T -> itree_spec (D +' E) T) :
  interp_mrec_spec ctx (assert_spec T) ≈ assert_spec T.
Proof.
  cbn. setoid_rewrite interp_mrec_spec_bind.
  setoid_rewrite interp_mrec_spec'_exists. rewrite bind_vis, bind_trigger.
  apply eqit_Vis. intros. setoid_rewrite interp_mrec_spec_ret. rewrite bind_ret_l.
  reflexivity.
Qed.

Ltac normalize_interp_mrec_spec :=
  match goal with
  | |- context [ITree.bind (ITree.bind ?t ?k1) ?k2 ] => setoid_rewrite bind_bind
  | |- context [interp_mrec_spec ?ctx (ITree.bind ?t ?k) ] => setoid_rewrite interp_mrec_spec_bind
  | |- context [interp_mrec_spec ?ctx (exists_spec ?T) ] => setoid_rewrite interp_mrec_exists_spec
  | |- context [interp_mrec_spec ?ctx (forall_spec ?T) ] => setoid_rewrite interp_mrec_forall_spec
  | |- context [interp_mrec_spec ?ctx (assert_spec ?T) ] => setoid_rewrite interp_mrec_spec_assert
  | |- context [interp_mrec_spec ?ctx (assume_spec ?T) ] => setoid_rewrite interp_mrec_spec_assume
  end.


(** * or_spec, and_spec *)

Lemma or_spec_l E1 E2 RPre RPost R1 R2 RR (t1 t2 : itree_spec E1 R1) (t3 : itree_spec E2 R2) :
  @padded_refines E1 E2 R1 R2 RPre RPost RR t1 t3 ->
  @padded_refines E1 E2 R1 R2 RPre RPost RR t2 t3 ->
  @padded_refines E1 E2 R1 R2 RPre RPost RR (or_spec t1 t2) t3.
Proof.
  intros. unfold or_spec. unfold padded_refines in *.
  rewrite pad_vis. pstep. constructor. intros [ | ]; constructor; pstep_reverse.
Qed.

Lemma or_spec_r E1 E2 RPre RPost R1 R2 RR (t1 : itree_spec E1 R1) (t2 t3: itree_spec E2 R2) :
  (@padded_refines E1 E2 R1 R2 RPre RPost RR t1 t2 \/
  @padded_refines E1 E2 R1 R2 RPre RPost RR t1 t3) ->
  @padded_refines E1 E2 R1 R2 RPre RPost RR t1 (or_spec t2 t3).
Proof.
  intros. unfold or_spec. unfold padded_refines in *.
  rewrite pad_vis. pstep.
  destruct H.
  - econstructor. constructor. Unshelve. all : try (apply true). pstep_reverse.
  - econstructor. constructor. Unshelve. all : try (apply false). pstep_reverse.
Qed.

Lemma interp_mrec_spec_or  (E : Type -> Type) (R : Type) (D : Type -> Type) (ctx : forall T : Type, D T -> itree_spec (D +' E) T)
  (t1 t2 : itree_spec _ R)
  : interp_mrec_spec ctx (or_spec t1 t2) ≅ or_spec (interp_mrec_spec ctx t1) (interp_mrec_spec ctx t2).
Proof.
  setoid_rewrite interp_mrec_spec'_exists. apply eqit_Vis. intros [ | ]; reflexivity.
Qed.

(*should be able to generalize this to cany concrete tree *)
Lemma or_spec_r_Ret_inv E1 E2 R1 R2 RPre RPost RR r t2 t3 :
  @padded_refines E1 E2 R1 R2 RPre RPost RR (Ret r) (or_spec t2 t3) ->
  padded_refines RPre RPost RR (Ret r) t2 \/ padded_refines RPre RPost RR (Ret r) t3.
Proof.
  intros Hor. unfold padded_refines in *. setoid_rewrite pad_ret in Hor.
  setoid_rewrite pad_ret. setoid_rewrite pad_vis in Hor.
  pinversion Hor. inj_existT. subst. inv H1. destruct a.
  - left. pstep. auto.
  - right. pstep. auto.
Qed.

Lemma or_spec_bind_l  E1 E2 R1 S R2 RPre RPost RR (t1 t2 : itree_spec E1 S) (k : S -> itree_spec E1 R1) (t3 : itree_spec E2 R2) :
  padded_refines RPre RPost RR (ITree.bind t1 k) t3 ->
  padded_refines RPre RPost RR (ITree.bind t2 k) t3 ->
  padded_refines RPre RPost RR (ITree.bind (or_spec t1 t2) k) t3.
Proof.
  unfold padded_refines. intros. setoid_rewrite bind_vis. setoid_rewrite pad_vis.
  pstep. constructor. intros [ | ]; constructor; pstep_reverse.
Qed.


(** * spin *)

Lemma spin_bind E R S k : (@ITree.spin E R) >>= k ≅ @ITree.spin E S.
Proof.
  ginit. gcofix CIH. gstep. red. cbn. constructor.
  gfinal. eauto.
Qed.

Lemma interp_mrec_spec_spin (E : Type -> Type) (R : Type) (D : Type -> Type) (ctx : forall T : Type, D T -> itree_spec (D +' E) T) :
  interp_mrec_spec ctx ITree.spin ≅ @ITree.spin _ R.
Proof.
  pcofix CIH. pstep. red. cbn. constructor.
  right. eauto.
Qed.


(** * total_spec, partial_spec *)

Lemma padded_refines_ret E1 E2 R1 R2 RPre RPost RR r1 r2 :
  (RR r1 r2 : Prop) ->
  @padded_refines E1 E2 R1 R2 RPre RPost RR (Ret r1) (Ret r2).
Proof.
  intros Hr. red. repeat rewrite pad_ret. pstep. constructor. auto.
Qed.

Fixpoint trepeat {E R} (n : nat) (t : itree E R) : itree E unit :=
  match n with
  | 0 => Ret tt
  | S m => t;; trepeat m t end.

Lemma trepeat_Sn E R (n : nat) (t : itree E R) :
  trepeat (S n) t ≅ t;; trepeat n t.
Proof.
  apply eqit_bind; reflexivity.
Qed.

Lemma trepeat_0 E R (t : itree E R) :
  trepeat 0 t ≅ Ret tt.
Proof. reflexivity. Qed.

Section SpecFix.
  Context {A B: Type} {E : Type -> Type}.
  Context (Pre : A -> Prop) (Post : A -> B -> Prop).
  Context (prog : A -> itree_spec E B).

  Context (Rdec : A -> A -> Prop).
  Context (HRdec : well_founded Rdec).

  Context (Hprog : forall a, isConcrete (prog a)).
  Variant pre_call : forall C, callE A B C -> Prop :=
    | pre_call_intro (a : A) : Pre a -> pre_call B (Call a).
  Variant post_call : forall C, callE A B C -> C -> Prop :=
    | post_call_intro a b : Post a b -> post_call B (Call a) b.

  Definition total_spec (a : A) : itree_spec E B :=
    assume_spec (Pre a);;
    b <- exists_spec B;;
    assert_spec (Post a b);;
    Ret b.

  (* better for using as a final spec *)
  Definition partial_spec (a : A) : itree_spec E B :=
    or_spec (total_spec a) ITree.spin.
  (* better for syntax driven solving *)
  (**)

  Definition partial_spec_fix : A -> itree_spec E B :=
    rec_fix_spec (fun rec a =>
                    assume_spec (Pre a);;
                    (
                      n <- exists_spec nat;;
                      trepeat n (a' <- exists_spec A;; assert_spec (Pre a');; rec a')
                    );;
                    b <- exists_spec B;;
                    assert_spec (Post a b);;
                    Ret b
                 ).

  Definition partial_spec_fix' : A -> itree_spec E B :=
    rec_fix_spec (fun rec a =>
                        assume_spec (Pre a);;
                        (
                          n <- exists_spec nat;;
                          trepeat n (a' <- exists_spec A;; assert_spec (Pre a');; rec a')
                        );;
                        or_spec (
                            b <- exists_spec B;;
                            assert_spec (Post a b);;
                            Ret b)
                        ITree.spin
                 ).


  Definition total_spec_fix : A -> itree_spec E B :=
    rec_fix_spec (fun rec a =>
                    assume_spec (Pre a);;
                    (
                      n <- exists_spec nat;;
                      trepeat n (a' <- exists_spec A;; assert_spec (Pre a' /\ Rdec a' a);; rec a')
                    );;
                    b <- exists_spec B;;
                    assert_spec (Post a b);;
                    Ret b
                 ).

  (* here would be a good place for proofs that partial_spec_fix' is greater than any of these
     from there I should be able to prove that total_spec_fix
   *)

  Lemma total_spec_fix_total a : padded_refines_eq eq (total_spec_fix a) (total_spec a).
  Proof.
    revert a.
    apply well_founded_ind with (R := Rdec). auto.
    intros a Hind. unfold total_spec_fix. simpl.
    setoid_rewrite interp_mrec_spec_bind.
    match goal with |- context [ interp_mrec_spec ?k _ ] => set k as body end.
    unfold total_spec. assumesr. intros Ha. setoid_rewrite interp_mrec_spec_assume.
    assumesl. auto. rewrite bind_bind.  setoid_rewrite interp_mrec_spec_bind.
    setoid_rewrite interp_mrec_exists_spec. existssl. intros n.
    induction n.
    - simpl. rewrite bind_ret_l. setoid_rewrite interp_mrec_spec_bind.
      setoid_rewrite interp_mrec_exists_spec.
      setoid_rewrite interp_mrec_spec_bind. setoid_rewrite interp_mrec_spec_assert.
      setoid_rewrite interp_mrec_spec_ret. reflexivity.
    - simpl. rewrite bind_bind. setoid_rewrite interp_mrec_spec_bind.
      setoid_rewrite IHn. setoid_rewrite interp_mrec_spec_bind.
      setoid_rewrite interp_mrec_exists_spec. rewrite bind_bind. existssl.
      intros a'. setoid_rewrite interp_mrec_spec_bind.
      setoid_rewrite interp_mrec_spec_assert. rewrite bind_bind. assertsl.
      intros [Hprea' Hdec]. simpl.
      assert (Htot : interp_mrec_spec body (call_spec a') ≈ total_spec_fix a').
      { unfold total_spec_fix, rec_fix_spec, rec_spec, mrec_spec .
        setoid_rewrite interp_mrec_spec_inl. rewrite tau_eutt. rewrite bind_ret_r.
        reflexivity. }
      rewrite Htot, Hind; auto. unfold total_spec.
      setoid_rewrite bind_bind at 1. assumesl. auto.
      setoid_rewrite bind_bind at 1. existssl. intros b.
      setoid_rewrite bind_bind at 1. assertsl. intros. rewrite bind_ret_l. reflexivity.
   Qed.


    Lemma partial_spec_fix_conv_ref :
    forall a, Pre a -> conv_ref (partial_spec_fix' a).
  Proof.
    intros a Ha.
    eapply conv_ref_mrec_conv_ref with (Pre := pre_call).
    constructor. auto.
    intros. inv H. inj_existT. subst.
    clear a Ha.
    rename a0 into a. rename H2 into Ha. clear H0. cbn.
    apply conv_ref_mrec_bind.  rewrite bind_trigger. apply conv_ref_mrec_forall.
    auto. intros. apply conv_ref_mrec_ret.
    intros []. rewrite bind_bind. apply conv_ref_mrec_bind.
    apply conv_ref_mrec_exists. intros. apply conv_ref_mrec_ret.
    intros n. induction n; cbn.
    - rewrite bind_ret_l. apply conv_ref_mrec_exists. intros [ | ].
      2 : apply conv_ref_mrec_spin. apply conv_ref_mrec_bind.
      + apply conv_ref_mrec_exists. intros. apply conv_ref_mrec_ret.
      + intros. rewrite bind_bind. setoid_rewrite bind_vis.
        apply conv_ref_mrec_exists. intros. repeat rewrite bind_ret_l.
        apply conv_ref_mrec_ret.
    - rewrite bind_bind. apply conv_ref_mrec_bind; intros; auto.
      apply conv_ref_mrec_bind.
      + apply conv_ref_mrec_exists. intros. apply conv_ref_mrec_ret.
      + intros. rewrite bind_bind. setoid_rewrite bind_vis.
        apply conv_ref_mrec_exists.
        intros. repeat rewrite bind_ret_l. pstep. red. cbn.
        constructor. constructor. auto. left.
        apply conv_ref_mrec_ret.
  Qed.

  Lemma prog_ret_spin : forall a, Pre a ->
                             padded_refines_eq eq (prog a) (partial_spec_fix' a) ->
                             (exists b, prog a ≈ Ret b) \/ (prog a ≈ ITree.spin).
  Proof.
    intros a Href Ha. apply no_ev_to_dec.
    eapply concrete_conv_ref_padded_to_no_ev; eauto.
    apply partial_spec_fix_conv_ref. auto.
  Qed.
    (* need a padded_refines version *)

(*   Lemma partial_spec_fix_partial_spec' a :
    (Pre a -> padded_refines_eq eq (prog a) (partial_spec_fix' a)) ->
    padded_refines_eq eq (prog a) (partial_spec a). *)


  Lemma partial_spec_fix_partial_spec_assume_succeed':
    forall (a : A) (b : B),
      Pre a ->
      padded_refines_eq eq (Ret b) (partial_spec_fix' a) ->
      padded_refines_eq eq (Ret b) (partial_spec a).
  Proof.
    intros a b Ha Hfix. unfold partial_spec_fix' in Hfix. cbn in Hfix.
    repeat setoid_rewrite interp_mrec_spec_or in Hfix.

    (*need an inversion principle for or spec *)
    (*could use rewrite for interp_mrec_spec and or_spec *)
    do 2 setoid_rewrite interp_mrec_spec_bind in Hfix. revert Hfix.
    match goal with | |- context [ interp_mrec_spec ?f _ ] => set f as body end.
    intro Hfix.
    assert (
        padded_refines_eq eq (interp_mrec_spec body (or_spec (b <- exists_spec B;; _ <- assert_spec (Post a b);; Ret b) ITree.spin)) (partial_spec a)).
    {
      rewrite interp_mrec_spec_or. unfold partial_spec.
      apply or_spec_l.
      - apply or_spec_r. left. unfold total_spec.
        assumesr. intros. repeat setoid_rewrite interp_mrec_spec_bind.
        normalize_interp_mrec_spec. setoid_rewrite interp_mrec_spec_ret.
        setoid_rewrite bind_bind. setoid_rewrite bind_ret_l.
        eapply padded_refines_bind. reflexivity.
        intros. subst. eapply padded_refines_bind. reflexivity.
        intros. subst. reflexivity.
      - apply or_spec_r. right. rewrite interp_mrec_spec_spin. reflexivity.
    } setoid_rewrite H in Hfix.
    setoid_rewrite interp_mrec_spec_ret in Hfix.
    match type of Hfix with padded_refines_eq eq _ ?t => set t as t1 end.
    fold t1 in Hfix.

    assert (t1 ≈ (interp_mrec_spec body (trigger (@Spec_forall _ (Pre a))) >>
                 Ret tt >>
                  (interp_mrec_spec body
           (ITree.bind (exists_spec nat)
              (fun n : nat => trepeat n (ITree.bind (exists_spec A) (fun a' : A =>
                       trigger (@Spec_exists _ (Pre a')) >> Ret tt >> call_spec a'))))) >> partial_spec a)
                 ).
    {
      unfold t1. repeat rewrite bind_bind.
      apply eqit_bind. reflexivity. intro.
      reflexivity.
    }
    rewrite H0 in Hfix. clear H0.
    (*might have dropped an important assumption *)
    eapply padded_conv_ref_ret_bind; eauto.
    normalize_interp_mrec_spec. cbn.
    apply conv_ref_bind.
    { pstep. red. cbn. constructor; auto. intros a0.
          left. pstep. red. cbn. constructor. }
    intros _.  setoid_rewrite bind_ret_l.
    eapply conv_ref_interp_mrec_conv_ref.
    Unshelve. 3 : { intros C c. destruct c. apply (Pre a0). }
    - cbn.
      intros. destruct d. cbn.
      clear - H0 Ha. setoid_rewrite bind_bind.
      apply conv_ref_mrec_bind.
      { pstep. red. cbn. constructor. auto. left.
        pstep. constructor. }
      intros _. rewrite bind_ret_l.
      repeat rewrite bind_bind. unfold or_spec. setoid_rewrite bind_vis.
      apply conv_ref_mrec_exists. intros n.
      rewrite bind_ret_l.
      eapply conv_ref_mrec_bind.
      + induction n. cbn. pstep. constructor.
        cbn. apply conv_ref_mrec_bind; intros; eauto.
        apply conv_ref_mrec_bind. apply conv_ref_mrec_exists.
        intros. pstep. constructor. intros.
        rewrite bind_bind.
        setoid_rewrite bind_vis.
        apply conv_ref_mrec_exists. intros Hr.
        repeat rewrite bind_ret_l. apply conv_ref_mrec_inl.
        auto. intros. pstep. constructor.
      + intros []. apply conv_ref_mrec_exists.
        intros [ | ]; try apply conv_ref_mrec_spin.
        setoid_rewrite bind_vis. apply conv_ref_mrec_exists.
        intros. setoid_rewrite bind_ret_l. rewrite bind_bind. setoid_rewrite bind_vis.
        apply conv_ref_mrec_exists. intros.
        repeat rewrite bind_ret_l. pstep. constructor.
    - setoid_rewrite bind_vis. setoid_rewrite bind_ret_l.
      apply conv_ref_mrec_exists. intros n. clear - n Ha.
      induction n. cbn. pstep. constructor.
      cbn. eapply conv_ref_mrec_bind; eauto.
      setoid_rewrite bind_bind. setoid_rewrite bind_ret_l.
      setoid_rewrite bind_vis.
      apply conv_ref_mrec_exists. intros a0. rewrite bind_ret_l.
      setoid_rewrite bind_vis. apply conv_ref_mrec_exists. intros Ha0.
      rewrite bind_ret_l. apply conv_ref_mrec_inl. auto. intros. pstep. constructor.
  Qed.

  Lemma partial_spec_fix_partial_spec_assume_fail a :
    ~ Pre a -> padded_refines_eq eq (prog a) (partial_spec a).
  Proof.
    intros HPre. apply or_spec_r.
    left. assumesr. intros. contradiction.
  Qed.

  Lemma partial_spec_fix_partial_spec_assume_succeed:
    forall (a : A) (b : B),
      padded_refines_eq eq (Ret b) (partial_spec_fix a) ->
      padded_refines_eq eq (Ret b) (partial_spec a).
  Proof.
    intros a b Hfix.
    apply or_spec_r. left. unfold total_spec.
    assumesr. intros Ha.
    unfold partial_spec_fix in Hfix.
    do 2 setoid_rewrite interp_mrec_spec_bind in Hfix. revert Hfix.
    match goal with | |- context [ interp_mrec_spec ?f _ ] => set f as body end.
    intro Hfix.
    assert (interp_mrec_spec body (b <- exists_spec B;; _ <- assert_spec (Post a b);; Ret b) ≈
                             (b <- exists_spec B;; _ <- assert_spec (Post a b);; Ret b)).
    {
      repeat setoid_rewrite interp_mrec_spec_bind.
      normalize_interp_mrec_spec.
      setoid_rewrite interp_mrec_spec_ret. cbn. reflexivity.
    } setoid_rewrite H in Hfix.
    (* need to manage diff between padded_refines and refines *)
    cbn in Hfix. setoid_rewrite <- bind_bind in Hfix.
    eapply padded_conv_ref_ret_bind; eauto.
    setoid_rewrite interp_mrec_spec_ret.
    apply conv_ref_bind.
    { pstep. red. cbn. constructor; auto. intros a0.
          left. pstep. red. cbn. constructor. }
    intros _.
    eapply conv_ref_interp_mrec_conv_ref.
    Unshelve. 3 : { intros C c. destruct c. apply (Pre a0). }
    - cbn.
      intros. destruct d. cbn.
      clear - H0 Ha.
      repeat rewrite bind_bind. setoid_rewrite bind_ret_l.
      apply conv_ref_mrec_bind.
      apply conv_ref_mrec_forall. auto. intros. pstep. constructor.
      intros. rewrite <- bind_bind.
      apply conv_ref_mrec_bind.
      + rewrite bind_bind. apply conv_ref_mrec_bind.
        apply conv_ref_mrec_exists. intros. pstep. constructor.
        intros n.
        induction n; cbn. rewrite bind_ret_l. apply conv_ref_mrec_exists.
        intros. pstep. constructor. rewrite bind_bind.
        eapply conv_ref_mrec_bind; intros; eauto.
        setoid_rewrite bind_vis. apply conv_ref_mrec_exists.
        intros. setoid_rewrite bind_ret_l. rewrite bind_bind. setoid_rewrite bind_vis.
        apply conv_ref_mrec_exists. intros. repeat rewrite bind_ret_l.
        apply conv_ref_mrec_inl. auto. intros. pstep. constructor.
      + intros b. rewrite bind_bind. setoid_rewrite bind_vis.
        apply conv_ref_mrec_exists. intros HPost. repeat rewrite bind_ret_l.
        pstep. constructor.
    - setoid_rewrite bind_vis. setoid_rewrite bind_ret_l.
      apply conv_ref_mrec_exists. intros n. clear - n Ha.
      induction n. cbn. pstep. constructor.
      cbn. eapply conv_ref_mrec_bind; eauto.
      setoid_rewrite bind_bind. setoid_rewrite bind_ret_l.
      setoid_rewrite bind_vis.
      apply conv_ref_mrec_exists. intros a0. rewrite bind_ret_l.
      setoid_rewrite bind_vis. apply conv_ref_mrec_exists. intros Ha0.
      rewrite bind_ret_l. apply conv_ref_mrec_inl. auto. intros. pstep. constructor.
  Qed.



  Lemma partial_spec_fix_partial_spec' a :
    (Pre a -> padded_refines_eq eq (prog a) (partial_spec_fix' a)) ->
    padded_refines_eq eq (prog a) (partial_spec a).
  Proof.
    intros Hfix. destruct (classic (Pre a)).
    - specialize (Hfix H). apply prog_ret_spin in H as Hdec; auto.
      destruct Hdec as [ [b Hb] | Hspin ].
      + rewrite Hb. rewrite Hb in Hfix.
        apply partial_spec_fix_partial_spec_assume_succeed'; auto.
      + rewrite Hspin. apply or_spec_r. right. reflexivity.
    - apply or_spec_r. left. assumesr. intro. contradiction.
  Qed.


  Lemma partial_spec_fix_partial_spec a :
    (Pre a -> padded_refines_eq eq (prog a) (partial_spec_fix a)) ->
    padded_refines_eq eq (prog a) (partial_spec a).
  Proof.
    intros Hfix. apply partial_spec_fix_partial_spec'.
    intros Ha. specialize (Hfix Ha). etransitivity; eauto.
    eapply padded_refines_monot with (RPre1 := eqPreRel) (RPost1 := eqPostRel)
    (RR1 := eqPostRel _ _ (Call a) (Call a)); auto.
    { intros. eqPostRel_inv PR. auto. }
    eapply padded_refines_mrec with (RPreInv := eqPreRel).
    2 : constructor.
    intros. eqPreRel_inv H. clear Ha Hfix a. destruct d2.
    simpl. assumesr. intros Ha. assumesl. auto.
    repeat rewrite bind_bind.
    existssl. intros n. existssr n.
    apply padded_refines_bind with (RR := eq).
    + apply refl_refines. red. intros. destruct e; do 2 constructor.
      red. intros. inv H. inj_existT. subst. eqPostRel_inv  H6. auto.
      inj_existT. subst. eqPostRel_inv H6. auto.
      auto. apply pad_is_padded.
    + intros [] [] _ .
      apply or_spec_r. left. existssl. intros b.
      existssr b. assertsl. intros. assertsr. auto. apply padded_refines_ret.
      constructor.
   Qed.

  Lemma partial_spec_fix_spin' a :
    padded_refines_eq eq ITree.spin (partial_spec_fix' a).
  Proof.
    unfold partial_spec_fix'. setoid_rewrite interp_mrec_spec_bind.
    repeat normalize_interp_mrec_spec. assumesr. intros.
    setoid_rewrite interp_mrec_spec_bind.
    setoid_rewrite interp_mrec_spec_bind.
    normalize_interp_mrec_spec.
    match goal with |- context [ interp_mrec_spec ?body_ _  ] => set body_ as body end.
    setoid_rewrite interp_mrec_exists_spec. existssr 0. cbn.
    rewrite interp_mrec_spec_ret, bind_ret_l. rewrite interp_mrec_spec_or.
    apply or_spec_r. right. rewrite interp_mrec_spec_spin. reflexivity.
  Qed.


End SpecFix.
