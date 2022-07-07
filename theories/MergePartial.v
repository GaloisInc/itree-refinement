Require Import Coq.Lists.List Coq.Sorting.Permutation.

From Coq Require Export Morphisms RelationClasses Setoid Program.Equality.
From ITree Require Export ITree ITreeFacts Eq.Rutt Props.Finite.
From Paco Require Import paco.
From Coq Require Export Eqdep EqdepFacts Logic.Classical.
Require Import Lia.
Require Export Refinement Combinators ConvergentRefinement ConcreteRefinement Automation Merge.

Import Monads.
Import MonadNotation.
Local Open Scope monad_scope.

Open Scope list_scope.


Lemma and_or_spec E R (t1 t2 : itree_spec E R) :
  padded_refines_eq eq (and_spec t1 t2) (or_spec t1 t2).
Proof.
  unfold and_spec, or_spec, padded_refines_eq, padded_refines.
  setoid_rewrite pad_vis. pstep. red. cbn. econstructor. constructor.
  Unshelve. all : try apply true. econstructor. cbn. constructor.
  Unshelve. all : try apply true. pstep_reverse.
  enough (padded_refines_eq eq t1 t1). auto. reflexivity.
Qed.


Definition halve_spec_fix {E} : list nat -> itree_spec E (list nat * list nat) :=
  rec_fix_spec (fun halve_spec_rec l =>
                  n <- exists_spec nat;;
                  trepeat n ( l' <- exists_spec (list nat);; halve_spec_rec l' );;
                  halve_spec l
               ).

Variant halve_call : forall A, callE (list nat) (list nat * list nat) A -> A -> Prop :=
  | halve_call_i (l l1 l2: list nat) :
    Permutation l (l1 ++ l2) ->
    (length l1 >= length l2 /\ (length l > length l1 \/ length l <= 1)) ->
    halve_call _ (Call l) (l1,l2).

Lemma halve_correct' E l : padded_refines_eq eq (@halve E l) (halve_spec_fix l).
Proof.
  eapply padded_refines_monot with (RPre1 := eqPreRel)
                                   (RPost1 := eqPostRel)
                                   (RR1 := subEqPostRel halve_call _ _ (Call l) (Call l)); eauto.
  { intros [l1 l2] [l3 l4]. intros. inv PR. inj_existT. subst. auto. }
  eapply padded_refines_mrec with (RPreInv := eqPreRel)
                                  (* in this post condition need to include *)
                                  (RPostInv := subEqPostRel halve_call).
  2 : constructor. intros.
  eqPreRel_inv H. clear l. destruct d2 as [l]. cbn.
  destruct l as [ | a [ | b l] ].
  - existssr 0. rewrite trepeat_0. rewrite bind_ret_l.
    existssr (@nil nat). existssr (@nil nat). assertsr. reflexivity.
    assertsr. cbn. lia.
    apply padded_refines_ret. do 2 constructor. reflexivity.
    cbn. lia. (*note reflexivity is not enough this is a subreflexive rel*)
  - existssr 0. rewrite trepeat_0. rewrite bind_ret_l.
    existssr (a :: nil). existssr (@nil nat). assertsr. reflexivity.
    assertsr. cbn. lia. apply padded_refines_ret. do 2 constructor.
    reflexivity. cbn. lia.
  - cbn. existssr 1. rewrite trepeat_Sn. setoid_rewrite trepeat_0.
    cbn. repeat rewrite bind_bind. existssr l.
    eapply padded_refines_bind with (RR :=
                                    subEqPostRel halve_call (list nat * list nat) (list nat * list nat) (Call (l)) (Call (l))).
    + unfold call_spec. apply padded_refines_vis. repeat constructor.
      intros [l1 l2] r Hl12. inv Hl12. inj_existT. subst.
      inv H5. inj_existT. subst. apply padded_refines_ret.
      constructor. auto.
    + intros [l1 l2] r2 Heq. inv Heq. inj_existT. subst.
      inv H4. inj_existT. injection H5. intros. subst.
      rewrite bind_ret_l.
      existssr (a :: l1). existssr (b :: l2). assertsr.
      { cbn. rewrite Permutation_app_comm. cbn.
      rewrite H0. rewrite Permutation_app_comm. reflexivity. }
      assertsr.
      { cbn. rewrite H0. repeat rewrite app_length. lia. }
      apply padded_refines_ret. do 2 constructor.
      { cbn. rewrite Permutation_app_comm. cbn.
      rewrite H0. rewrite Permutation_app_comm. reflexivity. }
      cbn. repeat rewrite H0. repeat rewrite app_length. lia.
Qed.

Lemma auto_halve_correct' E l :
  padded_refines_eq eq (@halve E l) (@halve_spec_fix E l).
Proof.
  unfold halve, halve_spec_fix, halve_spec.
  prove_refinement.
  - exact (a = a0).
  - exact ((Permutation a (fst r ++ snd r)) /\
           (length (fst r) >= length (snd r) /\ (length a > length (fst r) \/ length a <= 1))).
  - prove_refinement_continue.
    Check padded_refines_trigger_bind_r.
    all: cbn; cbn in *.
    all: try split; try easy; try lia.
    + rewrite Permutation_app_comm. cbn.
      rewrite H0. rewrite Permutation_app_comm. reflexivity.
    + rewrite H0. repeat rewrite app_length. lia.
    + rewrite Permutation_app_comm. cbn.
      rewrite H0. rewrite Permutation_app_comm. reflexivity.
    + repeat rewrite H0. repeat rewrite app_length. lia.
Qed.

Opaque assume_spec.
Opaque assert_spec.
Opaque forall_spec.
Opaque exists_spec.

Lemma halve_spec_fix_correct' E l :
  padded_refines_eq eq (@halve E l) (partial_spec_fix (fun _ => True)
                                                   (fun l '(l1,l2) => Permutation l (l1 ++ l2) /\
                               (length l1 >= length l2 /\ (length l > length l1 \/ length l <= 1))) l).
Proof.
  eapply padded_refines_monot with (RPre1 := eqPreRel)
                                   (RPost1 := eqPostRel)
                                   (RR1 := subEqPostRel halve_call _ _ (Call l) (Call l)); eauto.
  { intros [l1 l2] [l3 l4]. intros. inv PR. inj_existT. subst. auto. }
    eapply padded_refines_mrec with (RPreInv := eqPreRel)
                                  (* in this post condition need to include *)
                                  (RPostInv := subEqPostRel halve_call).
  2 : constructor. intros.
  eqPreRel_inv H. clear l. destruct d2 as [l]. cbn.
  destruct l as [ | a [ | b l] ].
  - assumesr. intros _. rewrite bind_bind. existssr 0.
    cbn. rewrite bind_ret_l. existssr (@nil nat,@nil nat).
    assertsr. split. reflexivity. lia.
    apply padded_refines_ret. do 2 constructor. reflexivity. cbn. lia.
  - assumesr. intros _. rewrite bind_bind. existssr 0.
    cbn. rewrite bind_ret_l. existssr (a :: nil, @nil nat).
    assertsr. split. reflexivity. cbn. lia.
    apply padded_refines_ret. do 2 constructor. reflexivity. cbn. lia.
  - assumesr. intros _. rewrite bind_bind. existssr 1.
    cbn. repeat rewrite bind_bind. existssr l.
    repeat rewrite bind_bind.
    assertsr. auto. setoid_rewrite bind_ret_l.
    eapply padded_refines_bind with  (RR :=
                                    subEqPostRel halve_call (list nat * list nat) (list nat * list nat) (Call (l)) (Call (l))).
    { apply padded_refines_vis. constructor. constructor. intros [l1 l2] b0 Hl12.
      inv Hl12. inj_existT. subst. inv H5. inj_existT. subst.
      apply padded_refines_ret. constructor. auto. }
    intros [l1 l2] r Hl12. inv Hl12. inj_existT. subst. inv H4. inj_existT.
    injection H5; intros; subst. existssr (a :: l1,b :: l2). assertsr.
    split.
    { cbn. rewrite Permutation_app_comm. cbn.
      rewrite H0. rewrite Permutation_app_comm. reflexivity. }
    { cbn. repeat rewrite H0. repeat rewrite app_length. lia. }
    apply padded_refines_ret. constructor. constructor.
    { cbn. rewrite Permutation_app_comm. cbn.
      rewrite H0. rewrite Permutation_app_comm. reflexivity. }
    { cbn. repeat rewrite H0. repeat rewrite app_length. lia. }
 Qed.

  (* this is maybe a tad more subtle then I realized, does it require transitivity?,
     that would not be problematic for these relations because there seem to be PER's

   *)

(*
Theorem merge
*)
