Require Import Coq.Lists.List Coq.Sorting.Permutation.

From Coq Require Export Morphisms RelationClasses Setoid Program.Equality.
From ITree Require Export ITree ITreeFacts Eq.Rutt Props.Finite.
From Paco Require Import paco.
From Coq Require Export Eqdep EqdepFacts Logic.Classical.
Require Import Lia.
Require Export Refinement Merge ConvergentRefinement ConcreteRefinement.

Import Monads.
Import MonadNotation.
Local Open Scope monad_scope.

Open Scope list_scope.


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

Lemma spin_bind E R S k : (@ITree.spin E R) >>= k ≅ @ITree.spin E S.
Proof.
  ginit. gcofix CIH. gstep. red. cbn. constructor.
  gfinal. eauto.
Qed.

Lemma and_or_spec E R (t1 t2 : itree_spec E R) :
  padded_refines_eq eq (and_spec t1 t2) (or_spec t1 t2).
Proof.
  unfold and_spec, or_spec, padded_refines_eq, padded_refines.
  setoid_rewrite pad_vis. pstep. red. cbn. econstructor. constructor.
  Unshelve. all : try apply true. econstructor. cbn. constructor.
  Unshelve. all : try apply true. pstep_reverse.
  enough (padded_refines_eq eq t1 t1). auto. reflexivity.
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

Definition halve_spec_fix {E} : list nat -> itree_spec E (list nat * list nat) :=
  rec_fix_spec (fun halve_spec_rec l =>
                  n <- exists_spec nat;;
                  trepeat n ( l' <- exists_spec (list nat);; halve_spec_rec l' );;
                  halve_spec l
               ).


Theorem padded_refines_ret E1 E2 R1 R2 RPre RPost RR r1 r2 :
  (RR r1 r2 : Prop) ->
  @padded_refines E1 E2 R1 R2 RPre RPost RR (Ret r1) (Ret r2).
Proof.
  intros Hr. red. repeat rewrite pad_ret. pstep. constructor. auto.
Qed.

Theorem padded_refines_vis E1 E2 R1 R2 A B
        RPre RPost RR (e1 : E1 A) (e2 : E2 B)
        (k1 : A -> itree_spec E1 R1) (k2 : B -> itree_spec E2 R2) :
  (RPre A B e1 e2 : Prop) ->
  (forall a b, (RPost A B e1 e2 a b : Prop) -> padded_refines RPre RPost RR (k1 a) (k2 b)) ->
  padded_refines RPre RPost RR (Vis (Spec_vis e1) k1) (Vis (Spec_vis e2) k2).
Proof.
  unfold padded_refines. setoid_rewrite pad_vis. intros.
  pstep. constructor; auto. intros. left. pstep. constructor.
  left. eapply H0; auto.
Qed.

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


Global Instance padded_refines_eq_itree E1 E2 R1 R2 RPre RPost RR
  : Proper (eq_itree eq ==> eq_itree eq ==> impl)
           (@padded_refines E1 E2 R1 R2 RPre RPost RR).
Proof.
  repeat intro. assert (x ≈ y). rewrite H. reflexivity.
  rewrite <- H2. assert (x0 ≈ y0). rewrite H0. reflexivity.
  rewrite <- H3. auto.
Qed.

Lemma interp_mrec_spec_or  (E : Type -> Type) (R : Type) (D : Type -> Type) (ctx : forall T : Type, D T -> itree_spec (D +' E) T)
  (t1 t2 : itree_spec _ R)
  : interp_mrec_spec ctx (or_spec t1 t2) ≅ or_spec (interp_mrec_spec ctx t1) (interp_mrec_spec ctx t2).
Proof.
  setoid_rewrite interp_mrec_spec'_exists. apply eqit_Vis. intros [ | ]; reflexivity.
Qed.

Lemma interp_mrec_spec_spin (E : Type -> Type) (R : Type) (D : Type -> Type) (ctx : forall T : Type, D T -> itree_spec (D +' E) T) :
  interp_mrec_spec ctx ITree.spin ≅ @ITree.spin _ R.
Proof.
  pcofix CIH. pstep. red. cbn. constructor.
  right. eauto.
Qed.

Lemma conv_ref_mrec_spin (E D : Type -> Type) (R : Type) (P : forall A : Type, D A -> Prop) :
  @conv_ref_mrec E D R P ITree.spin.
Proof.
  pcofix CIH. pstep. red. cbn. constructor.
  eauto.
Qed.

Lemma conv_ref_mrec_ret (E D : Type -> Type) (R : Type) (P : forall A : Type, D A -> Prop) r:
  @conv_ref_mrec E D R P (Ret r).
Proof.
  pstep. constructor.
Qed.

Lemma conv_ref_mrec_ex (E D : Type -> Type) (R A : Type) (P : forall A : Type, D A -> Prop) k :
  (forall a, conv_ref_mrec P (k a)) ->
  @conv_ref_mrec E D R P (Vis (@Spec_exists _ A) k).
Proof.
  intros. pstep. constructor. left. apply H.
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

Lemma conv_ref_exists_spec E R :
  @conv_ref E R (exists_spec R).
Proof.
  pstep. red. cbn. constructor.
  intros. left. pstep. constructor.
Qed.

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
    apply conv_ref_mrec_bind. rewrite bind_trigger. apply conv_ref_mrec_forall.
    auto. intros. apply conv_ref_mrec_ret.
    intros []. rewrite bind_bind. apply conv_ref_mrec_bind.
    apply conv_ref_mrec_ex. intros. apply conv_ref_mrec_ret.
    intros n. induction n; cbn.
    - rewrite bind_ret_l. apply conv_ref_mrec_ex. intros [ | ].
      2 : apply conv_ref_mrec_spin. apply conv_ref_mrec_bind.
      + apply conv_ref_mrec_ex. intros. apply conv_ref_mrec_ret.
      + intros. rewrite bind_bind. setoid_rewrite bind_vis.
        apply conv_ref_mrec_ex. intros. repeat rewrite bind_ret_l.
        apply conv_ref_mrec_ret.
    - rewrite bind_bind. apply conv_ref_mrec_bind; intros; auto.
      apply conv_ref_mrec_bind.
      + apply conv_ref_mrec_ex. intros. apply conv_ref_mrec_ret.
      + intros. rewrite bind_bind. setoid_rewrite bind_vis.
        apply conv_ref_mrec_ex.
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
      apply conv_ref_mrec_ex. intros n.
      rewrite bind_ret_l.
      eapply conv_ref_mrec_bind.
      + induction n. cbn. pstep. constructor.
        cbn. apply conv_ref_mrec_bind; intros; eauto.
        apply conv_ref_mrec_bind. apply conv_ref_mrec_ex.
        intros. pstep. constructor. intros.
        rewrite bind_bind.
        setoid_rewrite bind_vis.
        apply conv_ref_mrec_ex. intros Hr.
        repeat rewrite bind_ret_l. apply conv_ref_mrec_inl.
        auto. intros. pstep. constructor.
      + intros []. apply conv_ref_mrec_ex.
        intros [ | ]; try apply conv_ref_mrec_spin.
        setoid_rewrite bind_vis. apply conv_ref_mrec_ex.
        intros. setoid_rewrite bind_ret_l. rewrite bind_bind. setoid_rewrite bind_vis.
        apply conv_ref_mrec_ex. intros.
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


Lemma subEqPreRel_eq_type E P A B (ea : E A) (eb : E B) : subEqPreRel P A B ea eb -> A = B.
Proof.
  intros. inv H. auto.
Qed.

Lemma subEqPreRel_eq E P A (e1 : E A) (e2 : E A) : subEqPreRel P A A e1 e2 -> e1 = e2 /\ P A e1.
Proof.
  intros. inv H. inj_existT. subst. auto.
Qed.

Lemma subEqPostRel_eq_type E P A B (ea : E A) (eb : E B) a b : subEqPostRel P A B ea eb a b -> A = B.
Proof.
  intros. inv H. auto.
Qed.

Lemma subEqPostRel_eq E P A (e1 : E A) (e2 : E A) a1 a2 : subEqPostRel P A A e1 e2 a1 a2 -> e1 = e2 /\ a1 = a2
                                                                                 /\ P A e1 a1.
Proof.
  intros. inv H. inj_existT. subst. auto.
Qed.

Ltac subEqPreRel_inv H := eapply subEqPreRel_eq_type in H as ?H; subst; eapply subEqPreRel_eq in H as [?H ?H] ; subst.
Ltac subEqPostRel_inv H := apply subEqPostRel_eq_type in H as ?H; subst; apply subEqPostRel_eq in H as [?H [?H ?H] ]; subst.


Global Instance padded_refines_subEqRel E R (RR : R -> R -> Prop) (P1 : forall A, E A -> Prop) (P2 : forall A, E A -> A -> Prop) :
  Transitive RR ->
  Transitive (padded_refines (subEqPreRel P1) (subEqPostRel P2) RR).
Proof.
  intros HRR t1 t2 t3 Ht12 Ht23. unfold padded_refines in *.
  eapply refines_monot; try eapply refinesTrans; eauto with solve_padded; try apply pad_is_padded.
  - intros A B ea eb PR. inv PR. inj_existT. subst. subEqPreRel_inv H3. auto.
  - intros. subEqPostRel_inv  PR. constructor. intros. destruct H. subEqPreRel_inv H.
    exists x1. split; constructor; auto.
  - intros. inv PR. etransitivity; eauto.
Qed.

Global Instance subEqPostRel_trans E (P : forall A, E A -> A -> Prop) A (e : E A) : Transitive (subEqPostRel P A A e e).
Proof.
  intros x y z Hxy Hyz. subEqPostRel_inv Hxy. auto.
Qed.

(* I think I can save the rest for tomorrow*)

(*
Global Instance refines_proper_bind_RPre E R RPre RPost S :
  Proper (@padded_refines E R R eq ==> pointwise_relation _ (padded_refines_eq eq) ==> @padded_refines_eq E S S eq) ITree.bind.
Proof.
  repeat intro. subst. unfold padded_refines_eq in *. eapply padded_refines_bind; eauto.
  intros; subst. auto.
Qed.
*)

(*do I need the proper instances? Probably *)

Global Instance  padded_refines_eq_gen E1 E2 R1 R2 RPre RPost RR : Proper (padded_refines_eq eq ==> flip (padded_refines_eq eq) ==> flip impl)
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
  (* this is maybe a tad more subtle then I realized, does it require transitivity?,
     that would not be problematic for these relations because there seem to be PER's

   *)

Lemma or_spec_bind_l  E1 E2 R1 S R2 RPre RPost RR (t1 t2 : itree_spec E1 S) (k : S -> itree_spec E1 R1) (t3 : itree_spec E2 R2) :
  padded_refines RPre RPost RR (ITree.bind t1 k) t3 ->
  padded_refines RPre RPost RR (ITree.bind t2 k) t3 ->
  padded_refines RPre RPost RR (ITree.bind (or_spec t1 t2) k) t3.
Proof.
  unfold padded_refines. intros. setoid_rewrite bind_vis. setoid_rewrite pad_vis.
  pstep. constructor. intros [ | ]; constructor; pstep_reverse.
Qed.


(*
Theorem merge
*)
