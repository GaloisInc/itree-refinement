

Require Import Coq.Lists.List Coq.Sorting.Permutation.

From Coq Require Export Morphisms RelationClasses Setoid Program.Equality.
From ITree Require Export ITree ITreeFacts Eq.Rutt Props.Finite.
From Paco Require Import paco.
From Coq Require Export Eqdep EqdepFacts.
Require Import Lia.
Require Export Refinement.

Import Monads.
Import MonadNotation.
Local Open Scope monad_scope.
Locate MonadNotation.
Open Scope list_scope.

Locate Permutation.
(*
Inductive sorted : list nat -> Prop :=
  | sorted_nil : sorted nil
  | sorted_singleton x : sorte
. *)


Inductive sorted : list nat -> Prop :=
  | sorted_nil : sorted nil
  | sorted_single x : sorted (x :: nil)
  | sorted_cons x y l : x <= y -> sorted (y :: l) -> sorted (x :: y :: l).

Lemma sorted_tail : forall l x, sorted (x :: l) -> sorted l.
Proof.
  intros l. induction l; intros; try (constructor; fail).
  inv H. auto.
Qed.
(*
Definition list_ind2_principle' (A : Type) (P : list A -> Prop) (Hnil : P nil)
         (Hcons1 : forall a, P (a :: nil)) (Hcons2 : forall a b l, P l -> P (a :: b :: l))
         l : P l :=
  fix rec l :=
    match l with
    | nil => Hnil
    | a :: nil => Hcons1 a
    | a :: b :: t => Hcons2 a b t (rec t) end. l.
*)
Lemma list_ind2_principle :
    forall (A : Type) (P : list A -> Prop),
      P nil ->
      (forall (a:A), P (a :: nil)) ->
      (forall (a b : A) (l : list A), P l -> P (a :: b :: l)) ->
      forall l : list A, P l.
Proof.
  intros.
  set (fix rec l :=
         match l return P l with
         | nil => H
         | a :: nil => H0 a
         | a :: b :: t => H1 a b t (rec t)
         end
      ) as f. auto.
Qed.

(*rec_fix*)
(* call *)
Definition call_spec {E A B} (a : A) : itree_spec (callE A B +' E) B :=
  ITree.trigger (Spec_vis (inl1 (Call a))).

Definition rec_spec {E A B} (body : A -> itree_spec (callE A B +' E) B) (a : A) :
  itree_spec E B :=
  mrec_spec (calling' body) (Call a).

Definition rec_fix_spec {E A B}
(body : (A -> itree_spec (callE A B +' E) B) ->
        A -> itree_spec (callE A B +' E) B)  :
  A -> itree_spec E B := rec_spec (body call_spec).

Definition halve {E} : list nat -> itree_spec E (list nat * list nat) :=
    rec_fix_spec (fun halve_rec l =>
               match l with
               | x :: y :: t => '(l1,l2) <- halve_rec t;; Ret (x :: l1, y :: l2)
               | x :: nil => Ret ( x :: nil  , nil )
               | nil => Ret ( nil , nil ) end

).

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

Opaque assume_spec.

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

Opaque assert_spec.

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



Definition halve_spec {E} (l : list nat) : itree_spec E (list nat * list nat) :=
  l1 <- exists_spec (list nat);;
  l2 <- exists_spec (list nat);;
  assert_spec (Permutation l (l1 ++ l2));;
  assert_spec (length l1 >= length l2 /\ (length l > length l1 \/ length l <= 1));;
  Ret (l1, l2).

Definition merge {E} : (list nat * list nat) -> itree_spec E (list nat) :=
  rec_fix_spec ( fun merge_rec '(l1, l2) =>
              match (l1,l2) with
              | (h1 :: t1, h2 :: t2) => if Nat.leb h1 h2
                                     then
                                       l <-  merge_rec (t1,l2);;
                                       Ret (h1 :: l)
                                     else
                                       l <- merge_rec (l1, t2);;
                                       Ret (h2 :: l)
              | (l1, nil) => Ret l1
              | (nil, l2) => Ret l2 end ).

Definition merge_spec1 {E} l1 l2 : itree_spec E (list nat) :=
  l <- exists_spec (list nat);;
  assert_spec (Permutation l (l1 ++ l2));;
  Ret l.

Definition merge_spec2 {E} l1 l2 : itree_spec E (list nat) :=
  assume_spec (sorted l1);;
  assume_spec (sorted l2);;
  l <- exists_spec (list nat);;
  assert_spec (sorted l);;
  Ret l.

Definition merge_spec {E} l1 l2 : itree_spec E (list nat) :=
  and_spec (merge_spec1 l1 l2) (merge_spec2 l1 l2).

Definition merge_spec' {E} l1 l2 : itree_spec E (list nat) :=
  assume_spec (sorted l1);;
  assume_spec (sorted l2);;
  l <- exists_spec (list nat);;
  assert_spec (sorted l);;
  assert_spec (Permutation l (l1 ++ l2));;
  Ret l.

(*missing base case*)
Definition sort {E} : list nat -> itree_spec E (list nat) :=
  rec_fix_spec (fun sort_rec l =>
             if Nat.leb (length l) 1
             then Ret l
             else
               '(l1,l2) <- halve l;;
               l1 <- sort_rec l1;;
               l2 <- sort_rec l2;;
               merge (l1,l2)
          ).

Definition sort_spec {E} (l : list nat) : itree_spec E (list nat) :=
  l' <- exists_spec (list nat);;
  assert_spec (Permutation l l');;
  assert_spec (sorted l');;
  Ret l'.


Definition padded_refines_eq {E R1 R2} RR (phi1 : itree_spec E R1) (phi2 : itree_spec E R2) :=
  padded_refines eqPreRel eqPostRel RR phi1 phi2.

Instance proper_leq : Proper (le ==> le ==> le) plus.
Proof.
  repeat intro. lia. Qed.

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

Lemma eqPreRel_eq_type E A B (ea : E A) (eb : E B) : eqPreRel A B ea eb -> A = B.
Proof.
  intros. inv H. auto.
Qed.

Lemma eqPreRel_eq E A (e1 : E A) (e2 : E A) : eqPreRel A A e1 e2 -> e1 = e2.
Proof.
  intros. inv H. inj_existT. subst. auto.
Qed.

Lemma eqPostRel_eq_type E A B (ea : E A) (eb : E B) a b : eqPostRel A B ea eb a b -> A = B.
Proof.
  intros. inv H. auto.
Qed.

Lemma eqPostRel_eq E A (e1 : E A) (e2 : E A) a1 a2 : eqPostRel A A e1 e2 a1 a2 -> e1 = e2 /\ a1 = a2.
Proof.
  intros. inv H. inj_existT. subst. auto.
Qed.

Ltac eqPreRel_inv H := apply eqPreRel_eq_type in H as ?H; subst; apply eqPreRel_eq in H; subst.
Ltac eqPostRel_inv H := apply eqPostRel_eq_type in H as ?H; subst; apply eqPostRel_eq in H as [?H ?H]; subst.

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

Lemma interp_mrec_ret :
  forall {D E : Type -> Type} (ctx : forall T : Type, D T -> itree (D +' E) T) R (r :R),
    interp_mrec ctx (Ret r) ≅ Ret r.
Proof.
  intros. setoid_rewrite unfold_iter. cbn. rewrite bind_ret_l. reflexivity.
Qed.


Instance perm_eq A : Equivalence (@Permutation A).
Proof.
  constructor.
  - red. apply Permutation_refl.
  - red. apply Permutation_sym.
  - red. apply Permutation_trans.
Qed.

(* in addition to needing more lemmas and stuff, I think I should be careful
   about what I am inducting on, its rather subtle*)
Lemma halve_correct E l : padded_refines_eq eq (halve l) (@halve_spec E l).
Proof.
  revert l.
  apply list_ind2_principle.
  - unfold halve, halve_spec, rec_fix_spec, rec_spec, mrec_spec. cbn.
    rewrite interp_mrec_spec_ret. existssr (@nil nat). existssr (@nil nat).
    assertsr. reflexivity. assertsr. split; auto.
    reflexivity.
  - intros n. unfold halve, halve_spec, rec_fix_spec, rec_spec, mrec_spec. cbn.
    rewrite interp_mrec_spec_ret. existssr ( n :: nil ). existssr (@nil nat).
    assertsr. reflexivity. assertsr. split; auto. cbn. repeat constructor.
    reflexivity.
  - intros a b l Hl.
    unfold halve, halve_spec, rec_fix_spec, rec_spec, mrec_spec. cbn.
    rewrite interp_mrec_spec_bind.
    setoid_rewrite interp_mrec_spec_trigger. cbn. setoid_rewrite Hl.
    cbn. rewrite bind_bind.
    existssl. intros l1. setoid_rewrite bind_bind. existssl. intros l2.
    rewrite bind_bind. assertsl. intros Hperm. rewrite bind_bind.
    assertsl. intros [Hlen1 Hlen2].
    existssr (a :: l1). existssr (b :: l2). rewrite bind_ret_l.
    rewrite interp_mrec_spec_ret.
    assertsr.
    { (* this is a permutation fact *) cbn. rewrite Permutation_app_comm. cbn.
      rewrite Hperm. rewrite Permutation_app_comm. reflexivity. }
    assertsr.
    { split; cbn. lia. apply Permutation_length in Hperm.
      rewrite Hperm, app_length. lia.
    }
    reflexivity.
Qed.

Lemma merge_correct' E l1 l2 : padded_refines_eq eq (merge (l1,l2))
                                                    (@merge_spec' E l1 l2).
Proof.
  revert l2. induction l1. intro l2.
  - cbn. unfold merge, rec_fix_spec, rec_spec, mrec_spec. cbn.
    destruct l2; setoid_rewrite interp_mrec_spec_ret.
    + assumesr. intro Hnil. assumesr. intros _ . existssr (@nil nat).
      assertsr. auto. assertsr; reflexivity.
    + assumesr. intros _ . assumesr. intros Hnl. existssr (n :: l2).
      assertsr. auto. assertsr; reflexivity.
  - intro l2. induction l2.
    + setoid_rewrite interp_mrec_spec_ret. cbn.
      assumesr. intros Hal. assumesr. intros Hnl. existssr (a :: l1).
      assertsr. auto. assertsr; try reflexivity. rewrite app_nil_r.
      reflexivity.
    + rename a0 into b.
      unfold merge, rec_fix_spec, rec_spec, mrec_spec. cbn.
      destruct (Nat.leb a b) eqn : Hab; setoid_rewrite interp_mrec_spec_bind;
        setoid_rewrite interp_mrec_spec_trigger.
      * setoid_rewrite IHl1. cbn. setoid_rewrite interp_mrec_spec_ret.
        cbn. rewrite bind_bind. assumesr. intros Hal1.
        assumesr. intros Hbl2. assumesl. eapply sorted_tail; eauto.
        rewrite bind_bind. assumesl. eauto. rewrite bind_bind.
        existssl. intros l. rewrite bind_bind. assertsl.
        intros. rewrite bind_bind. assertsl. intros Hl12.
        rewrite bind_ret_l. existssr (a :: l).
        assertsr.
        { (*fact about permutations should be able to prove fine, maybe easier to go
            through a List Forall def of sorted*) admit. }
        assertsr.
        { rewrite Hl12. reflexivity. }
        reflexivity.
      * setoid_rewrite IHl2. setoid_rewrite interp_mrec_spec_ret.
        cbn. rewrite bind_bind. assumesr. intros Hal1.
        assumesr. intros Hbl2. assumesl. auto.
        rewrite bind_bind. assumesl. eapply sorted_tail; eauto. rewrite bind_bind.
        existssl. intros l. rewrite bind_bind. assertsl.
        intros. rewrite bind_bind. assertsl. intros Hl12.
        rewrite bind_ret_l. existssr (b :: l).
        assertsr.
        { (* similar to before*) admit. }
        assertsr.
        { rewrite Hl12. rewrite (Permutation_app_comm l1 (b ::l2)).
          cbn. rewrite Permutation_app_comm. constructor. }
        reflexivity.
Abort.

Section strong_nat_ind.
  Context (P : nat -> Prop) (H0 : P 0) (Hsind : (forall m, (forall n, n <= m -> P n) -> P (S m))).
  Theorem strong_nat_ind (n : nat) : P n .
  Proof.
    set (fun n => forall k, k <= n -> P k) as Q.
    enough (Q n).
    { unfold Q in H. apply (H n). reflexivity. }
    induction n; unfold Q.
    - intros. inv H. auto.
    - unfold Q in IHn. intros k Hk.
      apply PeanoNat.Nat.le_succ_r in Hk. destruct Hk; subst; auto.
  Qed.
End strong_nat_ind.

Section strong_list_ind.
  Context (A : Type) (P : list A -> Prop) (Hnil : P nil).
  Context (Hsind : forall a l, (forall l', length l' <= length l -> P l') -> P (a :: l)).

  Theorem strong_list_ind (l : list A) : P l.
  Proof.
    remember (length l) as len. generalize dependent l.
    set (fun n =>forall l, n = length l -> P l) as Q.
    enough (Q len); auto.
    apply strong_nat_ind; unfold Q.
    - intros. destruct l; try discriminate. auto.
    - intros m Hm l Hl. destruct l; auto. apply Hsind.
      intros. injection Hl as Hl. subst. eapply Hm; eauto.
  Qed.

End strong_list_ind.


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
  Transparent assume_spec. unfold assume_spec.
  cbn. setoid_rewrite interp_mrec_spec_bind.
  setoid_rewrite interp_mrec_spec'_forall. rewrite bind_vis, bind_trigger.
  apply eqit_Vis. intros. setoid_rewrite interp_mrec_spec_ret. rewrite bind_ret_l.
  reflexivity.
  Opaque assume_spec.
Qed.

Lemma interp_mrec_spec_assert E D T (ctx : forall T, D T -> itree_spec (D +' E) T) :
  interp_mrec_spec ctx (assert_spec T) ≈ assert_spec T.
Proof.
  Transparent assert_spec. unfold assert_spec.
  cbn. setoid_rewrite interp_mrec_spec_bind.
  setoid_rewrite interp_mrec_spec'_exists. rewrite bind_vis, bind_trigger.
  apply eqit_Vis. intros. setoid_rewrite interp_mrec_spec_ret. rewrite bind_ret_l.
  reflexivity.
  Opaque assert_spec.
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

Variant Err : Type -> Type :=
  | throw : Err void.
