

Require Import Coq.Lists.List Coq.Sorting.Permutation.

From Coq Require Export Morphisms RelationClasses Setoid Program.Equality.
From ITree Require Export ITree ITreeFacts Eq.Rutt Props.Finite.
From Paco Require Import paco.
From Coq Require Export Eqdep EqdepFacts.
Require Import Lia.
Require Export Refinement Combinators.

Import Monads.
Import MonadNotation.
Local Open Scope monad_scope.
Locate MonadNotation.
Open Scope list_scope.

Locate Permutation.

Opaque assume_spec.
Opaque assert_spec.


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


Definition halve {E} : list nat -> itree_spec E (list nat * list nat) :=
    rec_fix_spec (fun halve_rec l =>
               match l with
               | x :: y :: t => '(l1,l2) <- halve_rec t;; Ret (x :: l1, y :: l2)
               | x :: nil => Ret ( x :: nil  , nil )
               | nil => Ret ( nil , nil ) end

).

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
