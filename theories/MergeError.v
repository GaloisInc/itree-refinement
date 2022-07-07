

Require Import Coq.Lists.List Coq.Sorting.Permutation.

From Coq Require Export Morphisms RelationClasses Setoid Program.Equality.
From Coq Require Export Wellfounded Arith.Wf_nat Arith.Compare_dec Arith.Lt.
From ITree Require Export ITree ITreeFacts Eq.Rutt Props.Finite.
From Paco Require Import paco.
From Coq Require Export Eqdep EqdepFacts.
Require Import Lia.
Require Export Refinement Merge MergePartial Automation.

Import Monads.
Import MonadNotation.
Local Open Scope monad_scope.

Open Scope list_scope.


Variant errorE : Type -> Type :=
  | throw : errorE void.
Locate "-<".

(*need stuff for injection *)

Global Instance ResumSpecEvent {E1 E2} : E1 -< E2 -> E1 -< SpecEvent E2 :=
  fun s _ e => Spec_vis (s _ e).

Definition is_nil {E} `{errorE -< E} (l : list nat) : itree_spec E bool :=
  match l with
  | nil => Ret true
  | _ => Ret false
  end.

Definition head {E} `{errorE -< E} (l : list nat) : itree_spec E nat :=
  match l with
  | nil => trigger throw ;; Ret 0
  | n :: _ => Ret n
  end.

Definition tail {E} `{errorE -< E} (l : list nat) : itree_spec E (list nat) :=
  match l with
  | nil => trigger throw;; Ret nil
  | _ :: t => Ret t
  end.


(** * Definitions *)

Definition halve {E : Type -> Type} `{errorE -< E}: list nat -> itree_spec E (list nat * list nat) :=
  rec_fix_spec (fun rec l1 =>
                 b1 <- is_nil l1;;
                 if b1 : bool
                 then Ret (nil, nil)
                 else l2 <- tail l1;;
                      b2 <- is_nil l2;;
                      if b2 : bool
                      then
                        Ret (l1, nil)
                      else
                        x <- head l1;;
                        y <- head l2;;
                        l3 <- tail l2;;
                        '(l4,l5) <- rec l3;;
                        Ret (x :: l4, y :: l5)

               ).

Definition merge {E : Type -> Type} `{errorE -< E} : (list nat * list nat) -> itree_spec E (list nat) :=
  rec_fix_spec (fun rec '(l1,l2) =>
                  b1 <- is_nil l1;;
                  b2 <- is_nil l2;;
                  if b1 : bool then
                    Ret l2
                  else if b2 : bool then
                    Ret l1
                  else
                    x <- head l1;;
                    tx <- tail l1;;
                    y <- head l2;;
                    ty <- tail l2;;
                    if Nat.leb x y then
                      l <- rec (tx, y :: ty);;
                      Ret (x :: l)
                    else
                      l <- rec (x :: tx, ty);;
                      Ret (y :: l)
               ).

Definition sort {E : Type -> Type} `{errorE -< E} : list nat -> itree_spec E (list nat) :=
  rec_fix_spec (fun rec l =>
                  b1 <- is_nil l;;
                  if b1 : bool then
                    Ret l
                  else
                    t <- tail l;;
                    b2 <- is_nil t;;
                    if b2 : bool then
                      Ret l
                    else
                      '(l1, l2) <- halve l;;
                      l1s <- rec l1;;
                      l2s <- rec l2;;
                      merge (l1s, l2s)
               ).


(** * Halve *)

Definition halve_pre (l : list nat) : Prop := True.
Definition halve_post (l : list nat) (p : list nat * list nat) :=
  let '(l1,l2) := p in
  Permutation l (l1 ++ l2) /\
    (length l1 >= length l2 /\ (length l > length l1 \/ 1 >= length l)).

Definition dec_length (l1 l2 : list nat) :=
  length l1 < length l2.

Lemma halve_refines_total_spec {E} `{errorE -< E} l :
  padded_refines_eq (E:=E) eq (halve l) (total_spec halve_pre halve_post l).
Proof.
  unfold halve, is_nil, head, tail.
  prove_refinement.
  - exact (a = a0).
  - exact (halve_post a r).
  - exact (dec_length a a0).
  - apply well_founded_ltof.
  - unfold halve_pre, halve_post, dec_length.
    prove_refinement_continue.
    all: repeat split; simpl; auto.
    all: destruct H1 as [? []]; try lia.
    + rewrite Permutation_app_comm. cbn.
      rewrite H1. rewrite Permutation_app_comm. reflexivity.
    + rewrite H1. repeat rewrite app_length. lia.
    + rewrite Permutation_app_comm. cbn.
      rewrite H1. rewrite Permutation_app_comm. reflexivity.
    + repeat rewrite H1. repeat rewrite app_length. lia.
Qed.


(** * Merge *)

Definition merge_pre (p : list nat * list nat) :=
  let '(l1,l2) := p in
  sorted l1 /\ sorted l2.
Definition merge_post (p : list nat * list nat) (l : list nat) :=
  let '(l1,l2) := p in
  sorted l /\ Permutation l (l1 ++ l2).

Definition dec_either_length (pr1 pr2 : list nat * list nat) :=
  length (fst pr1) < length (fst pr2) /\ length (snd pr1) = length (snd pr2) \/
  length (fst pr1) = length (fst pr2) /\ length (snd pr1) < length (snd pr2).

Lemma wf_dec_either_length : well_founded dec_either_length.
Proof.
  apply wf_union.
  - intros [z1 z2] [y1 y2] [] [x1 x2] []; simpl in *.
    exists (z1, x2); simpl; split; try easy.
    + rewrite <- H0. exact H2.
    + rewrite H1. exact H.
  - eapply wf_incl; [| apply well_founded_ltof ].
    intros ? ? []. exact H.
  - eapply wf_incl; [| apply well_founded_ltof ].
    intros ? ? []. exact H0.
Qed.

Lemma sorted_cons_all x xs : sorted xs ->
  (forall x', In x' xs -> x <= x') -> sorted (x :: xs).
Proof.
  destruct xs.
  - constructor.
  - constructor; eauto.
    apply H0. left; reflexivity.
Qed.

Lemma sorted_fst_and_tail x y xs :
  sorted (x :: y :: xs) -> sorted (x :: xs).
Proof.
  intro; inversion H; subst.
  destruct xs.
  - constructor.
  - inversion H4; subst.
    constructor; eauto.
    transitivity y; eauto.
Qed.

Lemma sorted_head x xs :
  sorted (x :: xs) -> (forall x', In x' xs -> x <= x').
Proof.
  revert x; induction xs; intros.
  - contradiction H0.
  - destruct H0; subst.
    + inversion H; subst. eauto.
    + apply IHxs; eauto.
      eapply sorted_fst_and_tail; eauto.
Qed.

Lemma sorted_cons_perm_app x xs y ys xys :
  Permutation xys (xs ++ (y :: ys)) -> sorted xys ->
  x <= y -> sorted (x :: xs) -> sorted (y :: ys) -> sorted (x :: xys).
Proof.
  intros. apply sorted_cons_all; eauto; intros.
  eapply Permutation_in in H4; eauto.
  apply in_app_or in H4; destruct H4.
  - eapply sorted_head in H2; eauto.
  - revert x' H4. eapply sorted_head.
    constructor; eauto.
Qed.

Lemma merge_refines_total_spec {E} `{errorE -< E} pr :
  padded_refines_eq (E:=E) eq (merge pr) (total_spec merge_pre merge_post pr).
Proof.
  unfold merge, is_nil, head, tail.
  prove_refinement.
  - exact (a = a0).
  - exact (merge_post a r).
  - exact (dec_either_length a a0).
  - apply wf_dec_either_length.
  - unfold merge_pre, merge_post, dec_either_length.
    prove_refinement_continue.
    all: repeat split; simpl; auto.
    all: destruct e_forall; try easy.
    + eapply sorted_tail; eauto.
    + eapply sorted_cons_perm_app; eauto.
      apply leb_complete; eauto.
    + eapply sorted_cons_perm_app; eauto.
      apply leb_complete; eauto.
    + eapply sorted_tail; eauto.
    + rewrite Permutation_app_comm in H2.
      eapply sorted_cons_perm_app; eauto.
      apply leb_iff_conv in e_if; lia.
    + rewrite H2. rewrite (Permutation_app_comm a2 (a :: a3)).
      cbn. rewrite Permutation_app_comm. constructor.
    + rewrite Permutation_app_comm in H2.
      eapply sorted_cons_perm_app; eauto.
      apply leb_iff_conv in e_if; lia.
    + rewrite H2. rewrite (Permutation_app_comm a2 (a :: a3)).
      cbn. rewrite Permutation_app_comm. constructor.
    + rewrite app_nil_r. reflexivity.
    + rewrite app_nil_r. reflexivity.
Qed.


(** * Sort *)

Definition sort_pre (l : list nat) := True.
Definition sort_post (l1 l2 : list nat) :=
  sorted l2 /\
  Permutation l1 l2.

Lemma padded_refines_rew_l {E1 E2 R1 R2 RPre RPost RR}
      {t1 t2 : itree_spec E1 R1} {t3 : itree_spec E2 R2} :
  padded_refines_eq eq t1 t2 ->
  padded_refines RPre RPost RR t2 t3 ->
  padded_refines RPre RPost RR t1 t3.
Proof. intros. rewrite H; eauto. Qed.

Lemma padded_refines_rew_bind_l {E1 E2 R1 R2 A RPre RPost RR}
      {t1 t2 : itree_spec E1 A} {k : A -> itree_spec E1 R1} {t3 : itree_spec E2 R2} :
  padded_refines_eq eq t1 t2 ->
  padded_refines RPre RPost RR (t2 >>= k) t3 ->
  padded_refines RPre RPost RR (t1 >>= k) t3.
Proof. intros. rewrite H; eauto. Qed.

Hint Extern 101 (padded_refines _ _ _ (halve ?l) _) =>
  apply (padded_refines_rew_l (halve_refines_total_spec l)) : refines.
Hint Extern 101 (padded_refines _ _ _ (halve ?l >>= _) _) =>
  apply (padded_refines_rew_bind_l (halve_refines_total_spec l)) : refines.

Hint Extern 101 (padded_refines _ _ _ (merge ?pr) _) =>
  apply (padded_refines_rew_l (merge_refines_total_spec pr)) : refines.
Hint Extern 101 (padded_refines _ _ _ (merge ?pr >>= _) _) =>
  apply (padded_refines_rew_bind_l (merge_refines_total_spec pr)) : refines.

Lemma sort_refines_total_spec {E} `{errorE -< E} pr :
  padded_refines_eq (E:=E) eq (sort pr) (total_spec sort_pre sort_post pr).
Proof.
  unfold sort, is_nil, head, tail.
  prove_refinement.
  - exact (a = a0).
  - exact (sort_post a r).
  - exact (dec_length a a0).
  - apply well_founded_ltof.
  - unfold sort_pre, sort_post, dec_length.
    prove_refinement_continue.
    all: unfold halve_pre, halve_post, merge_pre, merge_post in *.
    all: try destruct e_exists0 as [? []]; try destruct e_exists1.
    all: split; try easy; try solve [ constructor ].
    + destruct H2; eauto. simpl in H2. lia.
    + destruct H5.
      * eapply le_lt_trans; eauto.
      * simpl in H5. lia.
    + rewrite H6, H10, H2, H5. reflexivity.
    + rewrite H6, H10, H2, H5. reflexivity.
Qed.
