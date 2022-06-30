Require Import Coq.Lists.List Coq.Sorting.Permutation.

From Coq Require Export Morphisms RelationClasses Setoid Program.Equality.
From Coq Require Export Wellfounded Arith.Wf_nat Arith.Compare_dec Arith.Lt.
From ITree Require Export ITree ITreeFacts Eq.Rutt Props.Finite.
From Paco Require Import paco.
From Coq Require Export Eqdep EqdepFacts.
Require Import Lia.
Require Export Refinement Merge MergePartial Automation MergeError.

Import Monads.
Import MonadNotation.
Local Open Scope monad_scope.

Open Scope list_scope.


Variant serverE : Type -> Type :=
  | sendE : list nat -> serverE unit 
  | rcvE  : serverE (list nat).


Definition server_impl {E} `{errorE -< E} `{serverE -< E} : unit -> itree_spec E void :=
  rec_fix_spec (fun rec _ => 
                  l <- trigger rcvE;;
                  ls <- sort l;;
                  trigger (sendE ls);;
                  rec tt
               ).

Definition server_spec {E} `{errorE -< E} `{serverE -< E} : unit -> itree_spec E void :=
  rec_fix_spec (fun rec _ => 
                  l <- trigger rcvE;;
                  ls <- spec_exists (list nat);;
                  assert_spec (Permutation l ls);;
                  assert_spec (sorted ls);;
                  trigger (sendE ls);;
                  rec tt
               ).

Hint Extern 101 (padded_refines _ _ _ (sort ?l) _) =>
  apply (padded_refines_rew_l (sort_refines_total_spec l)) : refines.
Hint Extern 101 (padded_refines _ _ _ (sort ?l >>= _) _) =>
  apply (padded_refines_rew_bind_l (sort_refines_total_spec l)) : refines.

Lemma server_refines_spec {E} `{errorE -< E} `{serverE -< E} u :
  padded_refines_eq (E:=E) eq (server_impl u) (server_spec u).
Proof.
  unfold server_impl, server_spec.
  prove_refinement.
  - exact (a = a0).
  - exact True.
  - prove_refinement_continue.
    all: unfold sort_pre, sort_post in *; easy.
Qed.
