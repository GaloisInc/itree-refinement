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
