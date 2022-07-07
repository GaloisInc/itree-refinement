From Coq Require Export Morphisms Setoid Program.Equality.
From ITree Require Export ITree ITreeFacts HeterogeneousRelations.
From Coq Require Export Eqdep EqdepFacts.


Ltac inj_existT := repeat match goal with | H : existT _ _ _ = _ |- _ => apply inj_pair2 in H end.


Notation Rel A B := (A -> B -> Prop).

Definition depProdRel {A B} (RR1 : Rel A B)
  (RR2 : forall a b, RR1 a b -> Prop) : Rel A B :=
  fun r1 r2 => { p : RR1 r1 r2 | RR2 r1 r2 p }.


Notation PreRel E1 E2 := (forall (A B : Type), (E1 A : Type) -> (E2 B : Type) -> Prop).

(*this is stronger than we need *)
Class ReflexivePreRel {E : Type -> Type} (RPre : PreRel E E) : Prop :=
  reflexivePreRel : forall A (e : E A), RPre A A e e.

Class SymmetricPreRel {E : Type -> Type} (RPre : PreRel E E) : Prop :=
  symmetricPreRel : forall A B (e1 : E A) (e2 : E B), RPre A B e1 e2 -> RPre B A e2 e1.

Class TransitivePreRel {E : Type -> Type} (RPre : PreRel E E) : Prop :=
  transitivePreRel : forall A B C (e1 : E A) (e2 : E B) (e3 : E C),
    RPre A B e1 e2 -> RPre B C e2 e3 -> RPre A C e1 e3.

Definition flipPreRel {E1 E2 : Type -> Type} (RPre : PreRel E1 E2) : PreRel E2 E1 :=
  fun A B e1 e2 => RPre B A e2 e1.

Variant rcomposePreRel {E1 E2 E3 : Type -> Type}
           (RPre12 : PreRel E1 E2) (RPre23 : PreRel E2 E3) : forall A C, E1 A -> E3 C -> Prop :=
  rcomposePreRel_intro (A B C: Type) e1 e2 e3 : RPre12 A B e1 e2 -> RPre23 B C e2 e3 -> rcomposePreRel RPre12 RPre23 A C e1 e3.

Variant sumPreRel {E1 E2 F1 F2} (RPreE : PreRel E1 E2) (RPreF : PreRel F1 F2) : forall A B, (E1 +' F1) A -> (E2 +' F2) B -> Prop :=
| sumPreRel_inl A B (e1 : E1 A) (e2 : E2 B) : RPreE A B e1 e2 -> sumPreRel RPreE RPreF A B (inl1 e1) (inl1 e2)
| sumPreRel_inr A B (f1 : F1 A) (f2 : F2 B) : RPreF A B f1 f2 -> sumPreRel RPreE RPreF A B (inr1 f1) (inr1 f2).


Notation PostRel E1 E2 := (forall (A B : Type), (E1 A : Type) -> (E2 B : Type) -> A -> B -> Prop).

Variant sumPostRel {E1 E2 F1 F2} (RPreE : PostRel E1 E2) (RPreF : PostRel F1 F2) :
  forall A B, (E1 +' F1) A -> (E2 +' F2) B -> A -> B -> Prop :=
| sumPostRel_inl A B (e1 : E1 A) (e2 : E2 B) a b : RPreE A B e1 e2 a b -> sumPostRel RPreE RPreF A B (inl1 e1) (inl1 e2) a b
| sumPostRel_inr A B (f1 : F1 A) (f2 : F2 B) a b : RPreF A B f1 f2 a b -> sumPostRel RPreE RPreF A B (inr1 f1) (inr1 f2) a b
.

(* This may need to be defined in dependent on two PreRel's?*)
(*
Variant rcomposePostRel' {E1 E2 E3 : Type -> Type}
           (RPre12 : PostRel E1 E2) (RPre23 : PostRel E2 E3):
  forall A C, E1 A -> E3 C -> A -> C -> Prop :=
  | rcomposePostRel_intro (A B C : Type)
                       (*maybe I should somehow universally quantify this*)
                       (e1 : E1 A) (e2 : E2 B) (e3 : E3 C)
                       a b c :
    RPre12 A B e1 e2 a b -> RPre23 B C e2 e3 b c ->
    rcomposePostRel RPre12 RPre23 A C e1 e3 a c.
*)


(* this means that if I find an e2, there must be a b that we can link
   the two with,
   the problem is what if the post condition is empty I should think of
   a new case for this possibility
 *)
Variant rcomposePostRel {E1 E2 E3 : Type -> Type}
           (RPre12 : PostRel E1 E2) (RPre23 : PostRel E2 E3)
           (RPre : forall A B C, E1 A -> E2 B -> E3 C -> Prop)
  :
  forall A C, E1 A -> E3 C -> A -> C -> Prop :=
  | rcomposePostRel_intro (A C : Type)
                       (e1 : E1 A) (e3 : E3 C)
                       a c :
    (forall B (e2 : E2 B),
      RPre A B C e1 e2 e3 -> exists b, RPre12 A B e1 e2 a b /\ RPre23 B C e2 e3 b c) ->
    rcomposePostRel RPre12 RPre23 RPre A C e1 e3 a c.

(*this is stronger than I need*)
(* I see 2 ways to do it, either it is reflexive wrt RPre
   or *)
Class ReflexivePostRel {E : Type -> Type} (RPreA : PostRel E E) : Prop :=
  reflexivePostRel : forall A (e : E A) (a b : A),
      RPreA A A e e a b -> a = b.

Class SymmetricPostRel {E : Type -> Type} (RPreA : PostRel E E) : Prop :=
  symmetricPostRel : forall A B (e1 : E A) (e2 : E B) a b,
      RPreA A B e1 e2 a b -> RPreA B A e2 e1 b a.


Variant eqPreRel {E} : PreRel E E :=
  | eqPreRel_refl A (e : E A) : eqPreRel A A e e.

Variant eqPostRel {E} : PostRel E E :=
  | eqPostRel_refl A e a : eqPostRel A A e e a a.

Variant subEqPreRel {E} (P : forall A, E A -> Prop) : PreRel E E :=
  | subEqPreRel_intro A (e : E A) : P A e -> subEqPreRel P A A e e.

Variant subEqPostRel {E} (P : forall A, E A -> A -> Prop) : PostRel E E :=
  | subEqPostRel_intro A e a : P A e a -> subEqPostRel P A A e e a a.

Variant subEqRel {A: Type} (P : A -> Prop) : Rel A A :=
  | subEqRel_intro a : P a -> subEqRel P a a.


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


Global Instance subEqPostRel_trans E (P : forall A, E A -> A -> Prop) A (e : E A) : Transitive (subEqPostRel P A A e e).
Proof.
  intros x y z Hxy Hyz. subEqPostRel_inv Hxy. auto.
Qed.
