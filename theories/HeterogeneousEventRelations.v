From Coq Require Export Morphisms Setoid Program.Equality.
From ITree Require Export ITree ITreeFacts HeterogeneousRelations.


Notation Rel A B := (A -> B -> Prop).

Definition depProdRel {A B} (RR1 : Rel A B)
  (RR2 : forall a b, RR1 a b -> Prop) : Rel A B :=
  fun r1 r2 => { p : RR1 r1 r2 | RR2 r1 r2 p }.


Notation PreRel E1 E2 := (forall (A B : Type), (E1 A : Type) -> (E2 B : Type) -> Prop).

(*this is stronger than we need *)
Class ReflexivePreRel {E : Type -> Type} (RE : PreRel E E) : Prop :=
  reflexivePreRel : forall A (e : E A), RE A A e e.

Class SymmetricPreRel {E : Type -> Type} (RE : PreRel E E) : Prop :=
  symmetricPreRel : forall A B (e1 : E A) (e2 : E B), RE A B e1 e2 -> RE B A e2 e1.

Class TransitivePreRel {E : Type -> Type} (RE : PreRel E E) : Prop :=
  transitivePreRel : forall A B C (e1 : E A) (e2 : E B) (e3 : E C),
    RE A B e1 e2 -> RE B C e2 e3 -> RE A C e1 e3.

Definition flipPreRel {E1 E2 : Type -> Type} (RE : PreRel E1 E2) : PreRel E2 E1 :=
  fun A B e1 e2 => RE B A e2 e1.

Variant rcomposePreRel {E1 E2 E3 : Type -> Type}
           (RE12 : PreRel E1 E2) (RE23 : PreRel E2 E3) : forall A C, E1 A -> E3 C -> Prop :=
  rcomposePreRel_intro (A B C: Type) e1 e2 e3 : RE12 A B e1 e2 -> RE23 B C e2 e3 -> rcomposePreRel RE12 RE23 A C e1 e3.

Variant sumPreRel {E1 E2 F1 F2} (REE : PreRel E1 E2) (REF : PreRel F1 F2) : forall A B, (E1 +' F1) A -> (E2 +' F2) B -> Prop :=
| sumPreRel_inl A B (e1 : E1 A) (e2 : E2 B) : REE A B e1 e2 -> sumPreRel REE REF A B (inl1 e1) (inl1 e2)
| sumPreRel_inr A B (f1 : F1 A) (f2 : F2 B) : REF A B f1 f2 -> sumPreRel REE REF A B (inr1 f1) (inr1 f2).


Notation PostRel E1 E2 := (forall (A B : Type), (E1 A : Type) -> (E2 B : Type) -> A -> B -> Prop).

Variant sumPostRel {E1 E2 F1 F2} (REE : PostRel E1 E2) (REF : PostRel F1 F2) :
  forall A B, (E1 +' F1) A -> (E2 +' F2) B -> A -> B -> Prop :=
| sumPostRel_inl A B (e1 : E1 A) (e2 : E2 B) a b : REE A B e1 e2 a b -> sumPostRel REE REF A B (inl1 e1) (inl1 e2) a b
| sumPostRel_inr A B (f1 : F1 A) (f2 : F2 B) a b : REF A B f1 f2 a b -> sumPostRel REE REF A B (inr1 f1) (inr1 f2) a b
.

(* This may need to be defined in dependent on two PreRel's?*)
(*
Variant rcomposePostRel' {E1 E2 E3 : Type -> Type}
           (RE12 : PostRel E1 E2) (RE23 : PostRel E2 E3):
  forall A C, E1 A -> E3 C -> A -> C -> Prop :=
  | rcomposePostRel_intro (A B C : Type)
                       (*maybe I should somehow universally quantify this*)
                       (e1 : E1 A) (e2 : E2 B) (e3 : E3 C)
                       a b c :
    RE12 A B e1 e2 a b -> RE23 B C e2 e3 b c ->
    rcomposePostRel RE12 RE23 A C e1 e3 a c.
*)


(* this means that if I find an e2, there must be a b that we can link
   the two with,
   the problem is what if the post condition is empty I should think of
   a new case for this possibility
 *)
Variant rcomposePostRel {E1 E2 E3 : Type -> Type}
           (RE12 : PostRel E1 E2) (RE23 : PostRel E2 E3)
           (RE : forall A B C, E1 A -> E2 B -> E3 C -> Prop)
  :
  forall A C, E1 A -> E3 C -> A -> C -> Prop :=
  | rcomposePostRel_intro (A C : Type)
                       (e1 : E1 A) (e3 : E3 C)
                       a c :
    (forall B (e2 : E2 B),
      RE A B C e1 e2 e3 -> exists b, RE12 A B e1 e2 a b /\ RE23 B C e2 e3 b c) ->
    rcomposePostRel RE12 RE23 RE A C e1 e3 a c.

(*this is stronger than I need*)
(* I see 2 ways to do it, either it is reflexive wrt RE
   or *)
Class ReflexivePostRel {E : Type -> Type} (REA : PostRel E E) : Prop :=
  reflexivePostRel : forall A (e : E A) (a b : A),
      REA A A e e a b -> a = b.

Class SymmetricPostRel {E : Type -> Type} (REA : PostRel E E) : Prop :=
  symmetricPostRel : forall A B (e1 : E A) (e2 : E B) a b,
      REA A B e1 e2 a b -> REA B A e2 e1 b a.


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
