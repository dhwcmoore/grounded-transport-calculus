(** * Erasure: forgetting the witness.

    [erased G x y] is [inhabited (GT G x y)]: the existence of a witness, with
    lineage and construction information discarded.  We prove soundness
    ([erasure_sound]).  Exact recovery of [R] needs a completeness hypothesis
    and is *not* a theorem of the generic calculus; see
    [Obstructions.UngroundedAgreement] for a model where it fails. *)

From Coq Require Import Classes.RelationClasses.
From GTC.Core Require Import GroundedTransport.

Section Erasure.
  Context {X : Type} {R : X -> X -> Prop} (G : GTransport X R).

  Definition erased (x y : X) : Prop := inhabited (GT G x y).

  Definition erase {x y : X} (w : GT G x y) : erased x y := inhabits w.

  Lemma erased_refl : forall x, erased x x.
  Proof. intro x. exact (erase (gt_refl G x)). Qed.

  Lemma erased_trans : forall x y z, erased x y -> erased y z -> erased x z.
  Proof.
    intros x y z [v] [w]. exact (erase (gt_compose G v w)).
  Qed.

  (** Milestone result 3. *)
  Theorem erasure_sound : forall x y, erased x y -> R x y.
  Proof. intros x y [w]. exact (gt_sound G w). Qed.

  Global Instance erased_Reflexive : Reflexive erased := erased_refl.
  Global Instance erased_Transitive : Transitive erased := erased_trans.
  Global Instance erased_PreOrder : PreOrder erased.
  Proof. split; [exact erased_refl | exact erased_trans]. Qed.

  (** Exact recovery, [R x y <-> ||GT x y||], holds exactly under a
      completeness (representability) hypothesis. *)
  Definition Complete : Prop := forall x y, R x y -> erased x y.

  Theorem erasure_exact_of_complete :
    Complete -> forall x y, R x y <-> erased x y.
  Proof.
    intros H x y. split; [apply H | apply erasure_sound].
  Qed.

  (** Conversely, [Complete] is refuted by any [R]-related pair with no
      witness. *)
  Lemma not_complete_of_gap :
    forall x y, R x y -> ~ erased x y -> ~ Complete.
  Proof. intros x y Hr Hn Hc. exact (Hn (Hc x y Hr)). Qed.
End Erasure.

(** Erasure forgets construction/lineage: structures whose witness types are
    merely interconvertible have the same erased relation, however
    different the witnesses themselves are. *)
Lemma erased_only_sees_inhabitation
  {X R R'} (G : GTransport X R) (G' : GTransport X R') :
  (forall x y, (GT G x y -> GT G' x y) * (GT G' x y -> GT G x y))%type ->
  forall x y, erased G x y <-> erased G' x y.
Proof.
  intros H x y. split; intros [w]; apply inhabits.
  - exact (fst (H x y) w).
  - exact (snd (H x y) w).
Qed.
