(** * Lineage obstruction: observational equivalence does not license
    substitution for lineage-sensitive predicates. *)

From Coq Require Import Classes.Morphisms Classes.RelationClasses.
From GTC.Core Require Import GroundedTransport Erasure.
From GTC.Obstructions Require Import FibreObstruction.

Section Lineage.
  Context {X O V : Type} (M : X -> O) (P : X -> V).

  Definition obs_equiv (x y : X) : Prop := M x = M y.

  (** [x ~_M y /\ P x <> P y  ==>  ~ Proper (~_M ==> eq) P]. *)
  Theorem not_proper_of_distinguished :
    forall x y, obs_equiv x y -> P x <> P y ->
      ~ Proper (obs_equiv ==> eq) P.
  Proof.
    intros x y Hobs Hne Hp. exact (Hne (Hp x y Hobs)).
  Qed.

  Theorem observational_insufficient :
    forall x y, obs_equiv x y -> P x <> P y -> ~ Factors M P.
  Proof. intros x y H1 H2. exact (fibre_obstruction M P x y H1 H2). Qed.

  (** Stronger, grounded reading: if grounded transport is sound for
      [P]-agreement, then observational equivalence does not yield a
      transport witness for any pair that [P] distinguishes. *)
  Theorem observational_not_grounded :
    forall (G : GTransport X (fun x y => P x = P y)) x y,
      obs_equiv x y -> P x <> P y -> ~ erased G x y.
  Proof.
    intros G x y _ Hne He. exact (Hne (erasure_sound G x y He)).
  Qed.

  (** Consequently observational equivalence cannot be complete for any such
      structure. *)
  Corollary obs_equiv_not_transport :
    forall (G : GTransport X (fun x y => P x = P y)) x y,
      obs_equiv x y -> P x <> P y -> ~ (forall a b, obs_equiv a b -> erased G a b).
  Proof.
    intros G x y H1 H2 Hall. exact (observational_not_grounded G x y H1 H2 (Hall x y H1)).
  Qed.
End Lineage.
