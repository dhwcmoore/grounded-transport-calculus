(** * Grounded transport: the generic proof-relevant, directed judgement.

    [GT G x y] is the type of *evidence* that [x] may be transported to [y].
    It is a [Type], so witnesses are data (constructions, seams, lineage,
    authorisations), not mere truth values.  The structure is directed: no
    symmetry is required.

    [R] is the ordinary (extensional) relation that transport is sound for.
    Soundness is the only link between the two levels. *)


Record GTransport (X : Type) (R : X -> X -> Prop) : Type := {
  GT : X -> X -> Type;
  gt_refl : forall x, GT x x;
  gt_compose : forall x y z, GT x y -> GT y z -> GT x z;
  gt_sound : forall x y, GT x y -> R x y
}.

Arguments GT {X R} _ _ _.
Arguments gt_refl {X R} _ _.
Arguments gt_compose {X R} _ {x y z} _ _.
Arguments gt_sound {X R} _ {x y} _.

(** Milestone results 1 and 2, in the vocabulary of the design document. *)

Definition grounded_transport_refl {X R} (G : GTransport X R) (x : X)
  : GT G x x := gt_refl G x.

Definition grounded_transport_compose {X R} (G : GTransport X R)
  {x y z : X} (v : GT G x y) (w : GT G y z) : GT G x z :=
  gt_compose G v w.
