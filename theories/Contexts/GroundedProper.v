(** * Witness-preserving contexts (generic).

    [GroundedProper GX GY F] is PARAMETRIC in the two transport structures: what it
    preserves is whatever the structures carry.  Instantiated at the CROSSING
    structure (no certificates) it is the crossing-level notion, packaged with an
    action on crossed seam elements as [CrossingProper]; instantiated at the
    certified-witness structure it preserves complete certificates and, with the
    commutation-with-erasure condition, is [CertificateProper]
    (theories/Debt/CertificateProper.v).  The name is historical: prefer
    [CrossingProper] / [CertificateProper] when the level matters.

    Ordinary [Proper] preserves a relation; this preserves the WARRANT for it,
    to the extent the chosen structure records it. *)

From GTC.Core Require Import GroundedTransport.

Record GroundedProper {X Y RX RY}
  (GX : GTransport X RX) (GY : GTransport Y RY) (F : X -> Y) : Type := {
  gp_map : forall x y, GT GX x y -> GT GY (F x) (F y);
  gp_map_refl : forall x,
    gp_map x x (gt_refl GX x) = gt_refl GY (F x);
  gp_map_compose : forall x y z (v : GT GX x y) (w : GT GX y z),
    gp_map x z (gt_compose GX v w)
    = gt_compose GY (gp_map x y v) (gp_map y z w)
}.

Arguments gp_map {X Y RX RY GX GY F} _ {x y} _.
Arguments gp_map_refl {X Y RX RY GX GY F} _ _.
Arguments gp_map_compose {X Y RX RY GX GY F} _ {x y z} _ _.

Definition gp_id {X R} (G : GTransport X R)
  : GroundedProper G G (fun x => x).
Proof.
  refine {| gp_map := fun x y w => w |}; reflexivity.
Defined.

(** Milestone result 4: composition of grounded-proper contexts. *)
Definition gp_comp {X Y Z RX RY RZ}
  {GX : GTransport X RX} {GY : GTransport Y RY} {GZ : GTransport Z RZ}
  {F : X -> Y} {H : Y -> Z}
  (P : GroundedProper GX GY F) (Q : GroundedProper GY GZ H)
  : GroundedProper GX GZ (fun x => H (F x)).
Proof.
  refine {| gp_map := fun x y w => gp_map Q (gp_map P w) |}.
  - intro x. cbn. rewrite (gp_map_refl P x). apply (gp_map_refl Q).
  - intros x y z v w. cbn.
    rewrite (gp_map_compose P v w). apply (gp_map_compose Q).
Defined.

Definition grounded_proper_compose := @gp_comp.
