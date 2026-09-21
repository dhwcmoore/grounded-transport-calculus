(** * Contextual preservation.

    Generic theorem: a grounded-proper context transports valid grounded
    witnesses, and nested contexts transport them compositionally. *)

From Coq Require Import Classes.Morphisms.
From GTC.Core Require Import GroundedTransport Erasure.
From GTC.Contexts Require Import GroundedProper.

Section Preservation.
  Context {X Y RX RY} {GX : GTransport X RX} {GY : GTransport Y RY}
          {F : X -> Y} (P : GroundedProper GX GY F).

  (** [w : GTrans(x,y)  ==>  map_C w : GTrans(C[x], C[y])]. *)
  Theorem contextual_preservation :
    forall x y, GT GX x y -> GT GY (F x) (F y).
  Proof. intros x y w. exact (gp_map P w). Qed.

  (** Preservation lifts to the erased relation. *)
  Theorem grounded_proper_erased :
    forall x y, erased GX x y -> erased GY (F x) (F y).
  Proof. intros x y [w]. exact (erase GY (gp_map P w)). Qed.

  (** ... and to the ordinary relations it is sound for. *)
  Corollary grounded_proper_sound :
    forall x y, GT GX x y -> RY (F x) (F y).
  Proof. intros x y w. exact (gt_sound GY (gp_map P w)). Qed.

  (** Connection to Rocq's [Proper]. *)
  Global Instance grounded_proper_Proper :
    Proper (erased GX ==> erased GY) F.
  Proof. intros x y H. exact (grounded_proper_erased x y H). Qed.
End Preservation.

(** Nesting: the witness map of a composite context is the composite of the
    witness maps. *)
Theorem contextual_preservation_nested
  {X Y Z RX RY RZ} {GX : GTransport X RX} {GY : GTransport Y RY}
  {GZ : GTransport Z RZ} {F : X -> Y} {H : Y -> Z}
  (P : GroundedProper GX GY F) (Q : GroundedProper GY GZ H)
  {x y} (w : GT GX x y) :
  gp_map (gp_comp P Q) w = gp_map Q (gp_map P w).
Proof. reflexivity. Qed.
