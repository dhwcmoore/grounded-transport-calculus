(** * A genuinely grounded seam: the original [seam_transport], recovered from
    the generic calculus, on concrete data. *)

From GTC.Core Require Import Erasure.
From GTC.Instances Require Import OriginalGroundedSeamInstance.
From Exactness Require Import GroundedSeam.

(** A = B = nat, one seam element; both coordinates and the independent seam
    valuation all read [true] there. *)
Definition one_span : Span nat nat :=
  {| seam := unit; back := fun _ => 4; fwd := fun _ => 10 |}.

Definition seam_val : seam one_span -> bool := fun _ => true.

Lemma one_span_grounded :
  GroundingEquations one_span Nat.even Nat.even seam_val.
Proof. intro r. split; reflexivity. Qed.

Example transport_on_one_span :
  forall r : seam one_span,
    Nat.even (fwd one_span r) = (fun b : bool => b) (Nat.even (back one_span r)).
Proof.
  intro r.
  exact (original_seam_transport_from_generic one_span Nat.even Nat.even seam_val
           Nat.even one_span_grounded (fun b => b) (fun a => eq_refl) r).
Qed.

Example crossing_erases :
  erased (orig_structure one_span Nat.even Nat.even seam_val) (inl 4) (inr 10).
Proof.
  exact (erase _ (grounding_gives_crossing one_span Nat.even Nat.even seam_val
                    one_span_grounded tt)).
Qed.
