(** * Ungrounded agreement.

    Extensional agreement ([R x y]) without a transport witness.  Its
    existence is a failure of *warrant*, not of extensional agreement, and it
    is exactly what blocks exact recovery of [R] by erasure. *)

From GTC.Core Require Import GroundedTransport Erasure.

Definition UngroundedAgreement {X R} (G : GTransport X R) (x y : X) : Prop :=
  R x y /\ ~ erased G x y.

Theorem ungrounded_agreement_not_complete {X R} (G : GTransport X R) x y :
  UngroundedAgreement G x y -> ~ Complete G.
Proof. intros [Hr Hn]. exact (not_complete_of_gap G x y Hr Hn). Qed.

(** Grounding entails agreement, never the reverse: *)
Theorem grounded_entails_agreement {X R} (G : GTransport X R) x y :
  erased G x y -> R x y.
Proof. exact (erasure_sound G x y). Qed.

Theorem no_exact_recovery_if_ungrounded {X R} (G : GTransport X R) x y :
  UngroundedAgreement G x y -> ~ (forall a b, R a b <-> erased G a b).
Proof.
  intros [Hr Hn] Hiff. exact (Hn (proj1 (Hiff x y) Hr)).
Qed.
