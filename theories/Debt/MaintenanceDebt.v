(** * Maintenance debt, tied to [SeamEvolution].

    The maintenance obligation between stage [t] and stage [u] is the
    existence of a legacy [SeamEvolution] (commuting back/fwd squares) that
    also preserves grounding on the image of its seam map.  It yields a grounded-proper context; its failure is
    a maintenance debt even when extensional agreement persists (see
    examples/MaintenanceFailure.v). *)

From GTC.Core Require Import GroundedTransport.
From GTC.Contexts Require Import GroundedProper.
From GTC.Instances Require Import OriginalGroundedSeamInstance OriginalDynamicSeamInstance.
From Exactness Require Import GroundedSeam.

Section Maintenance.
  Context {X : TemporalSystem} (V : ValuedSystem X).

  Definition EvolutionMaintained (t u : time X) : Prop :=
    exists e : SeamEvolution X t u, PreservesGroundingOnImage V e.

  (** Proof-relevant form: the evolution itself, together with its
      preservation proof, is the evidence. *)
  Definition EvolutionMaintenanceEvidence (t u : time X) : Type :=
    { e : SeamEvolution X t u & PreservesGroundingOnImage V e }.

  Lemma maintained_iff_evidence (t u : time X) :
    EvolutionMaintained t u <-> inhabited (EvolutionMaintenanceEvidence t u).
  Proof.
    split.
    - intros [e M]. exact (inhabits (existT _ e M)).
    - intros [[e M]]. exists e. exact M.
  Qed.

  Theorem maintained_gives_grounded_proper (t u : time X) :
    EvolutionMaintained t u ->
    exists F, inhabited (GroundedProper (gstr V t) (gstr V u) F).
  Proof.
    intros [e M]. exists (evo_state e).
    exact (inhabits (original_grounding_preserving_evolution_is_grounded_proper V e M)).
  Qed.

  (** Located maintenance failure: either no structural evolution exists, or
      EVERY structural evolution loses grounding at a named seam element
      (grounded at [t], not grounded at its image at [u]).  This is data, not
      [false]. *)
  Definition MaintenanceFailureAt (t u : time X) : Type :=
    ((SeamEvolution X t u -> False) +
     (forall e : SeamEvolution X t u,
        { r : seam (sp X t) & GroundedAt V t r /\ ~ GroundedAt V u (ev_seam e r) }))%type.

  Lemma maintenance_failure_refutes (t u : time X) :
    MaintenanceFailureAt t u -> EvolutionMaintenanceEvidence t u -> False.
  Proof.
    intros [f|f] [e M].
    - exact (f e).
    - destruct (f e) as [r [g ng]]. exact (ng (M r g)).
  Qed.

  Lemma maintained_refl (t : time X) : EvolutionMaintained t t.
  Proof. exists (evolution_id X t). apply preserves_id. Qed.

  Lemma maintained_trans (t u v : time X) :
    EvolutionMaintained t u -> EvolutionMaintained u v -> EvolutionMaintained t v.
  Proof.
    intros [e1 M1] [e2 M2]. exists (evolution_compose e1 e2).
    exact (preserves_compose V e1 e2 M1 M2).
  Qed.
End Maintenance.
