(** * The original copied dual-write counterexample, assessed.

    Uses the legacy [dual_write], [copied_status], [trace_status] unchanged.

    DECLARED HISTORY (the "construction" reading is relative to it):
    - observation: the surface is adequate for the stated extensional predicate;
    - no temporal transition is declared, so maintenance is vacuous;
    - authority is assigned;
    - the ground [trace_status] was never independently constituted: the
      declared lineage record derives it from a coordinate ([copy_lineage]).
    Under this history exactly one obligation fails.  That is a statement about
    this fully specified problem; the manuscript's debt categories are
    diagnostic loci, not a partition. *)

From Coq Require Import List.
Import ListNotations.
From GTC.Core Require Import GroundedTransport Erasure.
From GTC.Obstructions Require Import UngroundedAgreement.
From GTC.Debt Require Import Certificates Assessment EvidenceObligations
  GroundedWitness TransportAssessment LineageCheck LineageAssessment.
From GTC.Instances Require Import OriginalGroundedSeamInstance.
From GTCExamples Require Import LineageCertificates.
From Exactness Require Import GroundedSeam.

Definition copied_ev : EvCandidate :=
  {| ecA := Req; ecB := Req; ecOA := unit; ecOB := unit; ecSpan := dual_write;
     ecMA := fun _ => tt; ecPA := copied_status;
     ecMB := fun _ => tt; ecPB := copied_status;
     ecPs := trace_status;
     ecLineage := copy_lineage;
     ecMaintenance := unit; ecMaintenanceFailure := Empty_set;
     ecMaintenanceRefutes := fun f _ => match f with end;
     ecMaintenanceSummary := unit_summary;
     ecAuthorisation := unit; ecAuthorisationFailure := Empty_set;
     ecAuthorisationRefutes := fun f _ => match f with end;
     ecAuthorisationSummary := unit_summary |}.

Lemma copied_obs : ObsEv copied_ev.
Proof. split; exists (fun _ => true); intro s; reflexivity. Qed.

(** The located construction failure: the ground descends from [d_A]. *)
Definition copied_failure : ConstructionFailure copied_ev :=
  LineageDescent copied_ev (or_introl copy_descends).

Lemma star_grounding_differs :
  copied_status r_star <> trace_status r_star.
Proof. intro H. discriminate H. Qed.

(** ... and, independently, grounding fails at [r_star]. *)
Definition copied_grounding_failure : ConstructionFailure copied_ev :=
  GroundingFailure copied_ev r_star (or_introl star_grounding_differs).

(** ** The assessment: [Refuted], with the located obstruction *)

Definition copied_assessment : TransportAssessment copied_ev :=
  assemble copied_ev
    (VDischarged copied_obs)
    (VFailed copied_failure)
    (VDischarged tt)
    (VDischarged tt).

Example copied_is_refuted_at_construction :
  copied_assessment = Refuted (ConstructionObstruction copied_ev copied_failure, []).
Proof. reflexivity. Qed.

(** Refutation soundness for this problem. *)
Corollary copied_not_certifiable : CertifiedTransport copied_ev -> False.
Proof.
  intro ct. exact (located_refutes copied_ev
                    (ConstructionObstruction copied_ev copied_failure) ct).
Qed.

(** ** 2. Ordinary substitutability does not reconstruct grounding *)

Lemma copied_rpath_trivial :
  forall x y, RPath copied_ev x y -> x = y.
Proof.
  intros x y w. induction w as [x|r ct|x y z w1 IH1 w2 IH2].
  - reflexivity.
  - exfalso. exact (copied_not_certifiable ct).
  - etransitivity; eassumption.
Qed.

Theorem erasure_not_reflecting :
  exists x y : rstate copied_ev,
    rval copied_ev x = rval copied_ev y /\ ~ ErasedTransport copied_ev x y.
Proof.
  exists (inl r_star), (inr r_star). split.
  - reflexivity.
  - intros [w]. discriminate (copied_rpath_trivial _ _ w).
Qed.

(** The same fact as generic [UngroundedAgreement]. *)
Corollary copied_ungrounded_agreement :
  UngroundedAgreement (rich_structure copied_ev) (inl r_star) (inr r_star).
Proof.
  split.
  - reflexivity.
  - intros [w]. discriminate (copied_rpath_trivial _ _ w).
Qed.

(** ** 5. The three outcomes differ: refuted, open, certified are not collapsed *)

(** Lineage record MISSING: the same problem is open, not refuted. *)
Definition copied_missing_lineage : TransportAssessment copied_ev :=
  assemble copied_ev
    (VDischarged copied_obs)
    (VOpen MissingLineageRecord)
    (VDischarged tt)
    (VDischarged tt).

Example missing_lineage_is_open :
  copied_missing_lineage =
    Open [ {| oo_kind := ConstructionDebt; oo_reason := MissingLineageRecord |} ].
Proof. reflexivity. Qed.

(** A partial lineage record: coverage-qualified, still open. *)
Definition copied_partial_lineage : TransportAssessment copied_ev :=
  assemble copied_ev
    (VDischarged copied_obs)
    (VOpen (CoverageGap [9]))
    (VDischarged tt)
    (VDischarged tt).

Example partial_lineage_is_open :
  copied_partial_lineage =
    Open [ {| oo_kind := ConstructionDebt; oo_reason := CoverageGap [9] |} ].
Proof. reflexivity. Qed.

(** The three statuses are pairwise distinct. *)
Example three_outcomes_distinct :
  tag copied_assessment <> tag copied_missing_lineage.
Proof. discriminate. Qed.

(** ** The located failure can come from the CHECKED audit

    The failure below is not hand-written: it is built from the proved evidence
    of a [lineage_check] rejection. *)

Definition copied_cov : CoverageRecord := {| cov_from := 0; cov_to := 1; cov_gaps := [] |}.

Lemma copied_lineage_rejected :
  lineage_check (ecLineage copied_ev) copied_cov = LineageRejected DescentFromA.
Proof. vm_compute. reflexivity. Qed.

Definition copied_failure_from_checker : ConstructionFailure copied_ev :=
  failure_of_rejection copied_ev copied_cov DescentFromA copied_lineage_rejected.

Definition copied_assessment_checked : TransportAssessment copied_ev :=
  assemble copied_ev
    (VDischarged copied_obs)
    (VFailed copied_failure_from_checker)
    (VDischarged tt)
    (VDischarged tt).

Example checked_assessment_refuted :
  tag copied_assessment_checked = TransportRefuted.
Proof. reflexivity. Qed.
