(** * From the checked lineage audit to located construction failures.

    A rejection by [lineage_check] carries proved evidence ([DefectEvidence]).
    [lineage_failure] turns it into the [ConstructionFailure] used by
    [TransportAssessment], so the checker feeds the assessment directly. *)

From GTC.Debt Require Import Certificates LineageCheck EvidenceObligations
  GroundedWitness TransportAssessment.

Lemma wf_evidence_not_wf g w : WfEvidence g w -> ~ LineageWellFormed g.
Proof.
  intros He (Hnd & Hd & HdA & HdB & Hg & Hrel & Hac).
  destruct w; cbn in He.
  - exact (He Hnd).
  - exact (He Hd).
  - exact (He (conj HdA (conj HdB Hg))).
  - exact (He Hrel).
  - exact (Hac n He).
Qed.

Definition lineage_failure (c : EvCandidate) (d : LineageDefect)
  : DefectEvidence (ecLineage c) d -> ConstructionFailure c :=
  match d as d0 return DefectEvidence (ecLineage c) d0 -> ConstructionFailure c with
  | Malformed w => fun H => LineageMalformed c (wf_evidence_not_wf _ w H)
  | GroundEqualsA => fun H => LineageCoordinateIdentity c (or_introl H)
  | GroundEqualsB => fun H => LineageCoordinateIdentity c (or_intror H)
  | DescentFromA => fun H => LineageDescent c (or_introl H)
  | DescentFromB => fun H => LineageDescent c (or_intror H)
  | UndisclosedShared n => fun H =>
      LineageUndisclosed c n (proj1 H) (proj1 (proj2 H))
        (proj1 (proj2 (proj2 H))) (proj2 (proj2 (proj2 H)))
  | NoIndependentSource => fun H => LineageNoIndependentSource c H
  end.

(** The failure built from a rejection refutes every construction certificate. *)
Corollary lineage_failure_refutes (c : EvCandidate) (d : LineageDefect)
    (H : DefectEvidence (ecLineage c) d) :
  ConstructionCertificate c -> False.
Proof. exact (construction_failure_refutes c (lineage_failure c d H)). Qed.

(** From a rejected check to a located failure, in one step. *)
Definition failure_of_rejection (c : EvCandidate) (cov : CoverageRecord)
    (d : LineageDefect) (H : lineage_check (ecLineage c) cov = LineageRejected d)
  : ConstructionFailure c :=
  lineage_failure c d (proj1 (lineage_check_rejected _ _ _ H)).
