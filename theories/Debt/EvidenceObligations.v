(** * Evidence-bearing obligations for an original grounded-seam candidate.

    Compared with [OriginalObligations.v] (Prop slots [Exhibited],
    [LineageGrounded], [Functorial], matching the legacy [Transportable]), the
    slots here are TYPES that carry certificates:

    | Debt          | Evidence type                                          |
    |---------------|--------------------------------------------------------|
    | Observational | [Admissible M_A Phi_A] and [Admissible M_B Phi_B]      |
    | Construction  | [ConstructionCertificate]: inhabitant, exhibition      |
    |               | certificate, lineage certificate for the DECLARED      |
    |               | lineage record, original grounding equations           |
    | Maintenance   | [ecMaintenance] (e.g. an evolution that preserves      |
    |               | grounding, [EvolutionMaintenanceEvidence])             |
    | Institutional | [ecAuthorisation] (e.g. an [AuthorisationCertificate]) |

    The legacy Props are recovered by erasure ([certified_gives_transportable]);
    a construction certificate also yields grounded transport witnesses
    ([construction_witness]) and hence, by erasure, extensional agreement. *)

From Coq Require Import Bool.
From GTC.Core Require Import GroundedTransport Erasure.
From GTC.Debt Require Import Certificates Assessment.
From GTC.Instances Require Import OriginalGroundedSeamInstance.
From Exactness Require Import GroundedSeam.

Record EvCandidate : Type := {
  ecA : Type;  ecB : Type;  ecOA : Type;  ecOB : Type;
  ecSpan : Span ecA ecB;
  ecMA : ecA -> ecOA;  ecPA : ecA -> bool;
  ecMB : ecB -> ecOB;  ecPB : ecB -> bool;
  ecPs : seam ecSpan -> bool;
  ecLineage : Lineage;             (* the DECLARED lineage record *)
  ecMaintenance : Type;            (* what would discharge maintenance   *)
  ecMaintenanceFailure : Type;     (* located ways maintenance can fail  *)
  ecMaintenanceRefutes : ecMaintenanceFailure -> ecMaintenance -> False;
  ecMaintenanceSummary : EvidenceSummary ecMaintenance;
  ecAuthorisation : Type;          (* what would discharge institutional *)
  ecAuthorisationFailure : Type;   (* located ways authorisation can fail *)
  ecAuthorisationRefutes : ecAuthorisationFailure -> ecAuthorisation -> False;
  ecAuthorisationSummary : EvidenceSummary ecAuthorisation
}.

Record ConstructionCertificate (c : EvCandidate) : Type := {
  cc_inhabitant : seam (ecSpan c);
  cc_exhibition : ExhibitionCertificate (ecSpan c) (ecPs c);
  cc_lineage : LineageCertificate;
  cc_lineage_declared : lc_graph cc_lineage = ecLineage c;
  cc_grounding : GroundingEquations (ecSpan c) (ecPA c) (ecPB c) (ecPs c)
}.
Arguments cc_inhabitant {c} _.
Arguments cc_exhibition {c} _.
Arguments cc_lineage {c} _.
Arguments cc_lineage_declared {c} _.
Arguments cc_grounding {c} _.

Definition ev_obligations : EvObligations EvCandidate :=
  {| EObs := fun c => Admissible (ecMA c) (ecPA c) /\ Admissible (ecMB c) (ecPB c);
     ECons := ConstructionCertificate;
     EMaint := ecMaintenance;
     EInst := ecAuthorisation |}.

(** Erasure back to the legacy [Transportable] (whose institutional component
    is absent by design): each evidence type erases to [inhabited]. *)
Theorem certified_gives_transportable (c : EvCandidate) :
  EvTransport ev_obligations c ->
  Transportable (ecSpan c) (ecMA c) (ecPA c) (ecMB c) (ecPB c) (ecPs c)
    (inhabited (ExhibitionCertificate (ecSpan c) (ecPs c)))
    (LineagePasses (ecLineage c))
    (inhabited (ecMaintenance c)).
Proof.
  intros ((( [oa ob] & cc) & m) & _).
  refine (conj (inhabits (cc_inhabitant cc)) (conj _ (conj _ (conj _ (conj _ (conj _ _)))))).
  - exact (inhabits (cc_exhibition cc)).
  - rewrite <- (cc_lineage_declared cc). exact (lineage_certificate_passes (cc_lineage cc)).
  - exact oa.
  - exact ob.
  - exact (cc_grounding cc).
  - exact (inhabits m).
Qed.

(** A construction certificate yields a grounded transport witness at every seam
    element ... *)
Definition construction_witness (c : EvCandidate) (cc : ConstructionCertificate c)
    (r : seam (ecSpan c))
  : GT (orig_structure (ecSpan c) (ecPA c) (ecPB c) (ecPs c))
       (inl (back (ecSpan c) r)) (inr (fwd (ecSpan c) r)) :=
  grounding_gives_crossing (ecSpan c) (ecPA c) (ecPB c) (ecPs c)
    (cc_grounding cc) r.

(** ... whose erasure is extensional agreement. *)
Corollary certified_erases_to_agreement (c : EvCandidate)
    (cc : ConstructionCertificate c) :
  forall r, ecPA c (back (ecSpan c) r) = ecPB c (fwd (ecSpan c) r).
Proof.
  intro r.
  exact (erasure_sound
           (orig_structure (ecSpan c) (ecPA c) (ecPB c) (ecPs c)) _ _
           (erase _ (construction_witness c cc r))).
Qed.

(** The exhibited valuation is a function of what the record retains. *)
Corollary certified_valuation_factors (c : EvCandidate)
    (cc : ConstructionCertificate c) :
  Admissible (ex_retain (cc_exhibition cc)) (ecPs c).
Proof. exact (exhibition_valuation_admissible (cc_exhibition cc)). Qed.
