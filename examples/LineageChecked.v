(** * The checked lineage audit on the example graphs.

    [lineage_check] is proved to reflect [LineagePasses] (Debt/LineageCheck.v);
    here it is run.  The hand-written certificate proofs of
    [LineageCertificates.v] are no longer needed for accepted graphs:
    [issue_certificate] constructs the certificate. *)

From Coq Require Import List.
Import ListNotations.
From GTC.Debt Require Import Certificates LineageCheck.
From GTCExamples Require Import LineageCertificates.

Definition full_coverage : CoverageRecord := {| cov_from := 0; cov_to := 1; cov_gaps := [] |}.
Definition gappy_coverage : CoverageRecord := {| cov_from := 0; cov_to := 1; cov_gaps := [9] |}.

Example independent_accepted :
  lineage_check (indep_lineage []) full_coverage = LineageAccepted.
Proof. vm_compute. reflexivity. Qed.

Example copied_rejected_with_location :
  lineage_check copy_lineage full_coverage = LineageRejected DescentFromA.
Proof. vm_compute. reflexivity. Qed.

Example partial_record_is_open_not_rejected :
  lineage_check (indep_lineage []) gappy_coverage = LineageOpen [9].
Proof. vm_compute. reflexivity. Qed.

(** A defect wins over a coverage gap: a proved failure is not merely open. *)
Example defect_beats_gap :
  lineage_check copy_lineage gappy_coverage = LineageRejected DescentFromA.
Proof. vm_compute. reflexivity. Qed.

(** The certificate is CONSTRUCTED by the checker, carrying graph and coverage. *)
Example issued_for_independent :
  exists cert, issue_certificate (indep_lineage []) full_coverage = Some cert /\
               lc_graph cert = indep_lineage [] /\ lc_coverage cert = full_coverage.
Proof.
  destruct (proj2 (issue_certificate_iff _ _) independent_accepted) as [cert H].
  exists cert. destruct (issue_certificate_data _ _ _ H) as [G C]. auto.
Qed.

Example not_issued_for_copy : issue_certificate copy_lineage full_coverage = None.
Proof. vm_compute. reflexivity. Qed.

(** A cycle and an undisclosed shared ancestor, on small hand graphs. *)
Definition cyclic_lineage : Lineage :=
  {| lin_derived := [(1, [2]); (2, [1]); (3, [0]); (4, [0])];
     lin_raw := [0]; lin_relevant := [0];
     lin_dA := 3; lin_dB := 4; lin_ground := 1; lin_dispositions := [] |}.

Example cycle_detected :
  lineage_check cyclic_lineage full_coverage = LineageRejected (Malformed (Cycle 1)).
Proof. vm_compute. reflexivity. Qed.

(** A shared non-raw ancestor (node 5) feeding both coordinates, undisclosed. *)
Definition shared_lineage (disp : list (nat * Disposition)) : Lineage :=
  {| lin_derived := [(5, [0]); (3, [5]); (4, [5]); (6, [1])];
     lin_raw := [0; 1]; lin_relevant := [1];
     lin_dA := 3; lin_dB := 4; lin_ground := 6; lin_dispositions := disp |}.

Example undisclosed_detected :
  lineage_check (shared_lineage []) full_coverage = LineageRejected (UndisclosedShared 5).
Proof. vm_compute. reflexivity. Qed.

Example disclosed_accepted :
  lineage_check (shared_lineage [(5, OpenDefeater 1)]) full_coverage = LineageAccepted.
Proof. vm_compute. reflexivity. Qed.
