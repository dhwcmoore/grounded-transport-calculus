(** * Pairwise lineage audits do not imply an outer audit.

    Each family fixes every field except the two coordinates: the declared
    graph, raw inputs, relevant inputs, dispositions and ground are identical
    for AB, BC and AC. No lineage composition operator is assumed.
    The first countermodel isolates L2; the second isolates L3. *)

From Coq Require Import List.
Import ListNotations.
From GTC.Debt Require Import Certificates LineageCheck.

Definition noncomposition_coverage : CoverageRecord :=
  {| cov_from := 0; cov_to := 1; cov_gaps := [] |}.

(** Disclosure countermodel. Only the coordinates vary. *)
Definition disclosure_lineage (a b : nat) : Lineage :=
  {| lin_derived := [(4, [0]); (5, [4]); (6, [1]); (7, [4]); (8, [3])];
     lin_raw := [0; 1; 2; 3]; lin_relevant := [3];
     lin_dA := a; lin_dB := b; lin_ground := 8;
     lin_dispositions := [] |}.

Definition disclosure_AB := disclosure_lineage 5 6.
Definition disclosure_BC := disclosure_lineage 6 7.
Definition disclosure_AC := disclosure_lineage 5 7.

Example disclosure_AB_accepted :
  lineage_check disclosure_AB noncomposition_coverage = LineageAccepted.
Proof. vm_compute. reflexivity. Qed.

Lemma disclosure_AB_passes : LineagePasses disclosure_AB.
Proof.
  exact (proj1 (proj1 (lineage_check_reflect _ _) disclosure_AB_accepted)).
Qed.

Example disclosure_BC_accepted :
  lineage_check disclosure_BC noncomposition_coverage = LineageAccepted.
Proof. vm_compute. reflexivity. Qed.

Lemma disclosure_BC_passes : LineagePasses disclosure_BC.
Proof.
  exact (proj1 (proj1 (lineage_check_reflect _ _) disclosure_BC_accepted)).
Qed.

Lemma disclosure_AC_wf : LineageWellFormed disclosure_AC.
Proof. apply (proj1 (wf_defect_none_iff _)). vm_compute. reflexivity. Qed.

Lemma disclosure_AC_declared : DeclParents disclosure_AC.
Proof.
  apply decl_parents_of_entries.
  exact (proj1 (proj2 disclosure_AC_wf)).
Qed.

Lemma disclosure_AC_L1 : L1 disclosure_AC.
Proof.
  apply (proj1 (check_L1_reflect _ disclosure_AC_declared)).
  vm_compute. reflexivity.
Qed.

Lemma disclosure_AC_L3 : L3 disclosure_AC.
Proof.
  apply (proj1 (check_L3_reflect _ disclosure_AC_declared)).
  vm_compute. reflexivity.
Qed.

Lemma disclosure_AC_not_L2 : ~ L2 disclosure_AC.
Proof.
  intro H. apply (proj2 (undisclosed_none_iff _ disclosure_AC_declared)) in H.
  vm_compute in H. discriminate.
Qed.

Example disclosure_AC_rejected :
  lineage_check disclosure_AC noncomposition_coverage =
    LineageRejected (UndisclosedShared 4).
Proof. vm_compute. reflexivity. Qed.

Lemma disclosure_AC_not_passes : ~ LineagePasses disclosure_AC.
Proof.
  intros (_ & _ & H & _). exact (disclosure_AC_not_L2 H).
Qed.

Theorem disclosure_noncomposition :
  LineagePasses disclosure_AB /\ LineagePasses disclosure_BC /\
  LineageWellFormed disclosure_AC /\
  L1 disclosure_AC /\ L3 disclosure_AC /\ ~ L2 disclosure_AC /\
  ~ LineagePasses disclosure_AC.
Proof.
  exact (conj disclosure_AB_passes (conj disclosure_BC_passes
    (conj disclosure_AC_wf (conj disclosure_AC_L1
      (conj disclosure_AC_L3 (conj disclosure_AC_not_L2 disclosure_AC_not_passes)))))).
Qed.

(** Source countermodel. Only the coordinates vary. *)
Definition source_lineage (a b : nat) : Lineage :=
  {| lin_derived := [(3, [1]); (4, [2]); (5, [0]); (6, [0; 1])];
     lin_raw := [0; 1; 2]; lin_relevant := [0; 1];
     lin_dA := a; lin_dB := b; lin_ground := 6;
     lin_dispositions := [] |}.

Definition source_AB := source_lineage 3 4.
Definition source_BC := source_lineage 4 5.
Definition source_AC := source_lineage 3 5.

Example source_AB_accepted :
  lineage_check source_AB noncomposition_coverage = LineageAccepted.
Proof. vm_compute. reflexivity. Qed.

Lemma source_AB_passes : LineagePasses source_AB.
Proof.
  exact (proj1 (proj1 (lineage_check_reflect _ _) source_AB_accepted)).
Qed.

Example source_BC_accepted :
  lineage_check source_BC noncomposition_coverage = LineageAccepted.
Proof. vm_compute. reflexivity. Qed.

Lemma source_BC_passes : LineagePasses source_BC.
Proof.
  exact (proj1 (proj1 (lineage_check_reflect _ _) source_BC_accepted)).
Qed.

Lemma source_AC_wf : LineageWellFormed source_AC.
Proof. apply (proj1 (wf_defect_none_iff _)). vm_compute. reflexivity. Qed.

Lemma source_AC_declared : DeclParents source_AC.
Proof.
  apply decl_parents_of_entries.
  exact (proj1 (proj2 source_AC_wf)).
Qed.

Lemma source_AC_L1 : L1 source_AC.
Proof.
  apply (proj1 (check_L1_reflect _ source_AC_declared)).
  vm_compute. reflexivity.
Qed.

Lemma source_AC_L2 : L2 source_AC.
Proof.
  apply (proj1 (undisclosed_none_iff _ source_AC_declared)).
  vm_compute. reflexivity.
Qed.

Lemma source_AC_not_L3 : ~ L3 source_AC.
Proof.
  intro H. apply (proj2 (check_L3_reflect _ source_AC_declared)) in H.
  vm_compute in H. discriminate.
Qed.

Example source_AC_rejected :
  lineage_check source_AC noncomposition_coverage =
    LineageRejected (NoIndependentSource).
Proof. vm_compute. reflexivity. Qed.

Lemma source_AC_not_passes : ~ LineagePasses source_AC.
Proof.
  intros (_ & _ & _ & H). exact (source_AC_not_L3 H).
Qed.

Theorem source_noncomposition :
  LineagePasses source_AB /\ LineagePasses source_BC /\
  LineageWellFormed source_AC /\
  L1 source_AC /\ L2 source_AC /\ ~ L3 source_AC /\
  ~ LineagePasses source_AC.
Proof.
  exact (conj source_AB_passes (conj source_BC_passes
    (conj source_AC_wf (conj source_AC_L1
      (conj source_AC_L2 (conj source_AC_not_L3 source_AC_not_passes)))))).
Qed.
