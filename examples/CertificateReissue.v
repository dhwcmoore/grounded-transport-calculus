(** * Certificate-level contextual preservation, and where it is impossible.

    Two stages, one seam element, as in [MaintenanceFailure.v].  A
    [ProblemMorphism] from the stage-0 problem to the stage-1 problem needs an
    EVIDENCE LIFT: a function from certified transports at stage 0 to certified
    transports at stage 1.

    - When the seam valuation stays grounded ([Vok]) the lift exists (the
      certificate is REISSUED at stage 1), so the seam evolution is
      [CertificateProper]: it maps full certified witnesses, not only crossings.
    - When grounding is lost ([V]) NO evidence lift exists: any lift would yield a
      certified transport at stage 1, whose grounding equations are false.

    So preservation of complete certificates fails exactly where maintenance of
    grounding fails, and the crossing-level and certificate-level notions are
    genuinely different. *)

From Coq Require Import List.
Import ListNotations.
From GTC.Debt Require Import Certificates EvidenceObligations GroundedWitness CertificateProper TransportAssessment.
From GTC.Instances Require Import OriginalGroundedSeamInstance OriginalDynamicSeamInstance.
From GTCExamples Require Import LineageCertificates MaintenanceFailure.
From Exactness Require Import GroundedSeam.

Definition cand_at (t : bool) (W : ValuedSystem sys) : EvCandidate :=
  {| ecA := unit; ecB := unit; ecOA := unit; ecOB := unit;
     ecSpan := sp sys t;
     ecMA := fun _ => tt; ecPA := vA W t;
     ecMB := fun _ => tt; ecPB := vB W t;
     ecPs := vS W t;
     ecLineage := indep_lineage [];
     ecMaintenance := unit; ecMaintenanceFailure := Empty_set;
     ecMaintenanceRefutes := fun f _ => match f with end;
     ecMaintenanceSummary := unit_summary;
     ecAuthorisation := AuthorisationCertificate unit (fun _ => True);
     ecAuthorisationFailure := Empty_set;
     ecAuthorisationRefutes := fun f _ => match f with end;
     ecAuthorisationSummary := authorisation_summary unit (fun _ => True) |}.

Definition exhibition_at (t : bool) (vs : bool -> bool)
  : ExhibitionCertificate (sp sys t) (vS (Vmk vs) t).
Proof.
  refine {| ex_record_id := 1; ex_identifier := fun _ => 0;
            ex_process := 1; ex_retained := bool;
            ex_retain := vS (Vmk vs) t; ex_evaluate := fun b => b;
            ex_evaluates := fun _ => eq_refl;
            ex_coverage := (0, 1); ex_custodian := 7 |}.
  intros r r' _. destruct r, r'. reflexivity.
Defined.

Lemma obs_at (t : bool) (vs : bool -> bool) :
  ObsEv (cand_at t (Vmk vs)).
Proof. split; exists (fun _ => true); intro s; reflexivity. Qed.

(** A certified transport at stage [t], provided the seam valuation is [true] there. *)
Definition ct_at (t : bool) (vs : bool -> bool) (H : vs t = true)
  : CertifiedTransport (cand_at t (Vmk vs)) :=
  @Build_CertifiedTransport (cand_at t (Vmk vs)) (obs_at t vs)
    (@Build_ConstructionCertificate (cand_at t (Vmk vs)) tt (exhibition_at t vs)
       (indep_certificate []) eq_refl
       (fun r => conj (eq_sym H) (eq_sym H)))
    tt auth.

(** ** Grounding kept: the certificate is reissued, and the evolution is
    certificate-proper. *)

Definition Vok_vs : bool -> bool := fun _ => true.

Definition reissue : ProblemMorphism (cand_at false (Vmk Vok_vs)) (cand_at true (Vmk Vok_vs)) :=
  @Build_ProblemMorphism (cand_at false (Vmk Vok_vs)) (cand_at true (Vmk Vok_vs))
    (fun _ => tt) (fun _ => tt) (fun _ => tt)
    (fun _ => eq_refl) (fun _ => eq_refl)
    (fun _ _ _ => conj eq_refl eq_refl)
    (fun _ => ct_at true Vok_vs eq_refl).

Theorem reissue_certificate_proper : CertificateProper (pm_state reissue).
Proof. exact (pm_certificate_proper reissue). Qed.

(** Hence, by the chain of implications, it is also crossing-proper and maps
    erased transports. *)
Definition reissue_crossing_proper := certificate_proper_crossing reissue_certificate_proper.

(** The crossing-level instance of the earlier development is a separate,
    weaker object: it needs no evidence, only preservation of grounding. *)
Check evolution_crossing_proper Vok e01 ok_preserves.

(** ** Grounding lost: no evidence lift exists. *)

Definition V_vs : bool -> bool := fun t => negb t.

Lemma stage0_certified : CertifiedTransport (cand_at false (Vmk V_vs)).
Proof. exact (ct_at false V_vs eq_refl). Qed.

Theorem no_evidence_lift_when_grounding_lost :
  ProblemMorphism (cand_at false (Vmk V_vs)) (cand_at true (Vmk V_vs)) -> False.
Proof.
  intro pm.
  pose proof (lift_gives_grounding pm stage0_certified tt) as [Ha _].
  cbn in Ha. discriminate Ha.
Qed.
