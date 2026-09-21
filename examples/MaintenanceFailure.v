(** * Maintenance failure: extensional persistence without grounded persistence.

    Two stages, one seam element.  Structural naturality holds throughout.

    DECLARED HISTORY (the "maintenance" reading is relative to it):
    1. construction was valid at issuance: at stage [false] the coordinates and
       the independent seam valuation all read [true], the seam is exhibited,
       and the declared lineage record passes;
    2. the system then evolved from [false] to [true];
    3. in [V] the seam valuation at stage [true] is [false] while the coordinates
       still read [true];
    4. observation and authority are declared discharged.

    Ordinary rewriting is oblivious to step 3.  The assessment is not. *)

From Coq Require Import List.
Import ListNotations.
From GTC.Core Require Import GroundedTransport Erasure.
From GTC.Debt Require Import Certificates Assessment EvidenceObligations
  GroundedWitness TransportAssessment MaintenanceDebt.
From GTC.Instances Require Import OriginalGroundedSeamInstance OriginalDynamicSeamInstance.
From GTCExamples Require Import LineageCertificates CopiedCoordinates.
From Exactness Require Import GroundedSeam.

Definition sys : TemporalSystem :=
  {| time := bool; A := fun _ => unit; B := fun _ => unit;
     sp := fun _ => {| seam := unit; back := fun _ => tt; fwd := fun _ => tt |} |}.

(** Coordinates always [true]; the seam valuation at stage [t] is [vs t]. *)
Definition Vmk (vs : bool -> bool) : ValuedSystem sys :=
  @Build_ValuedSystem sys (fun _ _ => true) (fun _ _ => true)
    (fun (t : bool) _ => vs t).

Definition V   := Vmk (fun t => negb t).   (* true at [false], false at [true] *)
Definition Vok := Vmk (fun _ => true).

Definition e01 : SeamEvolution sys false true :=
  @mkSeamEvolution sys false true (fun _ => tt) (fun _ => tt) (fun _ => tt)
    (fun _ => eq_refl) (fun _ => eq_refl).

(** ** 6. Dynamic failure is visible despite extensional persistence *)

Definition ExtAgreementAt (W : ValuedSystem sys) (t : bool) : Prop :=
  forall r : seam (sp sys t),
    vA W t (back (sp sys t) r) = vB W t (fwd (sp sys t) r).

Theorem dynamic_failure_visible :
  (* structural naturality *)
  ((forall r, back (sp sys true) (ev_seam e01 r) = ev_A e01 (back (sp sys false) r)) /\
   (forall r, fwd (sp sys true) (ev_seam e01 r) = ev_B e01 (fwd (sp sys false) r))) /\
  (* extensional agreement at both stages *)
  ExtAgreementAt V false /\ ExtAgreementAt V true /\
  (* grounded at t, not grounded at the transported element at u *)
  GroundedAt V false tt /\ ~ GroundedAt V true (ev_seam e01 tt).
Proof.
  refine (conj (conj (ev_back_commutes e01) (ev_fwd_commutes e01)) _).
  refine (conj (fun _ => eq_refl) (conj (fun _ => eq_refl) (conj _ _))).
  - split; reflexivity.
  - intros [Ha _]. cbn in Ha. discriminate Ha.
Qed.

(** Ordinary rewriting still succeeds at stage [true]: the extensional
    endpoint equation of [seam_transport] holds with the constant factor. *)
Theorem ordinary_rewriting_still_succeeds :
  forall r : seam (sp sys true),
    vB V true (fwd (sp sys true) r)
    = (fun _ : unit => true) ((fun _ : unit => tt) (back (sp sys true) r)).
Proof.
  intro r.
  exact (extensional_factor_transport (sp sys true) (vA V true) (vB V true)
           (fun _ : unit => tt) (fun _ : unit => true) (fun r' => eq_refl)
           (fun a => eq_refl) r).
Qed.

(** Structural naturality does not entail preservation of grounded coherence. *)
Theorem structural_naturality_not_preservation :
  ~ PreservesGroundingOnImage V e01.
Proof.
  intro M. destruct (M tt (conj eq_refl eq_refl)) as [Ha _]. cbn in Ha. discriminate Ha.
Qed.

(** ** The located maintenance failure *)

Lemma not_grounded_after (e : SeamEvolution sys false true) :
  ~ GroundedAt V true (ev_seam e tt).
Proof. intros [Ha _]. cbn in Ha. discriminate Ha. Qed.

Definition lost_grounding : MaintenanceFailureAt V false true :=
  inr (fun e => existT _ tt (conj (conj eq_refl eq_refl) (not_grounded_after e))).

(** ** The stage candidate *)

Definition auth : AuthorisationCertificate unit (fun _ => True) :=
  {| auth_authority := 1; auth_rule := tt; auth_licensed := I |}.

Definition stage_cand (W : ValuedSystem sys) (g : Lineage) : EvCandidate :=
  {| ecA := unit; ecB := unit; ecOA := unit; ecOB := unit;
     ecSpan := sp sys false;
     ecMA := fun _ => tt; ecPA := vA W false;
     ecMB := fun _ => tt; ecPB := vB W false;
     ecPs := vS W false;
     ecLineage := g;
     ecMaintenance := EvolutionMaintenanceEvidence W false true;
     ecMaintenanceFailure := MaintenanceFailureAt W false true;
     ecMaintenanceRefutes := maintenance_failure_refutes W false true;
     ecMaintenanceSummary := {| evidence_summary := fun _ => [AtomMaintenance 0 0 1] |};
     ecAuthorisation := AuthorisationCertificate unit (fun _ => True);
     ecAuthorisationFailure := Empty_set;
     ecAuthorisationRefutes := fun f _ => match f with end;
     ecAuthorisationSummary := authorisation_summary unit (fun _ => True) |}.

Definition stage_exhibition (vs : bool -> bool) (custodian : nat)
  : ExhibitionCertificate (sp sys false) (vS (Vmk vs) false).
Proof.
  refine {| ex_record_id := 1; ex_identifier := fun _ => 0;
            ex_process := 1; ex_retained := bool;
            ex_retain := vS (Vmk vs) false; ex_evaluate := fun b => b;
            ex_evaluates := fun _ => eq_refl;
            ex_coverage := (0, 1); ex_custodian := custodian |}.
  intros r r' _. destruct r, r'. reflexivity.
Defined.

Lemma stage_grounded (vs : bool -> bool) (H : vs false = true) :
  GroundingEquations (sp sys false) (vA (Vmk vs) false) (vB (Vmk vs) false)
                     (vS (Vmk vs) false).
Proof. intro r. cbn. split; symmetry; exact H. Qed.

Definition stage_cc (vs : bool -> bool) (H : vs false = true)
  : ConstructionCertificate (stage_cand (Vmk vs) (indep_lineage [])) :=
  @Build_ConstructionCertificate (stage_cand (Vmk vs) (indep_lineage [])) tt
    (stage_exhibition vs 7) (indep_certificate []) eq_refl (stage_grounded vs H).

Lemma stage_obs (vs : bool -> bool) (g : Lineage) : ObsEv (stage_cand (Vmk vs) g).
Proof. split; exists (fun _ => true); intro s; reflexivity. Qed.

(** ** 1. Maintenance fails: [Refuted], located *)

Definition failure_assessment : TransportAssessment (stage_cand V (indep_lineage [])) :=
  assemble _ (VDischarged (stage_obs _ _))
             (VDischarged (stage_cc _ eq_refl))
             (VFailed lost_grounding)
             (VDischarged auth).

Example maintenance_obstruction_reported :
  failure_assessment =
    Refuted (MaintenanceObstruction (stage_cand V (indep_lineage [])) lost_grounding, []).
Proof. reflexivity. Qed.

(** ** 2. Maintenance unassessed: [Open], not refuted *)

Definition open_assessment : TransportAssessment (stage_cand V (indep_lineage [])) :=
  assemble _ (VDischarged (stage_obs _ _))
             (VDischarged (stage_cc _ eq_refl))
             (VOpen NotYetAssessed)
             (VDischarged auth).

Example open_maintenance :
  open_assessment =
    Open [ {| oo_kind := MaintenanceDebt; oo_reason := NotYetAssessed |} ].
Proof. reflexivity. Qed.

(** ** 3. Grounded valuations: [Certified], carrying the evidence *)

Lemma ok_preserves : PreservesGroundingOnImage Vok e01.
Proof. intros r [ha hb]. split; reflexivity. Qed.

Definition certified_assessment : TransportAssessment (stage_cand Vok (indep_lineage [])) :=
  assemble _ (VDischarged (stage_obs _ _))
             (VDischarged (stage_cc _ eq_refl))
             (VDischarged (existT _ e01 ok_preserves))
             (VDischarged auth).

Example certified_carries_evidence :
  exists ct, certified_assessment = Certified ct.
Proof. eexists. reflexivity. Qed.

(** ** 4. Co-occurring obstructions

    The same maintenance failure, now with a COPIED ground: both the
    construction and the maintenance obligations fail.  The report contains
    both, located, in a fixed order. *)

Definition copy_construction_failure : ConstructionFailure (stage_cand V copy_lineage) :=
  LineageDescent (stage_cand V copy_lineage) (or_introl copy_descends).

Definition both_assessment : TransportAssessment (stage_cand V copy_lineage) :=
  assemble _ (VDischarged (stage_obs _ _))
             (VFailed copy_construction_failure)
             (VFailed lost_grounding)
             (VDischarged auth).

Example both_obstructions_reported :
  both_assessment =
    Refuted (ConstructionObstruction (stage_cand V copy_lineage) copy_construction_failure,
             [MaintenanceObstruction (stage_cand V copy_lineage) lost_grounding]).
Proof. reflexivity. Qed.

(** ** 5. A failure and an unresolved obligation together

    Copied ground (construction FAILED) and maintenance not yet assessed (OPEN).
    The verdict is [Refuted]; the report still lists the open obligation. *)

Definition refuted_and_open_report :=
  report_of (stage_cand V copy_lineage)
    (VDischarged (stage_obs _ _))
    (VFailed copy_construction_failure)
    (VOpen NotYetAssessed)
    (VDischarged auth).

Example refuted_verdict_keeps_open_item :
  report_verdict _ refuted_and_open_report = TransportRefuted /\
  rep_opens refuted_and_open_report =
    [ {| oo_kind := MaintenanceDebt; oo_reason := NotYetAssessed |} ] /\
  length (rep_failures refuted_and_open_report) = 1.
Proof. repeat split; reflexivity. Qed.
