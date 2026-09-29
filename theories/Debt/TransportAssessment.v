(** * Evidence-bearing transport assessment.

        Certified w   here is the evidence that warrants transport;
        Refuted os    here are LOCATED obstructions (a non-empty collection,
                      since the categories can co-occur);
        Open ds       neither certified nor refuted: NAMED obligations remain
                      unresolved.

    Everything is in [Type].  A failure is not [false]: it is a fibre witness, a
    seam element on which grounding fails, a lineage ancestor path, a lost
    grounding, ...  Open is not refutation: a missing lineage record, a
    coverage gap and an incomplete search are [Open]; only a proved defect is
    [Refuted].

    INDEXING.  Assessments are indexed by the transport PROBLEM (an
    [EvCandidate]), not by a pair of states.  A pair-indexed [Refuted] would be
    wrong at reflexive pairs, where [rp_refl] needs no certificate.  Pair-level
    witnesses are derived: a [Certified] assessment yields an [RPath] at every
    seam crossing ([certified_witness_at]).

    LIMITS.  A certified assessment says: given these declared records and their
    checks, transport is warranted within the formal regime.  It does not show
    the declared lineage includes every real production path, that raw inputs
    are accurate, that the state model fits the target, that an authority is
    competent, or that the seam is what actually happened.  Those are
    construction and institutional debt. *)

From Coq Require Import List Bool.
Import ListNotations.
From GTC.Core Require Import GroundedTransport Erasure.
From GTC.Debt Require Import Certificates Assessment EvidenceObligations GroundedWitness.
From GTC.Instances Require Import OriginalGroundedSeamInstance.
From Exactness Require Import GroundedSeam.

(** ** Located failures *)

Record FibreWitness {S O : Type} (M : S -> O) (Phi : S -> bool) : Type := {
  fw_s1 : S;  fw_s2 : S;
  fw_obs_eq : M fw_s1 = M fw_s2;
  fw_ne : Phi fw_s1 <> Phi fw_s2
}.

Lemma fibre_witness_refutes {S O} (M : S -> O) (Phi : S -> bool) :
  FibreWitness M Phi -> Admissible M Phi -> False.
Proof.
  intros [s1 s2 Heq Hne] [h Hh]. apply Hne.
  rewrite (Hh s1), (Hh s2), Heq. reflexivity.
Qed.

Inductive ObservationalFailure (c : EvCandidate) : Type :=
| ObsFailA : FibreWitness (ecMA c) (ecPA c) -> ObservationalFailure c
| ObsFailB : FibreWitness (ecMB c) (ecPB c) -> ObservationalFailure c.

Inductive ConstructionFailure (c : EvCandidate) : Type :=
| SeamEmpty : (seam (ecSpan c) -> False) -> ConstructionFailure c
| GroundingFailure : forall r : seam (ecSpan c),
    (ecPA c (back (ecSpan c) r) <> ecPs c r \/ ecPB c (fwd (ecSpan c) r) <> ecPs c r) ->
    ConstructionFailure c
| ExhibitionDefeated :
    (ExhibitionCertificate (ecSpan c) (ecPs c) -> False) -> ConstructionFailure c
| LineageCoordinateIdentity :
    (lin_ground (ecLineage c) = lin_dA (ecLineage c) \/
     lin_ground (ecLineage c) = lin_dB (ecLineage c)) ->
    ConstructionFailure c
| LineageDescent :
    (Ancestor (ecLineage c) (lin_ground (ecLineage c)) (lin_dA (ecLineage c)) \/
     Ancestor (ecLineage c) (lin_ground (ecLineage c)) (lin_dB (ecLineage c))) ->
    ConstructionFailure c
| LineageUndisclosed : forall n : nat,
    Ancestor (ecLineage c) (lin_dA (ecLineage c)) n ->
    Ancestor (ecLineage c) (lin_dB (ecLineage c)) n ->
    ~ lin_is_raw (ecLineage c) n -> ~ lin_disposed (ecLineage c) n ->
    ConstructionFailure c
| LineageNoIndependentSource : ~ L3 (ecLineage c) -> ConstructionFailure c
| LineageMalformed : ~ LineageWellFormed (ecLineage c) -> ConstructionFailure c.

Inductive Located (c : EvCandidate) : Type :=
| ObservationalObstruction : ObservationalFailure c -> Located c
| ConstructionObstruction : ConstructionFailure c -> Located c
| MaintenanceObstruction : ecMaintenanceFailure c -> Located c
| InstitutionalObstruction : ecAuthorisationFailure c -> Located c.

(** A non-empty collection: head and tail. *)
Definition Obstructions (c : EvCandidate) : Type := (Located c * list (Located c))%type.

(** ** Each located failure refutes the corresponding evidence *)

Lemma observational_failure_refutes c :
  ObservationalFailure c ->
  (Admissible (ecMA c) (ecPA c) /\ Admissible (ecMB c) (ecPB c)) -> False.
Proof.
  intros [w|w] [a b]; [exact (fibre_witness_refutes _ _ w a) | exact (fibre_witness_refutes _ _ w b)].
Qed.

Lemma construction_failure_refutes c :
  ConstructionFailure c -> ConstructionCertificate c -> False.
Proof.
  intros f cc.
  pose proof (lineage_certificate_passes (cc_lineage cc)) as (wf & l1 & l2 & l3).
  rewrite (cc_lineage_declared cc) in wf, l1, l2, l3.
  destruct l1 as (Hga & Hgb & Hda & Hdb).
  destruct f as [e|r H|e|[H|H]|[H|H]|n H1 H2 H3 H4|H|H].
  - exact (e (cc_inhabitant cc)).
  - destruct (cc_grounding cc r) as [ga gb]. destruct H as [H|H]; [exact (H ga) | exact (H gb)].
  - exact (e (cc_exhibition cc)).
  - exact (Hga H).
  - exact (Hgb H).
  - exact (Hda H).
  - exact (Hdb H).
  - exact (H4 (l2 n H1 H2 H3)).
  - exact (H l3).
  - exact (H wf).
Qed.

Definition located_refutes c (l : Located c) (ct : CertifiedTransport c) : False :=
  match l with
  | ObservationalObstruction _ f => observational_failure_refutes c f (ct_observational ct)
  | ConstructionObstruction _ f => construction_failure_refutes c f (ct_construction ct)
  | MaintenanceObstruction _ f => ecMaintenanceRefutes c f (ct_maintenance ct)
  | InstitutionalObstruction _ f => ecAuthorisationRefutes c f (ct_authority ct)
  end.

(** Refutation soundness: no certified transport coexists with an obstruction,
    and this holds of EVERY member of the collection. *)
Theorem obstructions_refute c (o : Obstructions c) (ct : CertifiedTransport c) : False.
Proof. exact (located_refutes c (fst o) ct). Qed.

Theorem each_obstruction_refutes c (o : Obstructions c) (l : Located c) :
  In l (fst o :: snd o) -> CertifiedTransport c -> False.
Proof. intros _ ct. exact (located_refutes c l ct). Qed.

(** ** Soundness against the legacy [Transportable] proposition

    The legacy predicate [Transportable] has ABSTRACT slots ([Exhibited],
    [LineageGrounded], [Functorial]); "the legacy predicate" is therefore a family.
    [TransportableLegacy c] is ONE instantiation: exhibition and maintenance
    erased to [inhabited], lineage to [LineagePasses].  [TransportableFull c]
    adds an inhabited authority, which the legacy predicate does not contain, so

        TransportableFull c  <->  TransportableLegacy c /\ inhabited (ecAuthorisation c)

    and [TransportableFull] is STRICTLY stronger.  Consequently refuting
    [TransportableFull] does NOT refute [TransportableLegacy]: an institutional
    failure refutes only the extra conjunct.  The precise statements are:

    - [certified_transportable_legacy] / [certified_transportable]: certified
      evidence yields both;
    - [located_refutes_legacy]: every NON-institutional located failure refutes
      [TransportableLegacy] (hence also [TransportableFull]);
    - [institutional_refutes_full]: an institutional failure refutes
      [TransportableFull] (and only the authority conjunct). *)

Definition TransportableLegacy (c : EvCandidate) : Prop :=
  Transportable (ecSpan c) (ecMA c) (ecPA c) (ecMB c) (ecPB c) (ecPs c)
    (inhabited (ExhibitionCertificate (ecSpan c) (ecPs c)))
    (LineagePasses (ecLineage c))
    (inhabited (ecMaintenance c)).

Definition TransportableFull (c : EvCandidate) : Prop :=
  TransportableLegacy c /\ inhabited (ecAuthorisation c).

Lemma full_iff_legacy_and_authority c :
  TransportableFull c <-> TransportableLegacy c /\ inhabited (ecAuthorisation c).
Proof. split; intro H; exact H. Qed.

Lemma full_implies_legacy c : TransportableFull c -> TransportableLegacy c.
Proof. intros [H _]. exact H. Qed.

Definition is_institutional {c} (l : Located c) : bool :=
  match l with InstitutionalObstruction _ _ => true | _ => false end.

Theorem certified_transportable_legacy c (ct : CertifiedTransport c) :
  TransportableLegacy c.
Proof.
  apply certified_gives_transportable.
  exact (((ct_observational ct, ct_construction ct), ct_maintenance ct), ct_authority ct).
Qed.

Theorem certified_transportable c (ct : CertifiedTransport c) : TransportableFull c.
Proof.
  split; [exact (certified_transportable_legacy c ct) | exact (inhabits (ct_authority ct))].
Qed.

(** Every NON-institutional located failure refutes the legacy instantiation. *)
Theorem located_refutes_legacy c (l : Located c) :
  is_institutional l = false -> ~ TransportableLegacy c.
Proof.
  intros Hnot (hs & hex & hlin & hA & hB & hG & hm).
  destruct hlin as (wf & l1 & l2 & l3).
  destruct l1 as (Hga & Hgb & Hda & Hdb).
  destruct l as [[w|w] | f | f | f]; cbn in Hnot; try discriminate Hnot.
  - exact (fibre_witness_refutes _ _ w hA).
  - exact (fibre_witness_refutes _ _ w hB).
  - destruct f as [e|r H|e|[H|H]|[H|H]|n H1 H2 H3 H4|H|H].
    + destruct hs as [s]. exact (e s).
    + destruct (hG r) as [ga gb]. destruct H as [H|H]; [exact (H ga) | exact (H gb)].
    + destruct hex as [ex]. exact (e ex).
    + exact (Hga H).
    + exact (Hgb H).
    + exact (Hda H).
    + exact (Hdb H).
    + exact (H4 (l2 n H1 H2 H3)).
    + exact (H l3).
    + exact (H wf).
  - destruct hm as [m]. exact (ecMaintenanceRefutes c f m).
Qed.

(** An institutional failure refutes only the extra authority conjunct. *)
Theorem institutional_refutes_full c (f : ecAuthorisationFailure c) :
  ~ TransportableFull c.
Proof.
  intros [_ [a]]. exact (ecAuthorisationRefutes c f a).
Qed.

Theorem located_refutes_transportable c (l : Located c) : ~ TransportableFull c.
Proof.
  destruct (is_institutional l) eqn:E.
  - destruct l as [o|f|f|f]; cbn in E; try discriminate E. exact (institutional_refutes_full c f).
  - intros [H _]. exact (located_refutes_legacy c l E H).
Qed.

Corollary refuted_not_transportable c (o : Obstructions c) : ~ TransportableFull c.
Proof. exact (located_refutes_transportable c (fst o)). Qed.

(** ** Open obligations *)

Inductive DebtKind : Type :=
| ObservationalDebt | ConstructionDebt | MaintenanceDebt | InstitutionalDebt.

Record OpenObligation : Type := { oo_kind : DebtKind; oo_reason : OpenReason }.

(** ** The assessment *)

Inductive TransportAssessment (c : EvCandidate) : Type :=
| Certified : CertifiedTransport c -> TransportAssessment c
| Refuted : Obstructions c -> TransportAssessment c
| Open : list OpenObligation -> TransportAssessment c.

Arguments Certified {c} _.
Arguments Refuted {c} _.
Arguments Open {c} _.

Definition tag {c} (a : TransportAssessment c) : WarrantStatus :=
  match a with
  | Certified _ => TransportCertified
  | Refuted _ => TransportRefuted
  | Open _ => TransportUnderdetermined
  end.

(** ** Per-obligation verdicts and their assembly *)

Inductive Verdict (Ev Fail : Type) : Type :=
| VDischarged : Ev -> Verdict Ev Fail
| VFailed : Fail -> Verdict Ev Fail
| VOpen : OpenReason -> Verdict Ev Fail.
Arguments VDischarged {Ev Fail} _.
Arguments VFailed {Ev Fail} _.
Arguments VOpen {Ev Fail} _.

Section Assemble.
  Context (c : EvCandidate).

  Definition ObsEv : Type := Admissible (ecMA c) (ecPA c) /\ Admissible (ecMB c) (ecPB c).

  Definition failures (vo : Verdict ObsEv (ObservationalFailure c))
      (vc : Verdict (ConstructionCertificate c) (ConstructionFailure c))
      (vm : Verdict (ecMaintenance c) (ecMaintenanceFailure c))
      (vi : Verdict (ecAuthorisation c) (ecAuthorisationFailure c))
    : list (Located c) :=
    (match vo with VFailed f => [ObservationalObstruction c f] | _ => [] end) ++
    (match vc with VFailed f => [ConstructionObstruction c f] | _ => [] end) ++
    (match vm with VFailed f => [MaintenanceObstruction c f] | _ => [] end) ++
    (match vi with VFailed f => [InstitutionalObstruction c f] | _ => [] end).

  Definition opens (vo : Verdict ObsEv (ObservationalFailure c))
      (vc : Verdict (ConstructionCertificate c) (ConstructionFailure c))
      (vm : Verdict (ecMaintenance c) (ecMaintenanceFailure c))
      (vi : Verdict (ecAuthorisation c) (ecAuthorisationFailure c))
    : list OpenObligation :=
    (match vo with VOpen r => [{| oo_kind := ObservationalDebt; oo_reason := r |}] | _ => [] end) ++
    (match vc with VOpen r => [{| oo_kind := ConstructionDebt; oo_reason := r |}] | _ => [] end) ++
    (match vm with VOpen r => [{| oo_kind := MaintenanceDebt; oo_reason := r |}] | _ => [] end) ++
    (match vi with VOpen r => [{| oo_kind := InstitutionalDebt; oo_reason := r |}] | _ => [] end).

  Definition assemble (vo : Verdict ObsEv (ObservationalFailure c))
      (vc : Verdict (ConstructionCertificate c) (ConstructionFailure c))
      (vm : Verdict (ecMaintenance c) (ecMaintenanceFailure c))
      (vi : Verdict (ecAuthorisation c) (ecAuthorisationFailure c))
    : TransportAssessment c :=
    match failures vo vc vm vi with
    | h :: t => Refuted (h, t)
    | [] =>
        match vo, vc, vm, vi with
        | VDischarged o, VDischarged k, VDischarged m, VDischarged i =>
            Certified {| ct_observational := o; ct_construction := k;
                         ct_maintenance := m; ct_authority := i |}
        | _, _, _, _ => Open (opens vo vc vm vi)
        end
    end.

  Definition any_failed vo vc vm vi : bool :=
    match failures vo vc vm vi with [] => false | _ => true end.
  Definition any_opened vo vc vm vi : bool :=
    match opens vo vc vm vi with [] => false | _ => true end.

  (** The status of an assembled assessment: a located refutation anywhere
      refutes; otherwise any open obligation leaves it open; otherwise it is
      certified.  Exactly the manuscript's componentwise rule. *)
  Theorem assemble_status vo vc vm vi :
    tag (assemble vo vc vm vi) =
      if any_failed vo vc vm vi then TransportRefuted
      else if any_opened vo vc vm vi then TransportUnderdetermined
      else TransportCertified.
  Proof.
    destruct vo, vc, vm, vi; reflexivity.
  Qed.

  Theorem assemble_open_nonempty vo vc vm vi os :
    assemble vo vc vm vi = Open os -> os <> [].
  Proof.
    intro H. destruct vo, vc, vm, vi; cbn in H;
      try discriminate H; (injection H as <-; discriminate).
  Qed.

  (** A refuted assembly reports EVERY failed obligation, in a fixed order
      (observational, construction, maintenance, institutional). *)
  Theorem assemble_refuted_reports_all vo vc vm vi h t :
    assemble vo vc vm vi = Refuted (h, t) -> h :: t = failures vo vc vm vi.
  Proof.
    unfold assemble. destruct (failures vo vc vm vi) as [|h' t'] eqn:E.
    - destruct vo, vc, vm, vi; discriminate.
    - intro H. injection H as <- <-. reflexivity.
  Qed.
End Assemble.

(** ** Reports versus verdicts

    [assemble] returns the VERDICT.  On refutation it reports the located
    failures; it does NOT carry along unresolved obligations that co-occur with
    them.  The complete [AssessmentReport] retains every obligation in exactly one
    of three lists, whatever the verdict; the verdict is derived from it
    ([report_verdict], [report_verdict_agrees]). *)

Record AssessmentReport (c : EvCandidate) : Type := {
  rep_failures : list (Located c);
  rep_opens : list OpenObligation;
  rep_discharged : list DebtKind
}.
Arguments rep_failures {c} _.
Arguments rep_opens {c} _.
Arguments rep_discharged {c} _.

Section Report.
  Context (c : EvCandidate).

  Definition discharged_kinds (vo : Verdict (ObsEv c) (ObservationalFailure c))
      (vc : Verdict (ConstructionCertificate c) (ConstructionFailure c))
      (vm : Verdict (ecMaintenance c) (ecMaintenanceFailure c))
      (vi : Verdict (ecAuthorisation c) (ecAuthorisationFailure c))
    : list DebtKind :=
    (match vo with VDischarged _ => [ObservationalDebt] | _ => [] end) ++
    (match vc with VDischarged _ => [ConstructionDebt] | _ => [] end) ++
    (match vm with VDischarged _ => [MaintenanceDebt] | _ => [] end) ++
    (match vi with VDischarged _ => [InstitutionalDebt] | _ => [] end).

  Definition report_of vo vc vm vi : AssessmentReport c :=
    {| rep_failures := failures c vo vc vm vi;
       rep_opens := opens c vo vc vm vi;
       rep_discharged := discharged_kinds vo vc vm vi |}.

  Definition report_verdict (r : AssessmentReport c) : WarrantStatus :=
    match rep_failures r with
    | _ :: _ => TransportRefuted
    | [] => match rep_opens r with
            | _ :: _ => TransportUnderdetermined
            | [] => TransportCertified
            end
    end.

  (** The verdict of the report is the tag of the assembled assessment. *)
  Theorem report_verdict_agrees vo vc vm vi :
    report_verdict (report_of vo vc vm vi) = tag (assemble c vo vc vm vi).
  Proof. destruct vo, vc, vm, vi; reflexivity. Qed.

  (** Every obligation is accounted for, exactly once: nothing is dropped, even
      when another obligation already refutes transport. *)
  Theorem report_accounts_for_all vo vc vm vi :
    length (rep_failures (report_of vo vc vm vi)) +
    length (rep_opens (report_of vo vc vm vi)) +
    length (rep_discharged (report_of vo vc vm vi)) = 4.
  Proof. destruct vo, vc, vm, vi; reflexivity. Qed.
End Report.

(** ** Erasure forgets the distinctions *)

(** Ordinary rewriting sees only this: whether a transport witness exists. *)
Definition ErasedTransport (c : EvCandidate) (x y : rstate c) : Prop :=
  erased (rich_structure c) x y.

(** A certified assessment yields a grounded witness at every crossing, and so an
    erased transport. *)
Definition certified_witness_at c (ct : CertifiedTransport c) (r : seam (ecSpan c))
  : RPath c (inl (back (ecSpan c) r)) (inr (fwd (ecSpan c) r)) := rp_step r ct.

Corollary certified_assessment_erases c (ct : CertifiedTransport c) r :
  ErasedTransport c (inl (back (ecSpan c) r)) (inr (fwd (ecSpan c) r)).
Proof. exact (certified_crossing_erases c ct r). Qed.

(** The status is all that survives of an assessment in [WarrantStatus]; the
    evidence, obstructions and open obligations do not. *)
Definition forget_assessment {c} (a : TransportAssessment c) : WarrantStatus := tag a.
