(** * Different warrants, same endpoints.

    Two grounded transport witnesses between the SAME pair of states, differing
    in seam element, exhibition record, custodian, coverage interval and lineage
    dispositions.  After erasure they are one and the same judgement; as
    witnesses they remain distinguishable, through their extractable summaries.
    The authority and maintenance components also differ in general; the summary
    projects only the exhibition and lineage data. *)

From Coq Require Import List.
Import ListNotations.
From GTC.Core Require Import GroundedTransport Erasure.
From GTC.Debt Require Import Certificates EvidenceObligations GroundedWitness PackedWarrant.
From GTCExamples Require Import LineageCertificates.
From Exactness Require Import GroundedSeam.

(** The lineage record is part of the DECLARED problem, so witnesses that differ
    in lineage live in different candidates [two_ev d]; those that differ in
    seam element, exhibition record, custodian or coverage share one candidate.
    Both kinds are compared below through the same extractable summary. *)

(** A seam with two elements over the same coordinate states. *)
Definition two_span : Span unit unit :=
  {| seam := bool; back := fun _ => tt; fwd := fun _ => tt |}.

Definition two_ev (d : list (nat * Disposition)) : EvCandidate :=
  {| ecA := unit; ecB := unit; ecOA := unit; ecOB := unit; ecSpan := two_span;
     ecMA := fun _ => tt; ecPA := fun _ => true;
     ecMB := fun _ => tt; ecPB := fun _ => true;
     ecPs := fun _ => true;
     ecLineage := indep_lineage d;
     ecMaintenance := unit; ecMaintenanceFailure := Empty_set;
     ecMaintenanceRefutes := fun f _ => match f with end;
     ecMaintenanceSummary := unit_summary;
     ecAuthorisation := AuthorisationCertificate unit (fun _ => True);
     ecAuthorisationFailure := Empty_set;
     ecAuthorisationRefutes := fun f _ => match f with end;
     ecAuthorisationSummary := authorisation_summary unit (fun _ => True) |}.

Definition exhibit (rid custodian : nat) (cov : nat * nat)
  : ExhibitionCertificate two_span (fun _ => true).
Proof.
  refine (@Build_ExhibitionCertificate unit unit two_span (fun _ => true) rid
            (fun b : bool => if b then 1 else 0) _ 1 bool (fun _ => true)
            (fun b => b) (fun _ => eq_refl) cov custodian).
  intros r r' H. destruct r, r'; first [reflexivity | discriminate H].
Defined.

Lemma two_grounded : GroundingEquations two_span (fun _ => true) (fun _ => true)
                                        (fun _ => true).
Proof. intro r. split; reflexivity. Qed.

(** Two certified transports for the same candidate, on different records. *)
Lemma two_obs (d : list (nat * Disposition)) :
  Admissible (ecMA (two_ev d)) (ecPA (two_ev d)) /\
  Admissible (ecMB (two_ev d)) (ecPB (two_ev d)).
Proof. split; exists (fun _ => true); intro s; reflexivity. Qed.

Definition ct_for (disp : list (nat * Disposition)) (rid custodian aid : nat)
    (cov : nat * nat) : CertifiedTransport (two_ev disp) :=
  @Build_CertifiedTransport (two_ev disp) (two_obs disp)
    (@Build_ConstructionCertificate (two_ev disp) true (exhibit rid custodian cov)
       (indep_certificate disp) eq_refl two_grounded)
    tt {| auth_authority := aid; auth_rule := tt; auth_licensed := I |}.

(** ** The witnesses *)

Definition d0 : list (nat * Disposition) := [].
Definition d1 : list (nat * Disposition) := [(9, Justified 42)].

(** Same problem, different seam element, record, custodian, coverage. *)
Definition w1 : RPath (two_ev d0) (inl tt) (inr tt) :=
  @rp_step (two_ev d0) false (ct_for d0 1 7 11 (0, 1)).
Definition w2 : RPath (two_ev d0) (inl tt) (inr tt) :=
  @rp_step (two_ev d0) true (ct_for d0 2 8 12 (0, 5)).

(** Different declared lineage (a disclosed disposition). *)
Definition w3 : RPath (two_ev d1) (inl tt) (inr tt) :=
  @rp_step (two_ev d1) false (ct_for d1 1 7 11 (0, 1)).

(** 3. The endpoints coincide; erasure identifies the witnesses; the witnesses
    remain distinguishable. *)
Theorem same_endpoints_different_warrants :
  erased (rich_structure (two_ev d0)) (inl tt) (inr tt) /\
  witness_summary (two_ev d0) w1 <> witness_summary (two_ev d0) w2 /\
  w1 <> w2.
Proof.
  refine (conj (erase (rich_structure (two_ev d0)) w1) (conj _ _)).
  - vm_compute. intro H. congruence.
  - intro H. assert (E : witness_summary (two_ev d0) w1 = witness_summary (two_ev d0) w2)
      by (rewrite H; reflexivity).
    vm_compute in E. congruence.
Qed.

Theorem different_lineage_different_warrant :
  erased (rich_structure (two_ev d1)) (inl tt) (inr tt) /\
  witness_summary (two_ev d0) w1 <> witness_summary (two_ev d1) w3.
Proof.
  refine (conj (erase (rich_structure (two_ev d1)) w3) _).
  vm_compute. intro H. congruence.
Qed.

(** Both are the same ordinary judgement: an [rval] agreement. *)
Corollary both_erase_to_agreement :
  rval (two_ev d0) (inl tt) = rval (two_ev d0) (inr tt).
Proof. exact (erase_sound (two_ev d0) _ _ w1). Qed.

(** ** Packed: one endpoint-indexed collection

    Endpoints are the two sides ([false] source side, [true] target side).  The
    packing puts warrants from DIFFERENT problems (different declared lineage)
    into the single type [PackedWarrant emb false true]. *)

Definition emb (c : EvCandidate) (s : rstate c) : bool :=
  match s with inl _ => false | inr _ => true end.

Definition pw1 : PackedWarrant emb false true :=
  {| pw_problem := two_ev d0; pw_src := inl tt; pw_tgt := inr tt;
     pw_src_is := eq_refl; pw_tgt_is := eq_refl; pw_witness := w1 |}.

Definition pw3 : PackedWarrant emb false true :=
  {| pw_problem := two_ev d1; pw_src := inl tt; pw_tgt := inr tt;
     pw_src_is := eq_refl; pw_tgt_is := eq_refl; pw_witness := w3 |}.

Theorem packed_warrants_same_endpoints :
  exists w1' w2' : PackedWarrant emb false true,
    warrant_summary w1' <> warrant_summary w2' /\ w1' <> w2' /\
    ErasedAt emb false true.
Proof.
  exists pw1, pw3.
  assert (Hs : warrant_summary pw1 <> warrant_summary pw3).
  { unfold warrant_summary, pw1, pw3. cbn. vm_compute. intro H. congruence. }
  refine (conj Hs (conj (packed_distinguishable emb pw1 pw3 Hs) (erase_packed pw1))).
Qed.

(** The authorities differ too; this is visible only through the summary
    interface, since the authority type is abstract in the generic library. *)
Example authorities_differ_in_summary :
  map ws_authority (witness_summary (two_ev d0) w1)
  <> map ws_authority (witness_summary (two_ev d0) w2).
Proof. vm_compute. intro H. congruence. Qed.
