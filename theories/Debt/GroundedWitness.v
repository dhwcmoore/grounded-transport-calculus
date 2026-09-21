(** * Grounded transport witnesses that CARRY their evidence.

    [CertifiedTransport c] is DATA: the observational, construction
    (inhabitant, exhibition record, lineage graph, grounding), maintenance and
    authority evidence for the candidate [c].  [RPath c x y] is the type of
    grounded transport witnesses between states: a path of grounded crossings,
    each crossing carrying a full [CertifiedTransport].  It is the [GT] of a
    generic [GTransport] ([rich_structure]).

    Erasure forgets in two stages, and both are lossy:

        RPath  --forget-->  OPath (grounded crossings, no certificates)
               --erase-->   [oval x = oval y]   (ordinary substitutability)

    Distinguishability is exhibited by [witness_summary], a projection to
    extractable data (record id, custodian, lineage ground node, coverage). *)

From Coq Require Import List.
Import ListNotations.
From GTC.Core Require Import GroundedTransport Erasure.
From GTC.Debt Require Import Certificates EvidenceObligations.
From GTC.Instances Require Import OriginalGroundedSeamInstance.
From Exactness Require Import GroundedSeam.

Record CertifiedTransport (c : EvCandidate) : Type := {
  ct_observational :
    Admissible (ecMA c) (ecPA c) /\ Admissible (ecMB c) (ecPB c);
  ct_construction : ConstructionCertificate c;
  ct_maintenance : ecMaintenance c;
  ct_authority : ecAuthorisation c
}.
Arguments ct_observational {c} _.
Arguments ct_construction {c} _.
Arguments ct_maintenance {c} _.
Arguments ct_authority {c} _.

Section Rich.
  Context (c : EvCandidate).

  Definition rstate : Type := @ost (ecA c) (ecB c).
  Definition rval : rstate -> bool := oval (ecPA c) (ecPB c).

  Inductive RPath : rstate -> rstate -> Type :=
  | rp_refl  : forall x, RPath x x
  | rp_step  : forall (r : seam (ecSpan c)) (ct : CertifiedTransport c),
      RPath (inl (back (ecSpan c) r)) (inr (fwd (ecSpan c) r))
  | rp_trans : forall x y z, RPath x y -> RPath y z -> RPath x z.

  (** Stage 1: forget the certificates, keep the grounded crossings. *)
  Fixpoint rpath_forget {x y} (w : RPath x y)
    : OPath (ecSpan c) (ecPA c) (ecPB c) (ecPs c) x y :=
    match w with
    | rp_refl x => op_refl _ _ _ _ x
    | rp_step r ct =>
        op_step _ _ _ _ r
          (proj1 (cc_grounding (ct_construction ct) r))
          (proj2 (cc_grounding (ct_construction ct) r))
    | rp_trans _ _ _ w1 w2 => op_trans _ _ _ _ _ _ _ (rpath_forget w1) (rpath_forget w2)
    end.

  (** Stage 2: ordinary substitutability. *)
  Lemma rpath_sound : forall x y, RPath x y -> rval x = rval y.
  Proof. intros x y w. exact (opath_sound _ _ _ _ x y (rpath_forget w)). Qed.

  Definition rich_structure : GTransport rstate (fun x y => rval x = rval y) :=
    {| GT := RPath; gt_refl := rp_refl; gt_compose := rp_trans;
       gt_sound := rpath_sound |}.

  (** ** The extractable summary of a witness *)

  Record WitnessSummary : Type := {
    ws_record : nat;              (* exhibition record id *)
    ws_custodian : nat;           (* custodian *)
    ws_ground : nat;              (* lineage ground node *)
    ws_coverage : nat * nat;      (* exhibition coverage interval *)
    ws_dispositions : nat;        (* number of declared lineage dispositions *)
    ws_maintenance : list EvidenceAtom;   (* via [EvidenceSummary] *)
    ws_authority : list EvidenceAtom      (* via [EvidenceSummary] *)
  }.

  Definition ct_summary (ct : CertifiedTransport c) : WitnessSummary :=
    let cc := ct_construction ct in
    {| ws_record := ex_record_id (cc_exhibition cc);
       ws_custodian := ex_custodian (cc_exhibition cc);
       ws_ground := lin_ground (lc_graph (cc_lineage cc));
       ws_coverage := ex_coverage (cc_exhibition cc);
       ws_dispositions := length (lin_dispositions (lc_graph (cc_lineage cc)));
       ws_maintenance :=
         @evidence_summary _ (ecMaintenanceSummary c) (ct_maintenance ct);
       ws_authority :=
         @evidence_summary _ (ecAuthorisationSummary c) (ct_authority ct) |}.

  Fixpoint witness_summary {x y} (w : RPath x y) : list WitnessSummary :=
    match w with
    | rp_refl _ => []
    | rp_step _ ct => [ct_summary ct]
    | rp_trans _ _ _ w1 w2 => witness_summary w1 ++ witness_summary w2
    end.
End Rich.

Arguments rp_refl {c} x.
Arguments rp_step {c} r ct.
Arguments rp_trans {c x y z} _ _.

(** 1. Grounded transport entails ordinary substitutability. *)
Theorem erase_sound (c : EvCandidate) (x y : rstate c) :
  RPath c x y -> rval c x = rval c y.
Proof. exact (rpath_sound c x y). Qed.

(** Every erased witness is extensional agreement, at every crossing. *)
Corollary certified_crossing_erases (c : EvCandidate) (ct : CertifiedTransport c)
    (r : seam (ecSpan c)) :
  erased (rich_structure c) (inl (back (ecSpan c) r)) (inr (fwd (ecSpan c) r)).
Proof. exact (erase (rich_structure c) (rp_step r ct)). Qed.

(** * Witness algebra: identity and associativity modulo crossing-sequence
    equivalence.

    [RPath] is a FREE structure: [rp_trans (rp_refl x) w] is not literally [w].
    The laws therefore hold modulo [WEquiv], which identifies two witnesses iff
    they have the same sequence of certified crossings.  It forgets bracketing
    and identity padding and NOTHING ELSE: every seam element and every
    certificate is compared.  The transport calculus is a category up to
    [WEquiv] (no quotient type is constructed); literal equality is not claimed. *)

Section Algebra.
  Context (c : EvCandidate).

  Definition crossing : Type := { r : seam (ecSpan c) & CertifiedTransport c }.

  Fixpoint crossings {x y} (w : RPath c x y) : list crossing :=
    match w with
    | rp_refl _ => []
    | rp_step r ct => [existT _ r ct]
    | rp_trans w1 w2 => crossings w1 ++ crossings w2
    end.

  Definition WEquiv {x y} (w1 w2 : RPath c x y) : Prop := crossings w1 = crossings w2.

  Lemma WEquiv_refl {x y} (w : RPath c x y) : WEquiv w w.
  Proof. reflexivity. Qed.
  Lemma WEquiv_sym {x y} (w1 w2 : RPath c x y) : WEquiv w1 w2 -> WEquiv w2 w1.
  Proof. intro H. symmetry. exact H. Qed.
  Lemma WEquiv_trans {x y} (w1 w2 w3 : RPath c x y) :
    WEquiv w1 w2 -> WEquiv w2 w3 -> WEquiv w1 w3.
  Proof. intros H1 H2. etransitivity; eassumption. Qed.

  (** Composition respects [WEquiv]. *)
  Lemma WEquiv_compose {x y z} (v v' : RPath c x y) (w w' : RPath c y z) :
    WEquiv v v' -> WEquiv w w' -> WEquiv (rp_trans v w) (rp_trans v' w').
  Proof. intros Hv Hw. unfold WEquiv in *. cbn. rewrite Hv, Hw. reflexivity. Qed.

  (** Identity and associativity. *)
  Theorem WEquiv_id_left {x y} (w : RPath c x y) : WEquiv (rp_trans (rp_refl x) w) w.
  Proof. reflexivity. Qed.

  Theorem WEquiv_id_right {x y} (w : RPath c x y) : WEquiv (rp_trans w (rp_refl y)) w.
  Proof. unfold WEquiv. cbn. apply app_nil_r. Qed.

  Theorem WEquiv_assoc {x y z u} (w1 : RPath c x y) (w2 : RPath c y z) (w3 : RPath c z u) :
    WEquiv (rp_trans (rp_trans w1 w2) w3) (rp_trans w1 (rp_trans w2 w3)).
  Proof. unfold WEquiv. cbn. symmetry. apply app_assoc. Qed.

  (** The extractable summary depends only on the crossing sequence, so
      equivalent witnesses have the same summary. *)
  Lemma summary_of_crossings {x y} (w : RPath c x y) :
    witness_summary c w = map (fun e => ct_summary c (projT2 e)) (crossings w).
  Proof.
    induction w as [x|r ct|x y z w1 IH1 w2 IH2]; cbn; [reflexivity | reflexivity |].
    rewrite map_app, IH1, IH2. reflexivity.
  Qed.

  Corollary WEquiv_summary {x y} (w1 w2 : RPath c x y) :
    WEquiv w1 w2 -> witness_summary c w1 = witness_summary c w2.
  Proof.
    intro H. rewrite !summary_of_crossings. unfold WEquiv in H. rewrite H. reflexivity.
  Qed.
End Algebra.
