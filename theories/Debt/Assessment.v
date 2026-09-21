(** * Abstract three-way assessment (skeleton).

    This file is the ABSTRACT layer: a refutation here is a bare function
    [P -> False].  The located, evidence-bearing judgement is
    [TransportAssessment.v], whose failures are data.  This layer is kept for the
    decidable special case and the status theorems.

    Evidence-sensitive assessment of transport.

    Each obligation is assessed as discharged (positive certificate), refuted
    (negative witness) or open (no verdict).  The aggregate status follows the
    manuscript's componentwise rule: affirmation needs every conjunct
    warranted; denial needs at least one warranted failure; otherwise the
    claim is warrant-underdetermined.

    The manuscript's fourth status, warrant conflict, cannot arise here: one
    assessment of one obligation is exactly one of the three cases.

    The Boolean/decidable classifier ([DebtClassifier.v]) is recovered as the
    special case where every assessment is discharged or refuted. *)

From Coq Require Import Bool Setoid.
From GTC.Debt Require Import WarrantDebt DebtClassifier.

Inductive OpenReason : Type :=
| NotYetAssessed
| EvidenceWithheld
| IncompleteSearch        (* e.g. NoWitnessFound on a sample *)
| NoIssuanceRecord        (* history absent; causal classification open *)
| UndeclaredPolicy
| MissingLineageRecord     (* no lineage record supplied: open, NOT refuted *)
| CoverageGap (gaps : list nat)   (* partial record: coverage-qualified only *)
| OtherReason (code : nat).

Inductive Assessment (P : Type) : Type :=
| Discharged : P -> Assessment P
| Disproved : (P -> False) -> Assessment P
| Unresolved : OpenReason -> Assessment P.

Arguments Discharged {P} _.
Arguments Disproved {P} _.
Arguments Unresolved {P} _.

Definition is_dis {P} (x : Assessment P) : bool :=
  match x with Discharged _ => true | _ => false end.
Definition is_ref {P} (x : Assessment P) : bool :=
  match x with Disproved _ => true | _ => false end.
Definition is_open {P} (x : Assessment P) : bool :=
  match x with Unresolved _ => true | _ => false end.

Lemma is_ref_neg {P} (x : Assessment P) : is_ref x = true -> P -> False.
Proof. destruct x as [p|n|r]; cbn; [discriminate | intros _; exact n | discriminate]. Qed.

Lemma is_dis_evidence {P} (x : Assessment P) : is_dis x = true -> P.
Proof. destruct x as [p|n|r]; cbn; [intros _; exact p | discriminate | discriminate]. Qed.

(** Evidence-typed obligations: fields are [Type], so they may carry
    certificates.  Props are accepted as degenerate evidence. *)
Record EvObligations (Pb : Type) : Type := {
  EObs   : Pb -> Type;
  ECons  : Pb -> Type;
  EMaint : Pb -> Type;
  EInst  : Pb -> Type
}.
Arguments EObs {Pb} _ _.
Arguments ECons {Pb} _ _.
Arguments EMaint {Pb} _ _.
Arguments EInst {Pb} _ _.

Definition EvTransport {Pb} (O : EvObligations Pb) (p : Pb) : Type :=
  (EObs O p * ECons O p * EMaint O p * EInst O p)%type.

Record TransportAssessment {Pb} (O : EvObligations Pb) (p : Pb) : Type := {
  observational_assessment : Assessment (EObs O p);
  construction_assessment  : Assessment (ECons O p);
  maintenance_assessment   : Assessment (EMaint O p);
  institutional_assessment : Assessment (EInst O p)
}.
Arguments observational_assessment {Pb O p} _.
Arguments construction_assessment  {Pb O p} _.
Arguments maintenance_assessment   {Pb O p} _.
Arguments institutional_assessment {Pb O p} _.

Inductive WarrantStatus : Type :=
| TransportCertified
| TransportRefuted
| TransportUnderdetermined.

Section Status.
  Context {Pb} {O : EvObligations Pb} {p : Pb} (a : TransportAssessment O p).

  Definition any_refuted : bool :=
    is_ref (observational_assessment a) || is_ref (construction_assessment a) ||
    is_ref (maintenance_assessment a) || is_ref (institutional_assessment a).

  Definition any_open : bool :=
    is_open (observational_assessment a) || is_open (construction_assessment a) ||
    is_open (maintenance_assessment a) || is_open (institutional_assessment a).

  Definition warrant_status : WarrantStatus :=
    if any_refuted then TransportRefuted
    else if any_open then TransportUnderdetermined
    else TransportCertified.

  Definition no_obligation_refuted : Prop := any_refuted = false.
  Definition some_obligation_open : Prop := any_open = true.

  (** Certification soundness: a certified status yields the evidence. *)
  Theorem certified_sound :
    warrant_status = TransportCertified -> EvTransport O p.
  Proof.
    unfold warrant_status, any_refuted, any_open.
    destruct (observational_assessment a) as [o|no|ro];
    destruct (construction_assessment a) as [c|nc|rc];
    destruct (maintenance_assessment a) as [m|nm|rm];
    destruct (institutional_assessment a) as [i|ni|ri];
    cbn; intro H; try discriminate; exact (o, c, m, i).
  Qed.

  (** Refutation soundness: a refuted status refutes transport. *)
  Theorem refuted_sound :
    warrant_status = TransportRefuted -> EvTransport O p -> False.
  Proof.
    intros H ((( o & c) & m) & i). unfold warrant_status in H.
    destruct (any_refuted) eqn:E.
    - unfold any_refuted in E.
      apply orb_true_iff in E as [E|E]; [apply orb_true_iff in E as [E|E]; [apply orb_true_iff in E as [E|E]|]|].
      + exact (is_ref_neg _ E o).
      + exact (is_ref_neg _ E c).
      + exact (is_ref_neg _ E m).
      + exact (is_ref_neg _ E i).
    - destruct any_open; discriminate.
  Qed.

  Theorem refuted_iff : warrant_status = TransportRefuted <-> any_refuted = true.
  Proof.
    unfold warrant_status. destruct any_refuted; split; intro H;
      try reflexivity; try discriminate; try exact H;
      destruct any_open; discriminate.
  Qed.

  (** Underdetermination characterisation. *)
  Theorem underdetermined_iff :
    warrant_status = TransportUnderdetermined <->
    no_obligation_refuted /\ some_obligation_open.
  Proof.
    unfold warrant_status, no_obligation_refuted, some_obligation_open.
    destruct any_refuted, any_open; split; intro H;
      try discriminate; try (destruct H; discriminate); try (split; reflexivity);
      try reflexivity.
  Qed.

  Theorem certified_iff :
    warrant_status = TransportCertified <-> any_refuted = false /\ any_open = false.
  Proof.
    unfold warrant_status.
    destruct any_refuted, any_open; split; intro H;
      try discriminate; try (destruct H; discriminate); try (split; reflexivity);
      try reflexivity.
  Qed.
End Status.

(** The manuscript's Proposition (constructive transport underdetermination):
    if exactly the observational obligation is open and the rest are
    discharged, transport is underdetermined. *)
Corollary only_open_observational_underdetermined {Pb} {O : EvObligations Pb} {p}
    (a : TransportAssessment O p) r :
  observational_assessment a = Unresolved r ->
  is_dis (construction_assessment a) = true ->
  is_dis (maintenance_assessment a) = true ->
  is_dis (institutional_assessment a) = true ->
  warrant_status a = TransportUnderdetermined.
Proof.
  intros Ho Hc Hm Hi. apply underdetermined_iff. unfold no_obligation_refuted,
    some_obligation_open, any_refuted, any_open. rewrite Ho.
  destruct (construction_assessment a), (maintenance_assessment a),
           (institutional_assessment a); cbn in *; try discriminate; split; reflexivity.
Qed.

(** ** Decidable special case *)

Definition assess_dec {P : Type} (d : P + (P -> False)) : Assessment P :=
  match d with inl p => Discharged p | inr n => Disproved n end.

Lemma assess_dec_not_open {P} (d : P + (P -> False)) : is_open (assess_dec d) = false.
Proof. destruct d; reflexivity. Qed.

Definition dec_to_sum {P : Prop} (d : {P} + {~ P}) : P + (P -> False) :=
  match d with left p => inl p | right n => inr n end.

Section Decided.
  Context {Pb} (O : EvObligations Pb).
  Hypothesis dObs   : forall p, EObs O p + (EObs O p -> False).
  Hypothesis dCons  : forall p, ECons O p + (ECons O p -> False).
  Hypothesis dMaint : forall p, EMaint O p + (EMaint O p -> False).
  Hypothesis dInst  : forall p, EInst O p + (EInst O p -> False).

  Definition decide_all (p : Pb) : TransportAssessment O p :=
    {| observational_assessment := assess_dec (dObs p);
       construction_assessment  := assess_dec (dCons p);
       maintenance_assessment   := assess_dec (dMaint p);
       institutional_assessment := assess_dec (dInst p) |}.

  (** Decidable completeness: with every obligation decided, the status is
      never underdetermined. *)
  Theorem decidable_not_underdetermined (p : Pb) :
    warrant_status (decide_all p) <> TransportUnderdetermined.
  Proof.
    intro H. apply underdetermined_iff in H as [_ Ho].
    unfold some_obligation_open, any_open, decide_all in Ho. cbn in Ho.
    rewrite !assess_dec_not_open in Ho. discriminate.
  Qed.
End Decided.

(** The Boolean classifier as a corollary.  Prop-valued obligations are
    evidence-typed obligations whose evidence is a proof. *)
Definition ev_of_prop {Pb} (O : Obligations Pb) : EvObligations Pb :=
  {| EObs := fun p => Obs O p; ECons := fun p => Cons O p;
     EMaint := fun p => Maint O p; EInst := fun p => Inst O p |}.

Section BooleanCorollary.
  Context {Pb} (O : Obligations Pb).
  Hypothesis dec_obs   : forall p, {Obs O p}   + {~ Obs O p}.
  Hypothesis dec_cons  : forall p, {Cons O p}  + {~ Cons O p}.
  Hypothesis dec_maint : forall p, {Maint O p} + {~ Maint O p}.
  Hypothesis dec_inst  : forall p, {Inst O p}  + {~ Inst O p}.

  Let dec := decide_all (ev_of_prop O)
    (fun p => dec_to_sum (dec_obs p)) (fun p => dec_to_sum (dec_cons p))
    (fun p => dec_to_sum (dec_maint p)) (fun p => dec_to_sum (dec_inst p)).

  Theorem decided_certified_iff_transport (p : Pb) :
    warrant_status (dec p) = TransportCertified <-> Transport O p.
  Proof.
    split.
    - intro H. destruct (certified_sound (dec p) H) as ((( o & c) & m) & i).
      exact (conj (o : Obs O p) (conj (c : Cons O p) (conj (m : Maint O p) (i : Inst O p)))).
    - intros (o & c & m & i). unfold warrant_status, any_refuted, any_open, dec, decide_all.
      cbn. destruct (dec_obs p) as [?|n]; [|exfalso; exact (n o)].
      destruct (dec_cons p) as [?|n]; [|exfalso; exact (n c)].
      destruct (dec_maint p) as [?|n]; [|exfalso; exact (n m)].
      destruct (dec_inst p) as [?|n]; [|exfalso; exact (n i)].
      reflexivity.
  Qed.

  Theorem decided_refuted_iff_not_transport (p : Pb) :
    warrant_status (dec p) = TransportRefuted <-> ~ Transport O p.
  Proof.
    split.
    - intros H (o & c & m & i). exact (refuted_sound (dec p) H (o, c, m, i)).
    - intro Hn. pose proof (decidable_not_underdetermined (ev_of_prop O)
                (fun p => dec_to_sum (dec_obs p)) (fun p => dec_to_sum (dec_cons p))
                (fun p => dec_to_sum (dec_maint p)) (fun p => dec_to_sum (dec_inst p)) p) as Hu.
      pose proof (decided_certified_iff_transport p) as Hc.
      fold dec in Hu. destruct (warrant_status (dec p)) eqn:E.
      + exfalso. apply Hn. apply Hc. reflexivity.
      + reflexivity.
      + exfalso. exact (Hu eq_refl).
  Qed.

  (** Agreement with the earlier Boolean classifier. *)
  Corollary decided_certified_iff_clean (p : Pb) :
    warrant_status (dec p) = TransportCertified <->
    Clean (classify O dec_obs dec_cons dec_maint dec_inst p).
  Proof.
    rewrite decided_certified_iff_transport.
    symmetry. apply clean_iff_transport.
  Qed.
End BooleanCorollary.
