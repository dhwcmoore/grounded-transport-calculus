(** * Evidence-bearing certificates.

    Types that CARRY the exhibited record, the lineage graph and the
    authorising record, instead of abstract Props.  The legacy abstract Props
    [Exhibited] / [LineageGrounded] are recovered by erasure ([inhabited],
    [LineagePasses]).

        concrete certificate  ->  grounded transport witness  ->  erased relation

    SCOPE. LineageCheck.issue_certificate constructs a Coq record with
    proofs of the implemented WF and L1-L3 conditions and empty declared
    coverage gaps. Extraction erases these proofs and retains the record
    data. The handwritten legacy OCaml audit is not proved equivalent to
    the reflected checker; differential tests cover the stated overlap.
    Disposition resolution, actual coverage and the truth of administrative
    identifiers remain outside these implemented lineage guarantees.
    Identifiers (custodian, process, record) are opaque [nat]s: administrative
    facts that mathematics cannot infer. *)

From Coq Require Import List Arith Lia.
Import ListNotations.
From Exactness Require Import GroundedSeam.

(** ** Exhibition (manuscript Definition 12, conditions (i)-(v)) *)

Record ExhibitionCertificate {A B : Type} (S : Span A B)
    (Ps : seam S -> bool) : Type := {
  ex_record_id : nat;                                   (* the record rho_t *)
  ex_identifier : seam S -> nat;                        (* (i) identifiers  *)
  ex_identifier_stable :
    forall r r', ex_identifier r = ex_identifier r' -> r = r';
  ex_process : nat;                                     (* (ii) one declared process *)
  ex_retained : Type;                                   (* (iii) what the record retains *)
  ex_retain : seam S -> ex_retained;
  ex_evaluate : ex_retained -> bool;
  ex_evaluates : forall r, Ps r = ex_evaluate (ex_retain r);
  ex_coverage : nat * nat;                              (* (iv) declared interval *)
  ex_custodian : nat                                    (* (v) custodian *)
}.

Arguments ex_record_id {A B S Ps} _.
Arguments ex_identifier {A B S Ps} _ _.
Arguments ex_identifier_stable {A B S Ps} _ _ _ _.
Arguments ex_process {A B S Ps} _.
Arguments ex_retained {A B S Ps} _.
Arguments ex_retain {A B S Ps} _ _.
Arguments ex_evaluate {A B S Ps} _ _.
Arguments ex_evaluates {A B S Ps} _ _.
Arguments ex_coverage {A B S Ps} _.
Arguments ex_custodian {A B S Ps} _.

(** Condition (iii) is itself a factorisation obligation: the seam valuation is
    a function of what the record retains. *)
Lemma exhibition_valuation_admissible {A B} {S : Span A B} {Ps : seam S -> bool}
    (c : ExhibitionCertificate S Ps) : Admissible (ex_retain c) Ps.
Proof. exists (ex_evaluate c). exact (ex_evaluates c). Qed.

(** ** Lineage record and audit specification (Definition 13)

    The record is FINITE DATA (lists of nats and dispositions), mirroring the
    OCaml [lineage] record, so that it survives extraction.  The audit
    conditions are Props over that data; the certificate carries the data, a
    coverage record and the issued verdict as data, and the proofs beside them. *)

(** A disposition of a shared non-raw ancestor.  The [nat] references the
    justification text held in the assurance record (kept outside the kernel). *)
Inductive Disposition : Type :=
| Justified (note : nat)
| OpenDefeater (note : nat).

Record Lineage : Type := {
  lin_derived : list (nat * list nat);        (* derived field, its parents *)
  lin_raw : list nat;                         (* raw inputs *)
  lin_relevant : list nat;                    (* claim-relevant raw inputs *)
  lin_dA : nat;  lin_dB : nat;  lin_ground : nat;
  lin_dispositions : list (nat * Disposition)
}.

Definition lin_nodes (g : Lineage) : list nat := map fst (lin_derived g) ++ lin_raw g.

Definition lin_parents (g : Lineage) (n : nat) : list nat :=
  match find (fun e => Nat.eqb (fst e) n) (lin_derived g) with
  | Some e => snd e
  | None => []
  end.

Definition lin_is_raw (g : Lineage) (n : nat) : Prop := In n (lin_raw g).
Definition lin_is_relevant (g : Lineage) (n : nat) : Prop := In n (lin_relevant g).
Definition lin_disposed (g : Lineage) (n : nat) : Prop :=
  exists d, In (n, d) (lin_dispositions g).

(** [Ancestor g n m]: [m] is a strict ancestor of [n]. *)
Inductive Ancestor (g : Lineage) : nat -> nat -> Prop :=
| anc_parent : forall n m, In m (lin_parents g n) -> Ancestor g n m
| anc_step : forall n p m,
    In p (lin_parents g n) -> Ancestor g p m -> Ancestor g n m.

Lemma anc_inv (g : Lineage) n m :
  Ancestor g n m ->
  In m (lin_parents g n) \/ exists p, In p (lin_parents g n) /\ Ancestor g p m.
Proof.
  intro H. destruct H as [n m H | n p m H1 H2].
  - left. exact H.
  - right. exists p. split; assumption.
Qed.

Lemma anc_leaf (g : Lineage) n m : lin_parents g n = [] -> ~ Ancestor g n m.
Proof.
  intros E H. apply anc_inv in H. rewrite E in H.
  destruct H as [[]|(p & [] & _)].
Qed.

(** Acyclicity via a rank function: parents have strictly smaller rank. *)
Lemma ancestor_rank (g : Lineage) (rank : nat -> nat) :
  (forall n p, In p (lin_parents g n) -> rank p < rank n) ->
  forall n m, Ancestor g n m -> rank m < rank n.
Proof.
  intros Hr n m H. induction H as [n m H | n p m H1 H2 IH].
  - exact (Hr n m H).
  - pose proof (Hr n p H1). lia.
Qed.

Definition LineageWellFormed (g : Lineage) : Prop :=
  NoDup (lin_nodes g) /\
  (forall n ps, In (n, ps) (lin_derived g) -> forall p, In p ps -> In p (lin_nodes g)) /\
  In (lin_dA g) (map fst (lin_derived g)) /\
  In (lin_dB g) (map fst (lin_derived g)) /\
  In (lin_ground g) (lin_nodes g) /\
  (forall n, lin_is_relevant g n -> lin_is_raw g n) /\
  (forall n, ~ Ancestor g n n).

(** (L1) no descent and no coordinate-ground identity *)
Definition L1 (g : Lineage) : Prop :=
  lin_ground g <> lin_dA g /\
  lin_ground g <> lin_dB g /\
  ~ Ancestor g (lin_ground g) (lin_dA g) /\
  ~ Ancestor g (lin_ground g) (lin_dB g).

(** (L2) disclosure of shared non-raw ancestry *)
Definition L2 (g : Lineage) : Prop :=
  forall n, Ancestor g (lin_dA g) n -> Ancestor g (lin_dB g) n ->
            ~ lin_is_raw g n -> lin_disposed g n.

(** (L3) independent source *)
Definition L3 (g : Lineage) : Prop :=
  exists n,
    lin_is_raw g n /\
    lin_is_relevant g n /\
    (n = lin_ground g \/ Ancestor g (lin_ground g) n) /\
    ~ Ancestor g (lin_dA g) n /\
    ~ Ancestor g (lin_dB g) n /\
    n <> lin_dA g /\
    n <> lin_dB g.

Definition LineagePasses (g : Lineage) : Prop :=
  LineageWellFormed g /\ L1 g /\ L2 g /\ L3 g.

(** The interval and gaps a lineage record covers.  A partial record supports
    only a coverage-qualified result ("pass relative to L"): unrecorded
    claim-relevant segments remain open construction obligations. *)
Record CoverageRecord : Type := {
  cov_from : nat;  cov_to : nat;
  cov_gaps : list nat            (* unrecorded segments, by identifier *)
}.

Inductive LineageVerdict : Type := LineagePass | LineageFail.

(** The certificate carries the graph, coverage and issued verdict as DATA, and
    the proofs that the graph passes.  The proof fields vanish on extraction;
    the data fields remain. *)
Record LineageCertificate : Type := {
  lc_graph : Lineage;
  lc_coverage : CoverageRecord;
  lc_audit : LineageVerdict;
  lc_audit_passed : lc_audit = LineagePass;
  lc_no_gaps : cov_gaps lc_coverage = [];
  lc_wf : LineageWellFormed lc_graph;
  lc_L1 : L1 lc_graph;
  lc_L2 : L2 lc_graph;
  lc_L3 : L3 lc_graph
}.

Lemma lineage_certificate_passes (c : LineageCertificate) :
  LineagePasses (lc_graph c).
Proof. exact (conj (lc_wf c) (conj (lc_L1 c) (conj (lc_L2 c) (lc_L3 c)))). Qed.

(** ** Evidence summaries

    The generic calculus imposes no institutional record format: maintenance and
    authority evidence stay abstract types.  What it asks for is a SUMMARY
    interface, so that an extracted consumer can inspect them.  Applications
    supply instances (authority records, maintenance events, expiry,
    custodians, revalidation decisions); an atom is a small piece of
    extractable data, not a proof. *)

Inductive EvidenceAtom : Type :=
| AtomRecord (id : nat)
| AtomCustodian (id : nat)
| AtomGround (node : nat)
| AtomInterval (from to : nat)
| AtomAuthority (id : nat)
| AtomMaintenance (kind from to : nat)
| AtomExpiry (t : nat)
| AtomRevalidation (id : nat)
| AtomNote (tag payload : nat).

Class EvidenceSummary (A : Type) : Type :=
  { evidence_summary : A -> list EvidenceAtom }.

Instance unit_summary : EvidenceSummary unit := { evidence_summary := fun _ => [] }.

(** ** Authorisation *)

(** An authorising record: the authority, the declared rule, and evidence that
    the rule licenses the transformation.  The rule system is an INPUT. *)
Record AuthorisationCertificate (Rule : Type) (Licenses : Rule -> Prop) : Type := {
  auth_authority : nat;
  auth_rule : Rule;
  auth_licensed : Licenses auth_rule
}.

Instance authorisation_summary (Rule : Type) (Licenses : Rule -> Prop)
  : EvidenceSummary (AuthorisationCertificate Rule Licenses) :=
  { evidence_summary := fun a => [AtomAuthority (auth_authority _ _ a)] }.
