# Status (2026-09-21, after the checked-lineage-audit milestone)

Reference environment: Coq 8.18.0, OCaml 4.14.1. Builds under `coq_makefile` and
`dune build --root .`. `coqchk` passes on the whole project; on the project
without `ClassicalFactorisation.v` it succeeds and reports no axioms. `Print
Assumptions` is "closed under the global context" for every theorem listed
below except `constant_factors`.

## Review response (2026-09-22)

Formal changes (all axiom-free; 120 cited Coq identifiers re-verified):
- **Two-level contexts** (`Debt/CertificateProper.v`): `CrossingProper` (with an
  action on crossed seam elements, needed because Coq lacks definitional proof
  irrelevance), `CertificateProper` (commutes with the first erasure up to that
  action), composition and identity at both levels, the chain
  certificate-proper => crossing-proper => Proper, `evolution_crossing_proper`,
  `ProblemMorphism` with an evidence lift and `pm_certificate_proper`.
  `examples/CertificateReissue.v`: reissue instance, and
  `no_evidence_lift_when_grounding_lost`.
- **`TransportableLegacy` / `TransportableFull` split**
  (`Debt/TransportAssessment.v`): Full = Legacy + inhabited authority, strictly
  stronger. `located_refutes_legacy` (non-institutional failures),
  `institutional_refutes_full`, `certified_transportable_legacy`.
- **Deep-ancestry populations** (6 x 300) in `extraction/lineage_regression.ml`;
  `mutation_matrix.py` now reports per suite (fixed / random / shallow / deep) and
  has 13 mutants. Union 13/13; stratified alone 13/13; shallow 11/13; deep 8/13;
  random 12/13; fixed 5/13. The shallow populations missed the bounded-saturation
  mutants; the deep ones kill them.

Manuscript (`document/`, LMCS class, 36 pages, arXiv source package tested):
author block, non-anonymous citation of the earlier manuscript, related work rewritten
against five technical neighbours (Sozeau; Benton-Hofmann-Nigam; Hofmann-Streicher;
Green-Karvounarakis-Tannen; W3C PROV) plus PCC / verified compilation / translation
validation, all references verified at primary sources, page-by-page visual review.

Open before submission: confirm e-mail; decide whether the earlier manuscript has a
public preprint (else remove the citation); arXiv/CoRR preprint with cs.LO; archive
the artefact with a DOI; a general (non-reissue) theory of maintaining certificates
across evolutions remains future work.

## LMCS draft 2 (2026-09-22)

`document/`: the paper restructured for Logical Methods in Computer Science
(official `lmcs.cls`, alphaurl, 31 pages), standalone for readers who know
setoid rewriting / type theory / proof assistants. See `document/README.md`.

Results added while writing it:
- **`TransportableFull` soundness** (`Debt/TransportAssessment.v`):
  `certified_transportable` and `located_refutes_transportable` /
  `refuted_not_transportable`. Refutation soundness is now stated against the
  legacy `Transportable` proposition (instantiated, with an inhabited authority),
  not only against the evidence type. Every located failure refutes it.
- **Stratified regression** (`extraction/lineage_regression.ml`): eleven
  populations of 300 graphs, each with an INTENDED verdict (accepted; open by
  coverage gap; descent from d_A / d_B; undisclosed shared ancestor; no
  independent source; and five malformations). 3300/3300 agree with both the
  intent and the handwritten audit's flags.
- **Mutation study** (`extraction/mutation_matrix.py`): twelve textual mutants
  of the EXTRACTED checker; all 12 detected. No single population detects all
  (M6, coverage gaps ignored, is caught only by the open population; M1 is missed
  by the fixed case study). Limitation found: M12 (one saturation step) is missed
  by the stratified populations because their graphs are shallow.

Points where the paper differs from the drafting brief, deliberately:
- `erase(w1)=erase(w2)` is stated as "both erase into one proposition
  `ErasedAt` while summaries differ": equality of the two proofs needs proof
  irrelevance and says nothing.
- Contexts (`GroundedProper`) are instantiated at the CROSSING level (stage-1
  erased), not on full certified witnesses; the paper says so (Remark on what the
  instances act on) and lists it as a limitation.
- The witness laws hold modulo `WEquiv`; the paper claims a category only up to
  that equivalence.
- The brief's outline has no separate obstruction section; the observational
  obstruction is Proposition 5.7 (in section 5) and located obstructions are in
  section 8.

## Paper-driven corrections (2026-09-21)

Checking the outline's pre-publication list against the code found two real
gaps, both now fixed and machine-checked (axiom-free):

1. **Witness algebra.** `RPath` is a free inductive, so identity and
   associativity do NOT hold by equality. They are now proved modulo
   `WEquiv` (equal sequence of certified crossings): `WEquiv_id_left`,
   `WEquiv_id_right`, `WEquiv_assoc`, `WEquiv_compose`, `WEquiv_summary`
   (`Debt/GroundedWitness.v`). The calculus is a category up to `WEquiv`, no
   quotient type built; nothing stronger is claimed.
2. **Reports versus verdicts.** `assemble` returned `Refuted (h, t)`, dropping
   unresolved obligations that co-occur with a failure. Added
   `AssessmentReport` (`report_of`, `report_verdict`,
   `report_verdict_agrees`, `report_accounts_for_all`): every obligation is in
   exactly one of failed / open / discharged whatever the verdict. Example:
   `refuted_verdict_keeps_open_item`. `assemble` itself is unchanged.

The other three checks were already satisfied: the packed-warrant theorem
(`packed_warrants_same_endpoints`), separate preservation-on-image versus
coverage theorems, and lineage reflection (`lineage_check_reflect`, stronger than
the conditional form the outline anticipated).

## Paper draft
`document/`: LaTeX first draft (~23 pages), see `document/README.md`.

## Latest milestone: the audit gap, closed for the Coq specification

The principal formal gap was that `LineagePasses` (a Prop) and the OCaml audit
had no connection. Now:

| Result | Where |
|---|---|
| Ancestors computed by saturation; proved sound and complete (needs only that parents are declared; pigeonhole) | `ancestors_sound`, `ancestors_complete`, `ancestors_iff` in `Debt/LineageCheck.v` |
| Well-formedness, L1, L2, L3 each proved to reflect their specification | `wf_defect_none_iff`, `check_L1_reflect`, `undisclosed_none_iff`, `check_L3_reflect` |
| **Reflection, unconditional**: accepted iff the graph passes and there are no coverage gaps | `lineage_check_reflect` |
| Located rejection with proved evidence | `defect_sound`, `lineage_check_rejected` |
| `Open` is coverage-qualified only: graph passes, gaps remain | `lineage_check_open` |
| The extracted checker CONSTRUCTS kernel-checked certificates | `issue_certificate`, `issue_certificate_iff`, `issue_certificate_data` |
| A checker rejection becomes a located `ConstructionFailure` | `Debt/LineageAssessment.v` (`failure_of_rejection`) |

Axiom-free (`Print Assumptions`). The check is constructive and computes
(`examples/LineageChecked.v`: accepted, rejected with location, open, cycle,
undisclosed ancestor).

### Extraction and regression against the handwritten audit
`extraction/run_lineage_regression.sh` extracts the checker and compares it
with the handwritten `Jurisdiction.audit` from the legacy supplement:
- the five case-study records: 5/5 agree (L1/L2/L3 flags, grounded, and the
  malformed cycle);
- 3000 random records, including every malformation kind (duplicate,
  undeclared parent, distinguished-not-derived, relevant-not-raw, cycle): 3000/3000
  agree, comparing against the handwritten audit's actual printed output.

Two honest points about what this shows.
- It is a TEST of agreement on those inputs, not a theorem of equivalence with
  the handwritten OCaml. The theorem is Coq-checker <-> Coq-specification.
- The harness discriminates: a deliberate mutation (dropping the d_B descent
  test) is caught by the random test (and exits non-zero) but NOT by the five
  case-study records. The case study alone would not have detected that fault.
The random generator produces few grounded records (89 of 3000), so the accepting
path is exercised less than the rejecting paths.

Recommended use, as planned: the extracted checker replaces the handwritten
audit's DECISION core; the handwritten code remains as input construction,
diagnostic formatting, the case-study driver and an independent regression
comparison. Replacing it in `jurisdiction.ml` has NOT been done (the legacy
files are preserved unchanged).

### Packed warrants and summaries
- `PackedWarrant emb x y` (`Debt/PackedWarrant.v`) packages a problem with a
  witness and an embedding into a common endpoint type, so warrants from
  different problems live in one endpoint-indexed type. `packed_warrants_same_endpoints`
  (`examples/DifferentWarrants.v`): two packed warrants for the same endpoints,
  from problems with different declared lineage, with different summaries, not
  equal, and both erasing to the same `ErasedAt` judgement.
- `EvidenceSummary` (`Debt/Certificates.v`) is the generic reporting interface
  for abstract maintenance and authority evidence (`EvidenceAtom`). Witness
  summaries now include both; `authorities_differ_in_summary` shows authorities
  differ though erased judgements coincide. This is an observability extension,
  not a correctness one.

### Documentation to keep in the paper
> Relational reflexivity licenses formal self-substitution. It does not certify
> every concrete process whose endpoints happen to be equal.
(This is why assessments are indexed by the transport problem, not `(x, y)`.)

> Verdicts may be singular, but warrant failures are cumulative.
(`assemble_status` gives the verdict; `assemble_refuted_reports_all` retains
every located failure.)

## Frozen milestone
`milestones/semantic-kernel-1.{md,tar.gz,sha256}`: the kernel before this
milestone, restorable byte-for-byte. Later changes are additive and are listed
in `milestones/semantic-kernel-1.md`.

## The test: does grounded transport retain what ordinary rewriting forgets?

Six demonstrations. All are proved, axiom-free, and the evidence is in `Type`
(checked by extraction, below).

| # | Claim | Theorem | File |
|---|---|---|---|
| 1 | grounded transport entails ordinary substitutability | `erase_sound` (via `rpath_sound`) | `Debt/GroundedWitness.v` |
| 2 | ordinary substitutability does not reconstruct grounding | `erasure_not_reflecting`, `copied_ungrounded_agreement` | `examples/CopiedCoordinates.v` |
| 3 | different warrants, same endpoints, identical after erasure | `same_endpoints_different_warrants`, `different_lineage_different_warrant` | `examples/DifferentWarrants.v` |
| 4 | failed transport yields LOCATED evidence, co-occurring | `Located`, `Obstructions` (non-empty), `located_refutes`, `obstructions_refute`, `assemble_refuted_reports_all`, `both_obstructions_reported` | `Debt/TransportAssessment.v`, `examples/MaintenanceFailure.v` |
| 5 | missing evidence is not refutation | `TransportAssessment = Certified | Refuted | Open`; `assemble_status`; `missing_lineage_is_open`, `partial_lineage_is_open`, `three_outcomes_distinct` | same |
| 6 | dynamic failure visible despite extensional persistence | `dynamic_failure_visible`, `ordinary_rewriting_still_succeeds` | `examples/MaintenanceFailure.v` |

### The shape
```
Certified : CertifiedTransport c   -> TransportAssessment c
Refuted   : Obstructions c         -> TransportAssessment c   (head :: tail, non-empty)
Open      : list OpenObligation    -> TransportAssessment c
```
`assemble` builds it from four per-obligation `Verdict`s (`VDischarged | VFailed |
VOpen`). A refuted assembly reports EVERY failed obligation in a fixed order;
`assemble_open_nonempty` shows `Open` is never empty; `assemble_status` is the
manuscript's componentwise rule.

**Indexing deviation from the sketch.** Assessments are indexed by the transport
PROBLEM (`EvCandidate`), not by a pair `(x, y)`. A pair-indexed `Refuted` would be
false at reflexive pairs, where `rp_refl` needs no certificate. Pair witnesses are
derived: `certified_witness_at` gives an `RPath` at every seam crossing.

### What is data now (all `Type`)
- `CertifiedTransport`: observational, construction, maintenance, authority.
- `ConstructionCertificate`: inhabitant, `ExhibitionCertificate` (record id,
  identifiers, process, retained record + evaluator, coverage, custodian),
  `LineageCertificate`, grounding.
- `Lineage` is finite data (lists), mirroring the OCaml record.
  `LineageCertificate` carries graph, `CoverageRecord` (with gaps) and the issued
  `LineageVerdict` as data, plus proofs.
- `RPath`: witnesses, each crossing carrying a full `CertifiedTransport`; the `GT`
  of a generic `GTransport` (`rich_structure`). Erasure is two-stage and lossy:
  `RPath -> OPath` (drop certificates) `-> rval x = rval y` (drop crossings).
- Failures are data: `FibreWitness`, `SeamEmpty`, `GroundingFailure r`,
  `ExhibitionDefeated`, `LineageDescent`, `LineageUndisclosed n`,
  `LineageNoIndependentSource`, `LineageMalformed`, `MaintenanceFailureAt`
  (no evolution, or a lost seam element per evolution).

### Extraction check (`extraction/ExtractAssessment.v`)
The assessments extract to OCaml and the evidence survives: lineage graph,
custodian, record id, coverage, verdict, obstruction constructors and their data
(a seam element, an undisclosed node id). The proof fields vanish. A consumer
(`extraction/inspect_assessment.ml`, run once, 2026-09-21) reports for the
examples: copied -> `Refuted [Construction(LineageDescent)]`; missing/partial
lineage -> `Open`; maintenance lost -> `Refuted [Maintenance]`; copied +
maintenance lost -> `Refuted [Construction(LineageDescent); Maintenance]`;
grounded -> `Certified` with custodian=7 record=1 ground node=5 `LineagePass`.
Not part of `_CoqProject`; build instructions are in the file.

## Layers

1. **Legacy** (`legacy/exactness-2026/`): byte-identical, checksums verified,
   built as library `Exactness`.
2. **Generic calculus** (`theories/{Core,Contexts,Obstructions}`).
3. **Compatibility** (`theories/Instances/Original*.v`).
4. **Assessment** (`theories/Debt/`):
   - *Abstract skeleton*: `Assessment.v` (a refutation is a bare `P -> False`),
     `DebtClassifier`, `OriginalObligations`; kept for the decidable special case
     and `Transportable` correspondence.
   - *Located, evidence-bearing*: `Certificates`, `EvidenceObligations`,
     `GroundedWitness`, `TransportAssessment`, `MaintenanceDebt`.

## Earlier milestones (still valid)
Original-seam reconciliation; dynamic seams (structural naturality, valuation
naturality with `UV`, `PreservesGroundingOnImage`, coverage); extensional
theorem and grounded corollary. See `paper/theorem-ledger.md`.

## Axioms
Kernel axiom-free (`coqchk` succeeds without the classical file; all 32 new
theorems closed under `Print Assumptions`). `constant_factors` is isolated in
`Obstructions/ClassicalFactorisation.v`.

## What a `Certified` assessment does NOT show
Given the declared records and their checks, transport is warranted within the
formal regime. It does not show that the declared lineage includes every real
production path, that raw inputs represent the concrete process, that the state
model fits the real target, that an authority is competent or legitimate, or that
the declared seam is what actually happened. Those are construction and
institutional debt. Certificates are ISSUED outside the kernel.

## What is and is not connected
- `LineagePasses` is a Coq specification of Definition 13. `lineage_check` is
  PROVED to decide it. The handwritten OCaml audit is NOT proved equivalent; it is
  regression-tested against the extracted checker (case study and 3000 random
  records). The handwritten OCaml still does not construct certificates; the
  extracted checker does (`issue_certificate`).
- OCaml's justified/open-defeater distinction is modelled by `Disposition`, but
  L2 only requires some disposition, as in the OCaml.
- Exhibition conditions (ii), (iv), (v) are recorded, not verified.
- The lineage record is part of the DECLARED problem, so witnesses differing in
  lineage belong to different candidates (`DifferentWarrants.v` compares them via
  the extractable `witness_summary`). The summary projects exhibition and lineage
  data, plus maintenance and authority evidence through the `EvidenceSummary`
  interface (types stay abstract; applications supply instances).
- "Only X flagged" means one failure under the declared history stated at the top
  of each example; the categories are diagnostic loci, not a partition.

## Open
1. Replace the handwritten audit's decision core with the extracted checker in
   the case-study driver (the audit is otherwise done: Coq checker <-> Coq spec is
   proved; Coq checker vs OCaml is regression-tested).
2. Coverage-qualified passes ("pass relative to L") as a first-class result, not
   only an `Open` reason; several candidate grounds.
3. Functoriality over a whole interval `I_t`, not one transition.
4. A second concrete `EvCandidate` from the tax-jurisdiction case study.
5. `OpenReason` is a small fixed enumeration.
6. Phase 6, rewriting tactics: still deliberately not started; the semantics they
   would rest on now exist.
