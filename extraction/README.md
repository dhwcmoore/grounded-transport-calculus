# Extraction / OCaml

`ExtractLineageCheck.v` extracts the PROVED lineage checker; `run_lineage_regression.sh`
builds it and runs `lineage_regression.ml` against the handwritten audit
(case study; random records on the legacy overlap; stratified populations; v6
edge cases).

`ExtractAssessment.v` extracts the assessments of the examples to OCaml; 
`inspect_assessment.ml` consumes them. Their point: the certificates and located
obstructions are DATA (lineage graph, custodian, coverage, verdict, obstruction
constructors) and survive extraction, whereas Prop-valued evidence would not.

The OCaml lineage audit is not duplicated here. It is preserved in
`../legacy/exactness-2026/jurisdiction.ml` (section "Lineage audit of a claimed
ground (Definition 12)", from line 154), and the extraction boundary in
`certified_temporal_seam.ml(i)` / `SeamExtraction.v`.

The lineage checker (`theories/Debt/LineageCheck.v`) is proved to reflect `LineagePasses`;
its agreement with the handwritten audit is tested, not proved.

In the Rocq development, the evidence layer (`theories/Debt/Certificates.v`)
defines `LineagePasses`, the Coq form of the lineage specification (since v6 it no
longer matches the handwritten audit everywhere; see Legacy overlap below), and
`LineageCertificate` carrying its proofs. Equivalence with the
OCaml audit is NOT proved, and the OCaml does not build kernel certificates.

In the interface layer, conditions (a) exhibition and (b) lineage grounding are
the abstract Props `cExhibited` and `cLineage` of `Debt/OriginalObligations.v`,
exactly as `Exhibited` and `LineageGrounded` are in the legacy `Transportable`.
The audit decides (b) on declared lineage records outside Coq; it is not
verified against those Props. That link is open work.

## Stratified regression and mutation study
`run_lineage_regression.sh` also runs seventeen stratified populations (eleven
shallow and six deep, 300 graphs each) with intended outcomes, and six v6 edge
cases. `mutation_matrix.py WORKDIR` (WORKDIR = the work directory given to the
regression script) mutates the extracted checker seventeen ways and reports which
suite detects each. Both are tests, not theorems.

## Legacy overlap
The handwritten audit predates the v6 conditions, so the random comparison uses
only records in the legacy overlap (`legacy_overlap` in `lineage_regression.ml`):
the ground differs from both coordinates and is not a purely raw node. On these
records, inspection of the definitions shows the v6-only clauses to be inactive;
agreement there is regression evidence, not a proof of equivalence. Records outside it are skipped,
not resampled (1079 of 3000 at the time of writing); the v6 clauses are tested by
the edge cases instead.

## Usage
From the repository root, after `dune build --root .`:

```sh
WORK=$(mktemp -d)
extraction/run_lineage_regression.sh "$WORK"
python3 extraction/mutation_matrix.py "$WORK"
```

## Issuance and execution boundary

`issue_certificate` builds a proof-bearing record in Coq; extraction retains data
and erases proofs. Issuance requires WF, L1--L3 and an empty declared gap list.
A `Justified` or `OpenDefeater` entry satisfies disclosure by membership;
resolution and disposition-key validation are not checked. Actual coverage,
source accuracy and L4 remain outside the checker.

`ExtrOcamlNatInt` requires non-negative encodings and identifiers, counters and
all intermediate arithmetic within OCaml machine-integer range. The extraction
mechanism, compiler, runtime and input encoding are trusted. The assessment
consumer uses `Obj.magic` for dummy endpoints in its witness-summary calls;
that demonstration is not a coercion-free sealed-interface guarantee.

The current mutation union detects 17/17. Fixed, random, shallow, deep and edge
suites detect 5, 12, 11, 8 and 4 respectively; shallow and deep together detect
13, and M14--M17 are detected only by edge cases. These are test outcomes,
not additional proofs of semantic equivalence or production fidelity.
