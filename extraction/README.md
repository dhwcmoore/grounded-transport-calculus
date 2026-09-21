# Extraction / OCaml

`ExtractLineageCheck.v` extracts the PROVED lineage checker; `run_lineage_regression.sh`
builds it and runs `lineage_regression.ml` against the handwritten audit
(case study plus 3000 random records).

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
defines `LineagePasses`, a Coq specification of Definition 13 mirroring the audit
by inspection, and `LineageCertificate` carrying its proofs. Equivalence with the
OCaml audit is NOT proved, and the OCaml does not build kernel certificates.

In the interface layer, conditions (a) exhibition and (b) lineage grounding are
the abstract Props `cExhibited` and `cLineage` of `Debt/OriginalObligations.v`,
exactly as `Exhibited` and `LineageGrounded` are in the legacy `Transportable`.
The audit decides (b) on declared lineage records outside Coq; it is not
verified against those Props. That link is open work.

## Stratified regression and mutation study
`run_lineage_regression.sh` also runs eleven stratified populations (300 graphs
each) with intended outcomes. `mutation_matrix.py WORKDIR` (WORKDIR = the output
directory of the regression script) mutates the extracted checker twelve ways and
reports which stage of the harness detects each. Both are tests, not theorems.
