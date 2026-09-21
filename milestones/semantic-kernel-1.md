# Milestone: semantic kernel 1 (2026-09-21)

Frozen state at the end of the located-evidence assessment milestone.
Contents: `semantic-kernel-1.tar.gz` (all sources and documents; no build
artefacts) and `semantic-kernel-1.sha256` (per-file SHA-256).

State at freeze: Coq 8.18.0; library, examples and `dune build --root .` build;
`coqchk` succeeds without `ClassicalFactorisation.v`; all reported theorems closed
under `Print Assumptions`; legacy supplement checksums verified.

Results at freeze: erasure (two-stage, with non-reflection), preservation for
contexts and qualified temporal evolution, located obstructions, and the
three-way `TransportAssessment` (Certified / Refuted / non-empty Open) with
`assemble_refuted_reports_all`; evidence survives extraction.

Later work builds on this kernel and does not alter its definitions. If a later
change must alter a kernel definition, record it here.

## Changes after the freeze (all ADDITIVE; none weakens a kernel definition or
## statement)

- `Debt/Certificates.v`: added `EvidenceAtom`, `EvidenceSummary` and instances
  (`unit_summary`, `authorisation_summary`).
- `Debt/EvidenceObligations.v`: `EvCandidate` gained two fields,
  `ecMaintenanceSummary` and `ecAuthorisationSummary` (`EvidenceSummary`
  instances). Existing candidates were updated to supply them.
- `Debt/GroundedWitness.v`: `WitnessSummary` gained `ws_maintenance` and
  `ws_authority`.
- `examples/{CopiedCoordinates,MaintenanceFailure,DifferentWarrants}.v`:
  updated for the new candidate fields; new results appended.
- New modules: `Debt/LineageCheck.v`, `Debt/LineageAssessment.v`,
  `Debt/PackedWarrant.v`, `examples/LineageChecked.v`.
- `_CoqProject`: lists the new files.

The frozen tarball restores byte-for-byte (`sha256sum -c
semantic-kernel-1.sha256` from an extracted copy).

## Further additive changes (paper drafting, 2026-09-21)

- `Debt/GroundedWitness.v`: added `crossing`, `crossings`, `WEquiv` and its laws.
- `Debt/TransportAssessment.v`: added `AssessmentReport`, `report_of`,
  `report_verdict`, `report_verdict_agrees`, `report_accounts_for_all`.
- `examples/MaintenanceFailure.v`: added `refuted_verdict_keeps_open_item`.
No existing definition or statement was altered.

## Further additive changes (LMCS drafting, 2026-09-22)
- `Debt/TransportAssessment.v`: added `TransportableFull`,
  `certified_transportable`, `located_refutes_transportable`,
  `refuted_not_transportable`. No existing definition or statement altered.
- `extraction/`: stratified populations and `mutation_matrix.py`.

## Further additive changes (review response, 2026-09-22)
- `Debt/TransportAssessment.v`: `TransportableFull` is now defined as
  `TransportableLegacy /\ inhabited authority` (previously a single conjunction);
  logically equivalent to the earlier definition. Added `located_refutes_legacy`,
  `institutional_refutes_full`, `full_iff_legacy_and_authority`,
  `certified_transportable_legacy`.
- New: `Debt/CertificateProper.v`, `examples/CertificateReissue.v`.
- `Contexts/GroundedProper.v`: documentation only.
No existing statement was weakened.
