# Theorem ledger

Status: **existing** (legacy supplement, checked there and re-checked here as the
library `Exactness`), **recovered** (existing result re-derived from the generic
calculus, statement unchanged), **new**, **conjectural**.

| Result | Status | Location |
|---|---|---|
| Admissibility characterisation (Thm 2.3) | existing | admissibility paper |
| `fibre_constant_admissible`, `witness_refutes` | existing | `legacy/.../Admissibility.v` |
| Fibre obstruction (generic) | new; legacy `witness_refutes` recovered from it | `Obstructions/FibreObstruction.v`, `Instances/OriginalAdmissibility.v` |
| Fibre factorisation, functional converse | new, **classical axioms**, isolated | `Obstructions/ClassicalFactorisation.v` |
| `evolution_id`, `evolution_compose` | existing | `legacy/.../GroundedSeam.v` |
| `seam_transport`, `seam_transport_admissible` | existing; **recovered** exactly | `Instances/OriginalGroundedSeamInstance.v` |
| `copied_not_grounded` (+ `copied_extensionally_coherent`) | existing; **recovered** from generic obstruction | same |
| Boolean reflection, extraction boundary | existing, not ported | legacy |
| Lineage audit (Definition 12, OCaml) | existing; not connected to Coq | `legacy/.../jurisdiction.ml` |
| `GTransport`, `gt_refl`, `gt_compose` | new | `Core/GroundedTransport.v` |
| `erasure_sound`, erased preorder, exact recovery under completeness | new | `Core/Erasure.v` |
| Grounded does not imply-collapse: `pairwise_agreement_not_grounding` | new (uses legacy lemmas) | `Instances/OriginalGroundedSeamInstance.v` |
| `original_grounding_erases_to_extensional` | new | same |
| `GroundedProper`, `gp_comp`, contextual preservation | new | `Contexts/` |
| Extensional factor transport; grounded corollary | new; `seam_transport` recovered as the corollary | `Instances/OriginalGroundedSeamInstance.v` |
| Valuation naturality (with value transport) => preservation on the image | new | `Instances/OriginalDynamicSeamInstance.v` |
| Surjective evolution preserves all grounding | new | same |
| `SeamEvolution` grounded-proper under `PreservesGroundingOnImage` | new (hypothesis exposed in the name) | same |
| Structural naturality does not give preservation; preservation does not give coverage | new (examples) | `examples/MaintenanceFailure.v`, `examples/EvolutionCoverage.v` |
| Exhibition and lineage certificates; Definition 13 as a specification | new | `Debt/Certificates.v` |
| Three-way assessment; certification, refutation, underdetermination theorems | new | `Debt/Assessment.v` |
| Boolean classifier as decidable special case | new | `Debt/Assessment.v` |
| Certificate -> `Transportable` -> witness -> erasure | new | `Debt/EvidenceObligations.v` |
| Data-bearing `CertifiedTransport`, `RPath` witnesses, `rich_structure` (a `GTransport`) | new | `Debt/GroundedWitness.v` |
| Located obstructions; `TransportAssessment` (Certified / Refuted / Open); `assemble` and its status, non-emptiness and reporting theorems | new | `Debt/TransportAssessment.v` |
| Erasure not reflecting; different warrants same endpoints; dynamic failure invisible to ordinary rewriting | new (examples) | `examples/CopiedCoordinates.v`, `DifferentWarrants.v`, `MaintenanceFailure.v` |
| Evidence survives extraction (OCaml consumer) | checked, not a theorem | `extraction/` |
| Lineage obstruction | new | `Obstructions/LineageObstruction.v` |
| Debt classifier: soundness, relative completeness | new | `Debt/DebtClassifier.v` |
| Four debts bound to `Transportable` (Prop interface layer); maintenance bound to `SeamEvolution` | new | `Debt/OriginalObligations.v`, `Debt/MaintenanceDebt.v` |
| Ancestors by saturation, sound and complete; L1/L2/L3 and well-formedness reflection; unconditional `lineage_check_reflect` | new | `Debt/LineageCheck.v` |
| Located rejection with proved evidence; coverage-qualified Open | new | same |
| Certified certificate issuer (`issue_certificate`) | new | same |
| Checker rejection -> located `ConstructionFailure` | new | `Debt/LineageAssessment.v` |
| `PackedWarrant`; same endpoints, different problems | new | `Debt/PackedWarrant.v`, `examples/DifferentWarrants.v` |
| `EvidenceSummary` interface | new | `Debt/Certificates.v` |
| Extracted checker agrees with the handwritten OCaml audit (5/5 case study; since v6, 1921/1921 random on the legacy overlap, 1079 of 3000 skipped) | tested, NOT a theorem | `extraction/run_lineage_regression.sh` |
| Handwritten OCaml audit proved equivalent to `LineagePasses` | conjectural (superseded by replacing its decision core) | - |
| Regional obstruction; fork/order/quorum obstructions | existing, separate | - |

| Certification / refutation soundness against the legacy `Transportable` (`TransportableFull`) | new | `Debt/TransportAssessment.v` |
| Historical pre-V6 stratified regression (11 x 300) and 12-mutant study | tested, NOT a theorem | `extraction/` |

| Two-level contexts: `CrossingProper`, `CertificateProper`, composition, chain, evidence lift (`ProblemMorphism`) | new | `Debt/CertificateProper.v` |
| Certificate reissue; no evidence lift when grounding is lost | new (example) | `examples/CertificateReissue.v` |
| Legacy vs full transportability: refutation soundness at the correct level | new | `Debt/TransportAssessment.v` |
| Historical pre-V6 deep-ancestry populations; 13-mutant, per-suite study | tested, NOT a theorem | `extraction/` |

## V6 lineage milestone (2026-09-29)

| Claim | Status | Where |
|---|---|---|
| Checker reflects the v6 conditions (ground identity in L1, declared ground in WF, the ground may be its own L3 source) | proved; theorem names unchanged | `check_L1_reflect`, `check_L3_reflect`, `lineage_defect_none_iff`, `lineage_check_reflect` |
| L1 composes across consecutive coordinate pairs, for a fixed graph and ground | proved | `L1_at_composes` (`examples/LineageNonComposition.v`) |
| L2 does not compose: AB and BC pass, AC fails only L2 | proved countermodel | `disclosure_noncomposition` |
| L3 does not compose: AB and BC pass, AC fails only L3 | proved countermodel | `source_noncomposition` |

| Current regression: 5 fixed cases; 1921 legacy-overlap random cases (1079 skipped); 3300 shallow; 1800 deep; six edge checks | tested, NOT a theorem | `extraction/` |
| Current mutation union: 17/17; fixed 5, random 12, shallow 11, deep 8, edge 4; stratified union 13; M14--M17 detected only by edge | tested, NOT a theorem | `extraction/mutation_matrix.py` |
