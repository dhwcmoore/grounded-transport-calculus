# Online Resource 1

This resource accompanies the manuscript *The Work of Exactness: Whitehead,
Warrant Debt, and Computational Systems*. It is anonymised for peer review.

## Reference environment

- Coq 8.18.0
- OCaml 4.14.1

Run `make check` or `./build.sh`. The target checks the pinned versions,
compiles the three Coq files, extracts the two runtime decision procedures to
OCaml, runs the OCaml enumerations, compares their output byte for byte with the
recorded output, and runs the interface-boundary tests. `make_check_output.txt`
is the complete transcript of a clean run in the reference environment;
`SHA256SUMS` lists checksums of every source and recorded-output file.

## Source map

| Manuscript claim | File or output label |
| --- | --- |
| Constructive finite fibre criterion | `Admissibility.v`: `fibre_constant_admissible` |
| Witness refutes admissibility | `Admissibility.v`: `witness_refutes` |
| Certified evolution identity and composition | `GroundedSeam.v`: `evolution_id`, `evolution_compose` |
| Grounded transport with a supplied factor | `GroundedSeam.v`: `seam_transport` |
| Seam and grounding witnesses refute the grounding equations | `GroundedSeam.v`: `seam_witness_refutes`, `grounding_witness_refutes` |
| Ungrounded agreement counterexample, equational part | `GroundedSeam.v`: `copied_not_grounded` |
| Runtime square check and grounding check, Boolean reflection | `GroundedSeam.v`: `squares_bool_reflect`, `grounding_bool_reflect` |
| Extraction of the runtime checks | `SeamExtraction.v`, generating `seam_checks.ml` and `seam_checks.mli` at build time |
| Finite checker with verified factor table and pre-check | `admissibility.ml` |
| Tenant, pressure, and composition enumerations (Section 14) | `examples.ml` |
| Tax-jurisdiction migration and lineage audit (Section 15) | `jurisdiction.ml` |
| Extraction boundary | `certified_temporal_seam.mli`, its implementation, and the `interface_*.ml` tests |

The Coq predicate `GroundingEquations` is the equational condition (c) of the
manuscript's grounded seam coherence (Definition 13). Conditions (a),
exhibition, and (b), lineage grounding, are not Coq propositions; they enter the
Coq `Transportable` definition as the abstract parameters `Exhibited` and
`LineageGrounded`, and condition (b) is decided on declared lineage records by
the OCaml audit described below.

## The finite checker

`Admissibility_check.check` returns one of four verdicts.

- `MalformedCertificate reason`: the pre-check failed. It rejects an
  observational equality that is not reflexive on the observed image or not
  symmetric on its representatives. It also rejects a factor table that fails
  verification, which is how a non-transitive equality that matters is caught.
  Completeness of the state list remains the caller's declaration and cannot be
  checked.
- `Inadmissible (s, s')`: an observational witness.
- `Admissible table`: returned only for a list declared complete, with a factor
  table (one representative observation per fibre and the predicate value on
  it). Before returning, the checker verifies `Phi s = factor (M s)` for every
  enumerated state. `eval_factor` evaluates the table and returns `None` off
  the image of `M`, where the factor is unconstrained.
- `NoWitnessFound`: no witness in a list not declared complete.

## Extraction boundary

`SeamExtraction.v` extracts `squares_bool` and `grounding_bool` from
`GroundedSeam.v`. `certify` and `certify_grounded` in
`certified_temporal_seam.ml` accept or reject solely on the result of these
extracted procedures, whose correctness is stated by the two reflection
theorems. After a rejection, a hand-written search reports a witness for
diagnosis; it does not decide acceptance.

Trusted rather than proved: the Coq extraction mechanism; the realisation of
Coq `nat` as OCaml `int` (`ExtrOcamlNatInt`), exact for the small non-negative
identifiers used; and the hand-written record type, identity, and composition,
which mirror the Coq `SeamEvolution` record by inspection. Proof terms are
erased, so the sealed interface enforces a conditional boundary: it holds for
well-typed clients confined to the interface and fails under `Obj.magic`,
unchecked marshalling, or foreign code, as `interface_unsafe_cast.ml`
demonstrates.

## Manuscript numbers

The recorded output in `examples_output.txt` maps to Section 14 as follows.

- Tenant isolation: `phi on M1` `fibres=  4 mixed= 2`; `phi on M2`
  `fibres=  6 mixed= 0`; the incomplete `c=o` sample returns `NoWitnessFound`.
- Pressure telemetry: `phi on M_sum` `fibres= 10 mixed= 4` with witness
  `(0,0,3) / (0,1,2)`; `phi on (sum,max)` `fibres= 16 mixed= 0`;
  `kernel of <M_sum, phi>: 14 blocks`.
- Composition: `psi on C = <phi1,phi2>` `fibres=  3 mixed= 2` with witness
  `(a,a,false,a) / (a,b,true,a)`; the repair `psi on C' = <phi1,phi2,phi3>`
  `fibres=  6 mixed= 0`; `psi = not phi1 or phi3 on every state: true`;
  `phi3 = psi on every state: false`; the owner-only alternative returns the
  witness `(a,a,true,b) / (a,b,true,a)`.
- Pre-check: a non-reflexive equality returns `MalformedCertificate`.

Every `Admissible` line also reports the size of its verified factor table.

The recorded output in `jurisdiction_output.txt` maps to Section 15 as follows.

- State model: `|S| = 864`; the target predicate holds on `96` states.
- Static stage-t surface: `fibres= 720 mixed= 28`.
- Static stage-(t+1) surface: `fibres= 360 mixed=  0`.
- Declared incomplete sample: `NoWitnessFound`.
- Seam carrier: `carrier=1728`.
- As-migrated seam: `seam_witnesses=48`, `grounding_witnesses=74`,
  `agree_but_ungrounded=26`.
- Repaired seam: `seam_witnesses=72`, `grounding_witnesses=72`,
  `agree_but_ungrounded=0`.
- Backfill translation coverage: `|D|=864`.

## Lineage audit (Definition 12)

A lineage record declares its derived fields and their parents, the raw inputs,
the claim-relevant subset of the raw inputs, the three distinguished nodes, and
a disposition (`Justified` or `Open_defeater`) for shared derived ancestors.
The audit first validates the record: unique names, raw inputs not derived,
every parent declared, the distinguished nodes present, claim-relevant inputs
raw, and acyclicity by depth-first search. A defective record returns
`MalformedLineage` with the defect. Ancestors are computed with a visited set,
so the audit terminates on any input.

On a well-formed record the audit returns pass or fail for each condition.

- L1: the seam valuation has neither coordinate among its ancestors.
- L2: every shared non-raw ancestor of the coordinates has a disposition.
- L3: the ground-only ancestry contains a claim-relevant raw input.

The five recorded results are these.

- `live rows`: all three pass; the ground-only nodes are `carrier_scan`,
  `delivery_event`, and `m_delivered`, of which `delivery_event` is the
  claim-relevant raw input; lineage-grounded.
- `backfill rows`: all three pass, with `zone` disclosed as an open defeater;
  lineage-grounded. The 26 agreeing grounding witnesses are then found by the
  grounding equations, not by the lineage audit.
- `backfill, zone undisclosed`: L2 fails.
- `copied seam valuation`: L1 and L3 fail; this is the copied valuation of the
  ungrounded-agreement proposition.
- `cyclic record`: `MalformedLineage: cycle through zone`.

The audit checks a declared graph. It cannot detect a production path the graph
omits, and it does not test the accuracy of any raw input.

## Trust boundary

Completeness of the finite state list and correctness of observational
equality, beyond the reflexivity, symmetry, and factor-verification checks
above, are declared inputs. The Coq proofs do not establish that the model is
relevant to a concrete process.
