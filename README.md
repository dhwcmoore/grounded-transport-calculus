# Grounded Transport: Proof-Relevant Rewriting for Processual Ontologies

> Substitutability is not always exhausted by extensional equality. In
> lineage-sensitive systems, substitution requires an exhibited process
> connecting the terms, and contexts must preserve that processual warrant.

A small Rocq/Coq kernel extracted from an already verified special case
(grounded seams), together with the obstruction to observational substitution
and a classification of transport failure ("warrant debt").

## Build

Requires Coq/Rocq (developed against Coq 8.18).

```sh
coq_makefile -f _CoqProject -o Makefile.coq && make -f Makefile.coq
# or
dune build --root .
```

## Verification

From the repository root, after `dune build --root .`:

```sh
# kernel check of a module and everything it depends on
coqchk -R _build/default/legacy/exactness-2026 Exactness \
       -R _build/default/theories GTC \
       -R _build/default/examples GTCExamples \
       GTCExamples.LineageNonComposition

# extracted lineage checker against the handwritten audit
WORK=$(mktemp -d)
extraction/run_lineage_regression.sh "$WORK"

# mutation study of the extracted checker, on the same work directory
python3 extraction/mutation_matrix.py "$WORK"
```

The regression script can be run from any directory. It reads the compiled
libraries from `_build/default` when a Dune build exists and from the source
tree otherwise (a `coq_makefile` build); set `GTC_LIBROOT` to choose
explicitly. `STATUS.md` records the current results. The pinned formal revision is
`e1e14a23a59906af0b14c556054133501a9b3612`; PR 4 is merged. A single
`coqchk` invocation on `LineageNonComposition` checks that module and its
dependency closure, not all 36 non-classical project modules. The complete
36-module pass and 123-identifier assumption audit are recorded separately.

## Layout

| Path | Content |
|---|---|
| `theories/Core` | `GTransport` structure, identity, composition, erased relation, erasure soundness |
| `theories/Contexts` | `GroundedProper`, composition, contextual preservation |
| `theories/Obstructions` | fibre factorisation, lineage obstruction, ungrounded agreement |
| `theories/Debt` | four warrant debts (with a proved lineage checker, `LineageCheck.v`): abstract skeleton (decidable classifier) and the located, evidence-bearing layer (certificates, `RPath` witnesses, `TransportAssessment` = Certified / Refuted / Open) |
| `theories/Instances` | compatibility layer: the *original* grounded seam, `SeamEvolution` and admissibility as instances (`Original*.v`); `ExtensionalSeam.v` is the weaker pairwise-only layer |
| `examples/` | the original copied counterexample, seam transport, maintenance failure, different warrants, evolution coverage, certificate reissue, lineage certificates, the checked lineage audit, and lineage non-composition |
| `paper/` | outline, theorem ledger, notation |
| `legacy/exactness-2026/` | the original supplement, **unchanged** (checksummed); built as library `Exactness` |
| `extraction/` | extraction of the assessments and of the proved lineage checker; differential regression against the handwritten audit and a mutation study |
| `document/` | the manuscript (LMCS class) |
| `milestones/` | frozen, checksummed snapshots of earlier states |

See `STATUS.md` for what is proved, what is recovered from the legacy supplement, and what is open.

## Manuscript and reviewer release

The bundled LMCS manuscript records an earlier layout; the current intended
submission venue is the Journal of Logic and Computation. No arXiv upload is
needed to reproduce the artefact. A Git commit fixes the source revision;
a reviewer archive still needs a published persistent identifier. Do not cite
a DOI until the archive has been deposited and its public retrieval checked.
