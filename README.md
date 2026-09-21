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

## Layout

| Path | Content |
|---|---|
| `theories/Core` | `GTransport` structure, identity, composition, erased relation, erasure soundness |
| `theories/Contexts` | `GroundedProper`, composition, contextual preservation |
| `theories/Obstructions` | fibre factorisation, lineage obstruction, ungrounded agreement |
| `theories/Debt` | four warrant debts (with a proved lineage checker, `LineageCheck.v`): abstract skeleton (decidable classifier) and the located, evidence-bearing layer (certificates, `RPath` witnesses, `TransportAssessment` = Certified / Refuted / Open) |
| `theories/Instances` | compatibility layer: the *original* grounded seam, `SeamEvolution` and admissibility as instances (`Original*.v`); `ExtensionalSeam.v` is the weaker pairwise-only layer |
| `examples/` | the original copied counterexample, seam transport, maintenance failure |
| `paper/` | outline, theorem ledger, notation |
| `legacy/exactness-2026/` | the original supplement, **unchanged** (checksummed); built as library `Exactness` |

See `STATUS.md` for what is proved, what is recovered from the legacy supplement, and what is open.
