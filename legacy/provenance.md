# Provenance of legacy material

`legacy/exactness-2026/` is the online supplement to *The Work of Exactness:
Whitehead, Warrant Debt, and Computational Systems*, imported UNCHANGED
(2026-09-21).

- Found at `/data/exactness-submit/35/Submission_Package (1).zip` ->
  `ESM_1.zip` -> `Online_Resource_1/` (also `/data/exactness-submit/34/Submission_Package.zip`,
  identical contents by checksum).
- All 20 files match their entries in `SHA256SUMS` (the six authoritative
  hashes supplied by the author match as well).
- Recorded outputs were moved into `recorded-output/`; `SHA256SUMS` still lists
  them at the top level. To re-run the supplement's own `make check`, copy them
  back next to the sources (done in a scratch copy on 2026-09-21: the run
  completed under Coq 8.18.0 / OCaml 4.14.1).
- Nothing in `legacy/exactness-2026/` may be edited. `legacy/dune` (outside that
  directory) only builds `Admissibility.v` and `GroundedSeam.v` as the Rocq
  library `Exactness`; `SeamExtraction.v` is built by the supplement's Makefile.

## Where the lineage audit lives

There is no `lineage_audit.ml`. The audit (Definition 12) is the section of
`jurisdiction.ml` beginning at the comment
`(* ---------- Lineage audit of a claimed ground (Definition 12) ---------- *)`
(line 154): `lineage`, `well_formed`, `ancestors`, `audit`. It is not split
out, so that the preserved file stays byte-identical. See `../extraction/README.md`.
