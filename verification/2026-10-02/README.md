# Fresh verification at the pinned transport revision

Source: `e1e14a23a59906af0b14c556054133501a9b3612`; root tree
`f059c32fa0a0c0621657e49eb40052f166c5aec6`. All 120 tracked blobs matched
GitHub's recursive tree before execution. `source-SHA256SUMS` is relative to
that pristine source root, not this later documentation branch.

`03-coqchk-36.txt.gz` contains the complete unabridged transcript; decompress
with `gzip -dc`. The 36 project arguments exclude the isolated classical
factorisation module. Standard library dependencies are checked as well.
`04-assumptions-123.txt` records 123 closed identifiers; the classical
exception is separately visible in `05-classical-exception.txt`.

All final commands exited 0. Dune 3.14.0 built the unchanged Dune 3.8 project
language with Coq 8.18.0 and OCaml 4.14.1. Packages were retrieved from the
Ubuntu snapshot and checked against package-index SHA-256 values. The local
environment initially lacked `/usr/bin/ocamlrun` and `/usr/lib/ocaml`; links
to the extracted matching runtime/libraries supplied those paths before the
successful OCaml runs. The earlier failed Findlib attempt is preserved.

Regression: 5/5 fixed, 1921/1921 random on the legacy overlap (1079 of 3000
skipped), 3300 shallow, 1800 deep, six edge checks on three fixed records.
Mutation union: 17/17; fixed/random/shallow/deep/edge 5/12/11/8/4; stratified
union 13; M14--M17 edge only. The assessment consumer reproduces 7/1/5 and
LineagePass, but its witness-summary demonstration uses Obj.magic.

These transcripts establish this pinned revision only. They do not bind an
unseen revised manuscript or Paper 2A's unconfirmed current artefact. A tag,
archival DOI and public archive retrieval remain separate release steps.
