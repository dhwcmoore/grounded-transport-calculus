#!/bin/sh
# Extract the checked lineage audit and compare it with the handwritten one.
# Run from the project root, after the library is built (make / dune build).
set -eu
ROOT=$(pwd)
WORK=${1:-$(mktemp -d)}
LEG="$ROOT/legacy/exactness-2026"
mkdir -p "$WORK"; cd "$WORK"
rm -f lineage_check_extracted.* *.cm* regression
coqc -R "$LEG" Exactness -R "$ROOT/theories" GTC -R "$ROOT/examples" GTCExamples \
     "$ROOT/extraction/ExtractLineageCheck.v" >/dev/null
cp "$LEG/admissibility.ml" "$LEG/jurisdiction.ml" "$ROOT/extraction/lineage_regression.ml" .
ocamlfind ocamlc -package unix -linkpkg -w -a \
  lineage_check_extracted.mli lineage_check_extracted.ml \
  admissibility.ml jurisdiction.ml lineage_regression.ml -o regression
if ./regression > regression.out 2>&1; then
  status=0
else
  status=$?
fi

sed -n '/=== extracted/,$p' regression.out
exit "$status"
