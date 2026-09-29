#!/bin/sh
# Extract the checked lineage audit and compare it with the handwritten one.
# Run after the library is built (dune build or make). Works from any directory.
#
# Usage: extraction/run_lineage_regression.sh [WORKDIR]
#
# Compiled Coq libraries are read from Dune's build tree (_build/default) when
# it exists, and otherwise from the source tree, as a make build leaves them.
# Set GTC_LIBROOT to choose explicitly, for example GTC_LIBROOT=/path/to/repo
# to use source-tree .vo files even when a _build directory is present.
set -eu
ROOT=$(cd "$(dirname "$0")/.." && pwd)
WORK=${1:-$(mktemp -d)}
LEG="$ROOT/legacy/exactness-2026"

if [ -n "${GTC_LIBROOT:-}" ]; then
  LIBROOT=$(cd "$GTC_LIBROOT" && pwd)
elif [ -d "$ROOT/_build/default/theories" ]; then
  LIBROOT="$ROOT/_build/default"
else
  LIBROOT="$ROOT"
fi
echo "run_lineage_regression: compiled libraries from $LIBROOT" >&2

mkdir -p "$WORK"; cd "$WORK"
rm -f ExtractLineageCheck.* lineage_check_extracted.* *.cm* regression
# Compile a copy inside WORK so that no build products are written into extraction/.
cp "$ROOT/extraction/ExtractLineageCheck.v" .
coqc -R "$LIBROOT/legacy/exactness-2026" Exactness \
     -R "$LIBROOT/theories" GTC \
     -R "$LIBROOT/examples" GTCExamples \
     ExtractLineageCheck.v >/dev/null
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
