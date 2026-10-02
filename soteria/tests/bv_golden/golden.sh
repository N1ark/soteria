#!/bin/sh
# Dumps the Bv_values golden output (about 2.7 MB, hence not committed) to $1.
# Usage: soteria/tests/bv_golden/golden.sh OUT [SEED]
# Compare dumps produced before and after a change with [cmp].
set -e
out=${1:?usage: golden.sh OUT [SEED]}
dune build soteria/tests/bv_golden/bv_golden.exe
dune exec --no-build -- soteria/tests/bv_golden/bv_golden.exe ${2:+"$2"} >"$out" 2>"$out.coverage"
