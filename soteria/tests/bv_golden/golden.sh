#!/bin/sh
# Dumps the golden output of the C language (about 2.7 MB, hence not committed)
# to $1 and, if $3 is given, compares it with the golden dump of the old
# stack, $3 (written by this script at the last commit before the migration to
# Kanon, f52223c).
# Usage: soteria/tests/bv_golden/golden.sh OUT [SEED [REFERENCE]]
#
# The only expected difference with the old stack: the location printed by
# [Printexc.to_string] for the assertion of [mk_bv] (file and line of the
# [assert], where the generator creates an out-of-range literal on purpose). It
# is normalised on both sides before comparing; the raw dumps are not touched.
set -e
out=${1:?usage: golden.sh OUT [SEED [REFERENCE]]}
dune build soteria/tests/bv_golden/bv_golden.exe
dune exec --no-build -- soteria/tests/bv_golden/bv_golden.exe ${2:+"$2"} >"$out" 2>"$out.coverage"
if [ -n "$3" ]; then
  norm() {
    sed -E 's/^(fact raised) File "[^"]*", line [0-9]+, characters [0-9]+-[0-9]+: /\1 <loc>: /' "$1"
  }
  if cmp -s "$out" "$3"; then
    echo "golden: byte-identical to $3"
  elif [ "$(norm "$out" | md5sum)" = "$(norm "$3" | md5sum)" ]; then
    echo "golden: identical to $3 up to assertion locations"
  else
    echo "golden: DIFFERENT from $3" >&2
    diff "$out" "$3" | head -40 >&2
    exit 1
  fi
fi
