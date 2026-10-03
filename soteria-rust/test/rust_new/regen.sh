#!/bin/sh
# Regenerates rust_types.gen.ml and rust_rules.gen.ml from rules/lang.knl.
# Usage: regen.sh [KANON_BIN]   (default: the NEW kanon, not the pinned one on
# PATH, which still implements the old syntax).
set -eu
here=$(cd "$(dirname "$0")" && pwd)
kanon=${1:-${KANON_BIN:-/home/user/kanon/_build/default/src/main.exe}}
cd "$here/rules"
"$kanon" ocaml-types lang.knl >"$here/rust_types.gen.ml.tmp"
"$kanon" ocaml lang.knl >"$here/rust_rules.gen.ml.tmp"
mv "$here/rust_types.gen.ml.tmp" "$here/rust_types.gen.ml"
mv "$here/rust_rules.gen.ml.tmp" "$here/rust_rules.gen.ml"
