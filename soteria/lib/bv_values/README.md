# Kanon in soteria

The simplifying smart constructors of `Bv_values.Svalue` (`Bool.and_`,
`BitVec.add`, `Float.eq`, ...) are written in
[Kanon](https://github.com/N1ark/kanon), a rule language for the smart
constructors of a value language, which generates their OCaml implementation
and a Lean proof of their soundness. See Kanon's README for the language.

- `soteria/lib/bv_values/rules/` declares the language of Bv_values
  (`lang.knl`, which uses its modules), and its modules `exists`, `bitvec`,
  `float` and `ptr`: their declarations (`.knl`) and rules (`.kn`).
- It also uses `bool` (booleans, equality, `Ite` and `Distinct`), the module
  built into kanon (`use +bool`).

The `kanon` tool, which soteria pins in its `Makefile` and CI (see
`KANON_COMMIT_HASH` in `scripts/versions.json`), generates `svalue_rules.gen.ml`
and `lang_check.gen.ml` in the language's directory: dune regenerates them and
promotes them to the source tree, where they are committed, and
`[%%include_file "svalue_rules.gen.ml"]` (the ppx `kanon.ppx_include_file`)
includes them where their primitives are in scope, in `Svalue.Make`.

## Tests

`soteria/tests/bv_rules/` runs the differential tests that `kanon ocaml-tests`
generates: it draws small well-typed arguments for every rule function of
Bv_values, and checks with `Eval` that its result refines its spec under random
assignments of the variables. `KANON_RULE_STATS=1` prints how often each rule
fired.
