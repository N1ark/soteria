# Kanon in soteria

The simplifying smart constructors of `Bv_values.Svalue` (`Bool.and_`,
`BitVec.add`, `Float.eq`, ...) and of `Tiny_values.Svalue` are written in
[Kanon](https://github.com/N1ark/kanon), a rule language for the smart
constructors of a value language, which generates their OCaml implementation
and a Lean proof of their soundness. See Kanon's README for the language.

- `soteria/lib/bv_values/rules/` declares the language of Bv_values
  (`lang.knl`), and its modules `bitvec`, `float` and `ptr`: their declarations
  (`.knl`) and rules (`.kn`).
- `soteria/lib/tiny_values/rules/` does the same for Tiny_values, with the
  module `int`.
- `modules/` has the modules that both languages share: `bool` (booleans,
  equality, `Ite` and `Distinct`) and `exists` (Bv_values only, for now).
- `lean/` is the Lean proof of the rules of Bv_values.

The `kanon` tool, which soteria pins in its `Makefile` and CI (see
`KANON_COMMIT_HASH` in `scripts/versions.json`), generates `svalue_rules.gen.ml`
and `lang_check.gen.ml` in each language's directory: dune regenerates them and
promotes them to the source tree, where they are committed, and
`[%%include_file "svalue_rules.gen.ml"]` (the ppx `kanon.ppx_include_file`)
includes them where their primitives are in scope, in `Svalue.Make` for
Bv_values and in a plain module for Tiny_values, which has no Lean model yet.

## Proofs

`lean/` is a Lean project, whose generated files (`kanon lean-all`) `dune test`
checks to be up to date (run `dune promote` after changing the rules):

- `Types.lean` and `Syntax.lean` define the types of the language, around
  `Abstract.lean` (written by hand), and which operators commute
  (`Binop.Comm`, from `[@comm]`; `Lib/Cases.lean` proves that they do), and
  `Typing.lean` the typing of the operators.
- `Model.lean` is a Lean model of the rule functions, over the primitives of
  `Prims.lean`, and `Semantics.lean` gives terms their meaning (written by
  hand), parameterised by a semantics of floats `FS`.
- `Statements.lean` states that every alternative of every rule is sound: its
  result *refines* its spec (the raw term it simplifies): it has the same sort,
  and the same value wherever the raw term has one.
- `Soundness.lean` proves each rule from its alternatives, and every function
  from its rules, up to `Kanon.opsN_sound`: the whole simplifier is sound.

The proof of an arm is the theorem tagged `@[kanon_arm]` that proves
`f.r_name.arm.Stmt` in `lean/Kanon/Proofs/`, if there is one; otherwise the
tactic given to its function by `attribute [kanon_tactic tac] f.spec`, in the
library that defines `tac` (`lean/Kanon/Lib/`); otherwise `kanon_auto`.
`kanon_arm` rejects a theorem that proves no arm, or an arm that already has a
proof.

`lean/Kanon/Core/` is a trial of modules proved once for any language
(`Bool.lean`, `Int.lean`, `Example.lean`), over the generic core of Kanon
(`Kanon.Core.Lang`, in Kanon's repository).

`lake build` checks every proof, and CI checks that the soundness theorem
depends on no `sorry` (`check_axioms.lean`).

## Tests

`soteria/tests/bv_rules/` runs the differential tests that `kanon ocaml-tests`
generates: it draws small well-typed arguments for every rule function of
Bv_values, and checks with `Eval` that its result refines its spec under random
assignments of the variables. `KANON_RULE_STATS=1` prints how often each rule
fired.
