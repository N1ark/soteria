# Kanon in soteria

The simplifying smart constructors of `Bv_values.Svalue` (`Bool.and_`,
`BitVec.add`, `Float.eq`, ...) and of `Tiny_values.Svalue` are written in
[Kanon](https://github.com/N1ark/kanon), a rule language for the smart
constructors of a value language, which generates their OCaml implementation
and a Lean proof of their soundness. See Kanon's README for the language.

- `soteria/lib/bv_values/rules/` declares the language of Bv_values
  (`lang.knl`, which uses its modules), and its modules `exists`, `bitvec`,
  `float` and `ptr`: their declarations (`.knl`) and rules (`.kn`).
- `soteria/lib/tiny_values/rules/` does the same for Tiny_values, with the
  module `int`.
- Both languages use `bool` (booleans, equality, `Ite` and `Distinct`), the
  module built into kanon (`use +bool`).
- `soteria/lib/bv_values/lean/` and `soteria/lib/tiny_values/lean/` are the
  Lean proofs of the rules of Bv_values (library `Kanon`) and of Tiny_values
  (library `Tiny`).

The `kanon` tool, which soteria pins in its `Makefile` and CI (see
`KANON_COMMIT_HASH` in `scripts/versions.json`), generates `svalue_rules.gen.ml`
and `lang_check.gen.ml` in each language's directory: dune regenerates them and
promotes them to the source tree, where they are committed, and
`[%%include_file "svalue_rules.gen.ml"]` (the ppx `kanon.ppx_include_file`)
includes them where their primitives are in scope, in `Svalue.Make` for
Bv_values and in a plain module for Tiny_values.

## Proofs

Each language has a Lean project, in its `lean/` directory, with a library:
`Kanon` (the namespace `Kanon`) for Bv_values, and `Tiny` (the namespace
`Tiny`) for Tiny_values. Their generated files (`kanon lean-all`) `dune test`
checks to be up to date (run `dune promote` after changing the rules):

- `Types.lean` and `Syntax.lean` define the types of the language, around
  `Abstract.lean` (written by hand), and which operators commute
  (`Binop.Comm`, from `[@comm]`; `Lib/Cases.lean` proves that they do), and
  `Typing.lean` the typing of the operators.
- `Model.lean` is a Lean model of the rule functions, over the primitives of
  `Prims.lean`, and `Semantics.lean` gives terms their meaning (written by
  hand); that of Bv_values is parameterised by a semantics of floats `FS`, and
  that of Tiny_values follows the SMT-LIB encoding of its integers (Euclidean
  `div` and `mod`, Z3's `rem`, and dividing by zero is undefined behaviour).
- `Statements.lean` states that every alternative of every rule is sound: its
  result *refines* its spec (the raw term it simplifies): it has the same sort,
  and the same value wherever the raw term has one.
- `Soundness.lean` proves each rule from its alternatives, and every function
  from its rules, up to `Kanon.opsN_sound` (`Tiny.opsN_sound`): the whole
  simplifier is sound.

The proof of an arm is the theorem tagged `@[kanon_arm]` that proves
`f.r_name.arm.Stmt` in `Kanon/Proofs/` (`Tiny/Proofs/`), if there is
one; otherwise the tactic given to its function by
`attribute [kanon_tactic tac] f.spec`, in the library that defines `tac`
(`Kanon/Lib/`); otherwise `kanon_auto` (`Kanon/Lib/Rule.lean`,
`Tiny/Lib/Rule.lean`).
`kanon_arm` rejects a theorem that proves no arm, or an arm that already has a
proof.

Both libraries build on the Lean library of Kanon (`KanonCore`, required by
the `lakefile.toml`s at `KANON_COMMIT_HASH`), which gives `kanon_arm`,
`kanon_proof%` and the tactics `kanon_auto`, `kanon_comm` and `kanon_congr`
that each language extends.

`lake build` checks every proof, and CI checks that the soundness theorems
depend on no `sorry` (`check_axioms.lean`).
