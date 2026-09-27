# Verifying the Bv_values reductions in Lean

## Goal

Every simplifying smart constructor in `soteria/lib/bv_values/svalue.ml`
(`Bool.*`, `BitVec.*`, `Float.*`, `Ptr.*`) is written **once**, in a small
rule language (BVR). From it we generate:

1. the OCaml implementation used by Soteria (`svalue_rules.ml`, generated at
   build time by dune, so it can never drift from the rules), and
2. a Lean model of the same functions, together with one soundness statement
   per rule. Hand-written Lean proofs discharge those statements; a generated
   "assembly" theorem combines them into soundness of the whole simplifier.

Enforcement: the committed Lean file is diffed against the generator output in
`dune test`, and CI runs `lake build`. Adding or changing a rule changes the
generated statement, so the Lean build fails until the rule is (re-)proved.

Out of scope: the knowledge-base simplifications in `analyses.ml` (which are
driven by the solver, not by construction) and the extension hook `V.mk`.

## The language (BVR)

BVR is a first-order, pure, typed subset of OCaml syntax, parsed with ppxlib,
so it reads like the code it replaces:

- Types: `bool`, `int` (mathematical integers: `Z.t` in OCaml, `Int` in Lean),
  `t` (terms), `ty`, `checked`, enums (`rm`, `fp`, `fc`), `float` (a concrete
  float literal), tuples, `option`, `list`.
- Term patterns match the *kind* of a term directly: `BitVec z`,
  `Binop (Add c, l, r)`, `Triop (Ite, b, x, y)`, with `as`, or-patterns and
  `when` guards. `k <| ty` builds a raw (unsimplified) node.
- Each case of a rule function carries a name (`[@r name]`), used to name its
  Lean obligation.
- Rule functions declare their specification: the raw node they must refine
  (`[@spec Binop (Add checked, v1, v2) <| ty v1]`).
- Primitives (`size`, `ty`, `equal`, `mk_masked`, float oracle calls, ...) are
  declared in the language and implemented once per backend by hand.

## Semantics and soundness statement (Lean)

- Terms are modelled as a Lean inductive mirroring `t_kind`/`t_node`
  (widths/indices as `Int`, like OCaml's unbounded-in-practice ints).
- `eval ρ t : Option Val` follows the SMT encoding (`encoding.ml`), with
  `none` meaning *poison*: ill-typed nodes, and checked (`Add {signed}`, ...)
  operations whose overflow flag is violated, evaluate to poison — like
  LLVM's `nsw`. `ite` is lazy and `&&`/`||` are "parallel" (a `false` operand
  wins over poison), so a flag only has to hold where its value is demanded.
- Soundness of a smart constructor `f` with spec `raw`: for every environment
  `ρ`, if `eval ρ raw = some v` then `eval ρ (f args) = some v` (refinement).
  On models of a path condition every flag holds, so there refinement is
  equality with the SMT semantics that ignores flags.
- Hash-consing: `equal` is structural equality; commutative normalisation
  uses an opaque tag order (proofs hold for any order).
- Floats: SMT-LIB semantics (NaNs identified). Arithmetic is abstract; the
  concrete `Floatml` operations are an explicit, documented trust assumption
  (a hypothesis structure every theorem takes), not axioms.

## Proof architecture

- Generated: `Ops` (a record of every rule function), for each rule `f_r` a
  function `f_r : Ops → args → Option Term` (pattern + guard + RHS, recursive
  calls through `Ops`), `f_step` (first rule that fires, else the raw node),
  and `opsN : Nat → Ops` (fuel; fuel 0 = raw constructors).
- Generated statement per rule: `O.Sound → f_r O args = some r → refines`.
- Hand-written: those proofs, grouped per area.
- Generated assembly: `∀ n, (opsN n).Sound` by induction on fuel. The OCaml
  function (the least fixpoint) returns, when it terminates, what `opsN n`
  returns for a large enough `n`: partial correctness.

## Steps (each ends with a commit)

1. This plan.
2. BVR generator: parser, type checker, OCaml backend. Move the AST types out
   of `svalue.ml` into `svalue_ast.ml`.
3. Port every rule to BVR, generating the OCaml. Validate: build, the existing
   tests, the Z3 fuzzer, and a differential test (old vs generated
   implementation on random terms, compared structurally).
4. Lean semantics (hand-written) and Lean backend; generated model +
   statements; dune diff rule; CI job.
5. Proofs, one area per commit (Bool, arithmetic, bitwise, extract/extend/
   concat, shifts, mul/div/rem, comparisons, overflow, float/ptr).
   Rules found unsound get the smallest fix, with a regression test,
   in their own commit.

## Proof redesign (prototype on `bv_add`, `bv_sub`, `bv_mul`, `bv_div`)

The first proofs spent most of their length on plumbing: inverting the rule's
`match`, typing, casts between `Int` widths and `BitVec`, and re-proving each
`[@comm]` alternative. Functions marked `[@cases]` are proved differently:

- Literals: `BitVec l` binds `l : bv`, a bit-vector value that knows its width.
  `+ - *` on `bv` are modular (primitives `lit_add`, ...), `lit l` rebuilds
  the literal term, `to_z` / `of_z` convert explicitly where integer reasoning
  is intended. Helpers with a BitVec meaning (`add_overflows`, `is_int_min`,
  ...) are defined in bvr and bridged once, in Lean, to Lean's `BitVec`
  predicates.
- Statements: one per alternative ("arm") of a rule, over the pattern's
  variables, with the guard as a hypothesis. The statement of the rule itself
  is proved from its arms by a generated proof.
- `[@comm]`: an arm whose pattern only swaps operands of commutative operators
  (or the two arguments of a symmetric spec) is derived from the unswapped arm
  by a generated proof, when its guard and body do not depend on the swap.
  `[@comm]` is rejected on operators that are not commutative.
- Lean library (`Bvr/Lib`): a typed view of bit-vector terms (`evalBV`) that
  turns value goals into `BitVec n` equations; equivalence of terms with
  commutativity and congruence lemmas; lifting of `O` calls to specs; tactics.

Once measured on these four functions, the other areas move to it and the
per-area lemma files are merged into `Bvr/Lib`.
