# bvr: the rule language of Bv_values

The simplifying smart constructors of `Bv_values.Svalue` (`Bool.and_`,
`BitVec.add`, `Float.eq`, ...) are written in bvr, in
`soteria/lib/bv_values/rules/*.bvr`. The `bvr` tool generates from them:

- `svalue_rules.ml`, the OCaml implementation (at build time, by dune), and
- a Lean model with one soundness statement per rule (see `lean/`).

bvr uses OCaml syntax, so editors and `ocamlformat`-style layouts work, but it
is a small, pure, first-order language with its own typing.

## Functions

```ocaml
let[@spec BvNot v <| ty v] bv_not (v : t) : t =
  match v with
  | BitVec bv [@r lit] -> mk_masked (size v) (lognot bv)
  | Ite (b, l, r) [@r ite] -> b_ite b (bv_not l) (bv_not r)
  | _ [@r default] -> BvNot v <| ty v
```

- Parameters and results are annotated. Types: `t` (terms), `ty`, `kind`,
  `int` (arbitrary precision, `Z.t`), `bv` (a bit-vector value, which knows
  its width), `bool`, `checked`, `rm`, `fp`, `fc`, `float`, `var`, tuples,
  `option`, `list`.
- `+`, `-`, `*` and unary `-` on `bv`s are modular, at the width of their
  first operand. `lit l` is the literal term of `l`, `to_z signed l` reads
  `l` as an integer, `of_z n z` is `z mod 2^n` (see `prelude.bvr`).
- `[@spec e]` makes the function a *rule function*: its result must refine the
  raw term `e`. Every case of its top-level `match` is a rule named with
  `[@r name]`; each rule gets its own Lean proof obligation.
- Functions without a spec are helpers. All functions can call each other.
- `external f : a -> b = ""` declares a primitive, implemented by hand in
  `svalue.ml` and in `lean/Bvr/Prims.lean`; `= "oracle"` declares one that
  the Lean model takes as a parameter (Floatml's arithmetic).

## `[@cases]` functions

A rule function marked `[@cases]` (`let[@spec e] [@cases] f ...`) is proved per
alternative of its rules, rather than per rule:

- `BitVec l` binds `l : bv`, the value of the literal.
- Each alternative of a rule (after expanding or-patterns and `[@comm]`) has
  its own statement, over the variables of its pattern and with its guard as
  a hypothesis: `f.r_name.aI.Stmt`. The statement of the rule is proved from
  them by generated code.
- An alternative that only swaps operands of commutative operators (or the two
  arguments of the function) is proved from the unswapped one by generated
  code, if its guard and body do not depend on the swap. `[@comm]` is only
  allowed on commutative operators there.
- It may only match on its parameters, with no `let` before the match, and
  its pattern variables may not shadow the parameters it does not match on.

## Terms

- `k <| ty` builds a raw node, without simplification.
- Operators are node constructors: `Add (c, a, b)` is `Binop (Add c, a, b)`,
  `Not p` is `Unop (Not, p)`, `BvExtract (i, j, v)` is
  `Unop (BvExtract (i, j), v)`, `Ite (b, t, e)`, `Distinct l`, ... The long
  forms remain available.
- Patterns match the kind of a term directly: `BitVec z`, `Add (c, l, r)`.

## Patterns

- `0`, `1`, ... match bit-vector literals; `true` and `false` match boolean
  literals.
- A repeated variable matches equal terms: `| p, Not p -> v_false`.
- `p [@comm]` also matches the operands of the binary operator `p`, or the
  components of the pair `p`, swapped: `(1, BvNot v) [@comm]` matches both
  `1, ~v` and `~v, 1`.
- Or-patterns, `as`, `when` guards, `Some`/`None`, lists and partial records
  (`{ unsigned = true; _ }`) are supported. Each alternative of an or-pattern
  is tried in turn, together with the guard.
