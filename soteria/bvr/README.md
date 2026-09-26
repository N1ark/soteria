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
  `int` (arbitrary precision, `Z.t`), `bool`, `checked`, `rm`, `fp`, `fc`,
  `float`, `var`, tuples, `option`, `list`.
- `[@spec e]` makes the function a *rule function*: its result must refine the
  raw term `e`. Every case of its top-level `match` is a rule named with
  `[@r name]`; each rule gets its own Lean proof obligation.
- Functions without a spec are helpers. All functions can call each other.
- `external f : a -> b = ""` declares a primitive, implemented by hand in
  `svalue.ml` and in `lean/Bvr/Prims.lean`; `= "oracle"` declares one that
  the Lean model takes as a parameter (Floatml's arithmetic).

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
