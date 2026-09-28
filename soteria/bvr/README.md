# bvr: the rule language of Bv_values

The simplifying smart constructors of `Bv_values.Svalue` (`Bool.and_`,
`BitVec.add`, `Float.eq`, ...) are written in bvr, in
`soteria/lib/bv_values/rules/*.bvr`. The `bvr` tool generates from them:

- `svalue_rules.ml`, the OCaml implementation (at build time, by dune), and
- a Lean model with one soundness statement per rule (see `lean/`).

bvr is a small, pure, first-order language with its own typing. Its syntax is
that of OCaml, apart from the declarations and rule names below; it is parsed
by `bvr_parser.mly`.

## Functions

```ocaml
rule bv_not (v : t) : BvNot v <| ty v =
  match v with
  | lit: BitVec bv -> lit (lognot bv)
  | ite: Ite (b, l, r) -> b_ite b (bv_not l) (bv_not r)
  | default: _ -> BvNot v <| ty v

fn size (v : t) : int = size_of_ty (ty v)
```

- Parameters and results are annotated; `(v1 v2 : t)` stands for
  `(v1 : t) (v2 : t)`. Types: `t` (terms), `ty`, `kind`,
  `int` (arbitrary precision, `Z.t`), `bv` (a bit-vector value, which knows
  its width), `bool`, `checked`, `rm`, `fp`, `fc`, `float`, `var`, tuples,
  `option`, `list`.
- `+`, `-`, `*` and unary `-` on `bv`s are modular, at the width of their
  first operand. `lit l` is the literal term of `l`, `to_z signed l` reads
  `l` as an integer, `of_z n z` is `z mod 2^n` (see `prelude.bvr`).
- `rule f params : e = body` declares a *rule function*, which returns a term
  that must refine the raw term `e` (its spec). Every case of its top-level
  `match` is a rule, named by the label before its pattern (`lit:`).
- `fn f params : ty = body` declares a helper. All functions can call each
  other.
- `prim f : a -> b` declares a primitive, implemented by hand in `svalue.ml`
  and in `lean/Bvr/Prims.lean`; `oracle f : a -> b` declares one that the Lean
  model takes as a parameter (Floatml's arithmetic).

## Rules

Rule functions are proved per alternative of their rules:

- `#l` (or `BitVec l`) binds `l : bv`, the value of the literal.
- Each alternative of a rule (after expanding or-patterns and swaps) has
  its own statement, over the variables of its pattern and with its guard as
  a hypothesis: `f.r_name.aI.Stmt`. The statement of the rule is proved from
  them by generated code.
- An alternative that only swaps operands of commutative operators (or the two
  arguments of the function) is proved from the unswapped one by generated
  code, if its guard and body do not depend on the swap.
- It may only match on its parameters, with no `let` before the match, and
  its pattern variables may not shadow the parameters it does not match on.

- A rule may match on the operands of its spec, when the spec is an operator
  on terms: in `rule bv_sub (checked : checked) (v1 v2 : t) : Sub (checked,
  v1, v2) <| ty v1`, `match v1 - v2 with | sub_sub: l - (l - r) -> r` stands
  for `match v1, v2 with | sub_sub: l, (l - r) -> r`. When the operator is
  commutative, the operands match in either order (unless the pattern is
  symmetric), so the cases must name them rather than use `v1` and `v2`
  (other than in `ty v1` and `size v1`).

## Terms

- `k <| ty` builds a raw node, without simplification.
- Operators are node constructors: `Add (c, a, b)` is `Binop (Add c, a, b)`,
  `Not p` is `Unop (Not, p)`, `BvExtract (i, j, v)` is
  `Unop (BvExtract (i, j), v)`, `Ite (b, t, e)`, `Distinct l`, ... The long
  forms remain available.
- Patterns match the kind of a term directly: `BitVec z`, `Add (c, l, r)`.

### Operators on terms

On terms, the operators below build (in expressions) or match (in patterns)
their node; in expressions they call its smart constructor, unchecked, and in
patterns they match any overflow check (use `Add (c, a, b)` to bind it).

| operator | node | smart constructor |
|---|---|---|
| `a + b`, `a - b`, `a * b` | `Add`, `Sub`, `Mul` | `bv_add unchecked`, ... |
| `-a`, `~a` | `Neg`, `BvNot` | `bv_neg false`, `bv_not` |
| `a land b`, `a lor b`, `a lxor b` | `BitAnd`, `BitOr`, `BitXor` | `bv_and`, ... |
| `a lsl b`, `a lsr b`, `a asr b` | `Shl`, `LShr`, `AShr` | `bv_shl`, ... |
| `a ++ b` | `BvConcat` | `bv_concat` |
| `a && b`, `a \|\| b`, `not a` | `And`, `Or`, `Not` | `b_and`, `b_or`, `b_not` |
| `a == b` | `Eq` | `sem_eq` |

On `bv`s, `+`, `-`, `*`, unary `-`, `land`, `lor`, `lxor`, `lsl`, `lsr`, `asr`
and `~` are the modular operations (`lit_add`, ...), and a `bv` where a term is
expected stands for its literal: `| lits: #l, #r -> l + r`.

## Patterns

- `0`, `1`, ... match bit-vector literals, `#_` any of them, and `#x` binds
  one (to its value in rules, to its unsigned integer in helpers); `true` and
  `false` match boolean literals.
- A repeated variable matches equal terms: `| p, not p -> v_false`.
- The operands of commutative operators (`+`, `*`, `land`, `lor`, `lxor`,
  `&&`, `||`, `==`, and `FEq`, `AddOvf`, `MulOvf`) match in either order:
  `x + #k` also matches `#k + x`. The swap is left out when both operands are
  wildcards or variables bound nowhere else, as it matches the same terms.
- `p [@comm]` also matches the components of the pair `p` swapped (the
  arguments of the rule function): `(1, ~v) [@comm]` matches both `1, ~v` and
  `~v, 1`.
- Or-patterns, `as`, `when` guards, `Some`/`None`, lists and partial records
  (`{ unsigned = true; _ }`) are supported. Each alternative of an or-pattern
  is tried in turn, together with the guard.
