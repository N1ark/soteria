# The bvr language

This is the reference of the language in which the simplifications of
`Bv_values` are written (`soteria/lib/bv_values/rules/*.bvr`). See
[README.md](README.md) for what bvr is and how it fits in Soteria.

bvr looks like a small subset of OCaml, with a few additions for writing
rewrite rules on terms. It is pure (no mutation, no exceptions other than
`assert`), first-order (functions are not values), and every function is
annotated with its type. Anything that the tool does not understand is
rejected with an error pointing at the offending code.

- [A first example](#a-first-example)
- [Files and declarations](#files-and-declarations)
- [Types](#types)
- [Expressions](#expressions)
- [Terms](#terms)
- [Patterns](#patterns)
- [Rule functions](#rule-functions)
- [Commutative operators](#commutative-operators)
- [Restrictions](#restrictions)

## A first example

```ocaml
rule bv_not (v : t) : BvNot v <| ty v =
  match v with
  | lit: #bv -> ~bv
  | ite: Ite (b, l, r) -> b_ite b (~l) (~r)
```

This defines `bv_not`, the smart constructor of bitwise negation. It takes a
term `v` and returns a term that means the same as the raw node `BvNot v` of
type `ty v` (the part after the `:`, called the *spec* of the rule). It has
two rules, one per case of the `match`:

- `lit`: if `v` is a bit-vector literal, whose value is bound to `bv`, the
  result is the literal of `~bv`, the value with all bits flipped;
- `ite`: the negation of `ite(b, l, r)` is `ite(b, ~l, ~r)`, where `~l` and
  `~r` are simplified in turn, and so is the `ite`.

The cases are tried in order, and the first one that matches gives the
result. If none matches, the result is the spec itself: the raw node
`BvNot v`, unsimplified. Each rule is proved sound on its own, so the order only decides which
simplification applies, never whether the result is correct.

## Files and declarations

A `.bvr` file is a list of declarations. The files are processed together,
in the order given to the tool (`prelude.bvr` first): every declaration can
use every other one, whatever the file or order they are in, and functions
can be (mutually) recursive.

Comments are written `(* ... *)`, and can be nested.

There are four kinds of declarations.

### `prim`: primitives

```ocaml
prim size_of_ty : ty -> int
prim v_true : t
```

A primitive is implemented by hand twice: in OCaml, in the `Prims` module of
`soteria/lib/bv_values/svalue.ml`, and in Lean, in `lean/Bvr/Prims.lean`. The
two implementations must agree (this is trusted, see
[README.md](README.md#what-is-proved-and-what-is-trusted)). Primitives are
declared in `prelude.bvr`, with a comment saying what they compute.

### `oracle`: primitives the proofs know nothing about

```ocaml
oracle tag_le : t -> t -> bool
oracle f_add : float -> float -> float
```

An oracle is implemented in OCaml only. In Lean, the model of the rules takes
the oracles as parameters, so the proofs hold for *any* implementation of
them, apart from a few assumptions stated in `lean/Bvr/Semantics.lean`
(`Oracle.Compat`). Two things are oracles: the order of hash-consing tags
(which is arbitrary), and float arithmetic on literals (which is done by
Floatml).

### `fn`: helper functions

```ocaml
fn size (v : t) : int = size_of_ty (ty v)

fn zmin (a b : int) : int = if a <= b then a else b

fn unchecked : checked = { signed = false; unsigned = false }
```

`fn name params : type = body` defines a function. Each parameter is written
`(x : type)`, and `(a b : int)` is short for `(a : int) (b : int)`. The result
type is required. A function without parameters is a constant.

### `rule`: rule functions

```ocaml
rule b_not (sv : t) : Not sv <| TBool =
  match sv with
  | true_: true -> v_false
  | ...
```

`rule name params : spec = body` defines a *rule function*: a smart
constructor, which returns a term. The spec is the raw term that the function
simplifies; the result must mean the same thing, and this is what is proved in
Lean. The body is a `match` whose cases are named rules. See
[Rule functions](#rule-functions).

## Types

| type | values |
|---|---|
| `t` | terms (svalues) |
| `ty` | the types of terms: `TBool`, `TBitVector n`, `TFloat fp`, `TLoc n`, `TPointer n`, `TSeq ty`, `TExtension _` |
| `kind` | the kinds of terms, i.e. their top-level node: `BitVec z`, `Binop (op, a, b)`, ... (see [Terms](#terms)) |
| `int` | arbitrary-precision integers (Zarith's `Z.t` in OCaml, `Int` in Lean) |
| `bv` | a bit-vector value: a width and a value of that width |
| `bool`, `unit` | as in OCaml |
| `checked` | overflow checks, the record `{ signed : bool; unsigned : bool }` |
| `float` | a float literal (an IEEE bit pattern and its precision) |
| `var` | a variable identifier |
| `unop`, `binop`, `triop`, `nop` | the operators of the nodes |
| `fp`, `rm`, `fc` | float precisions (`F16`, ...), rounding modes (`NearestTiesToEven`, ...), float classes (`Normal`, `NaN`, ...) |
| `ext`, `ext_ty` | extensions |
| `a * b`, `a option`, `a list` | tuples, options, lists |

Widths and indices in nodes (the `n` of `TBitVector n`, the bounds of
`BvExtract`, ...) are OCaml `int`s, but they have type `int` in bvr like any
integer: the conversions are inserted by the tool.

## Expressions

### Basics

- Variables, integer literals (`0`, `42`), `true`, `false`, `()`.
- Function calls are written `f a b`, as in OCaml. Arguments that are not
  variables or literals need parentheses: `f (g x) (a + 1)`.
- `if c then a else b`; the `else` is required.
- `let x = e in body`, `let (a, b) = e in body`, and `let x : ty = e in body`.
- Local functions: `let f (x : int) : int = x + 1 in body`. They cannot be
  recursive.
- `match e with | p1 -> e1 | p2 when guard -> e2 | ...`, and
  `match a, b with | p, q -> ...` to match on several values. See
  [Patterns](#patterns).
- Tuples `(a, b)`, lists `[a; b]` and `x :: l`, options `Some x` and `None`.
- Records of type `checked`: `{ signed = true; unsigned = false }` (both
  fields are required), and the fields `c.signed`, `c.unsigned`.
- `(e : ty)` annotates `e` with its type, e.g. for a `None` or `[]` whose
  type cannot be guessed.
- `assert c; e` checks `c` before evaluating `e`. It raises in OCaml if `c` is
  false; the Lean model ignores it, so the proofs do not rely on it.

### Operators

The meaning of an operator depends on the type of its operands.

| operators | on `int`s | on `bv`s | on terms (`t`) |
|---|---|---|---|
| `+`, `-`, `*`, unary `-` | arithmetic | modular arithmetic | the smart constructor, unchecked (see below) |
| `land`, `lor`, `lxor`, `~` | bitwise, two's complement | bitwise | the smart constructor |
| `lsl`, `asr` | shifts | shifts | the smart constructor |
| `lsr` | (not defined) | logical shift | the smart constructor |
| `<`, `<=`, `>`, `>=` | comparisons | (not defined) | (not defined) |

- `&&`, `||` and `not` are the boolean operators on `bool`s, and the smart
  constructors of `And`, `Or` and `Not` on terms. `==` and `++` are only
  defined on terms.
- `=` and `<>` are structural equality, on `int`, `bv`, `bool`, `unit`, `ty`,
  the operators, and tuples and options of those. Terms are compared with
  `equal a b`, and floats with `f_equal` or `f_bits_equal`.
- On `bv`s, the operations are done at the width of their first operand, and
  wrap around (e.g. `lit_add` in `prelude.bvr`). A `bv` used where a term is
  expected stands for its literal: in `| lits: #l, #r -> l + r`, `l + r` is
  the literal of the sum.
- On terms, the operators call the smart constructor of their node, so their
  result is simplified in turn. The arithmetic ones are unchecked (they carry
  no promise of not overflowing): `a + b` is `bv_add unchecked a b`, and
  `-a` is `bv_neg false a`. To build a checked operation, call the smart
  constructor: `bv_add checked_unsigned a b`.

| operator on terms | smart constructor |
|---|---|
| `a + b`, `a - b`, `a * b`, `-a` | `bv_add unchecked`, `bv_sub unchecked`, `bv_mul unchecked`, `bv_neg false` |
| `a land b`, `a lor b`, `a lxor b`, `~a` | `bv_and`, `bv_or`, `bv_xor`, `bv_not` |
| `a lsl b`, `a lsr b`, `a asr b` | `bv_shl`, `bv_lshr`, `bv_ashr` |
| `a ++ b` | `bv_concat` |
| `a && b`, `a \|\| b`, `not a` | `b_and`, `b_or`, `b_not` |
| `a == b` | `sem_eq` |

Precedence is as in OCaml: `lsl`, `lsr` and `asr` bind tighter than `*`,
`land`, `lor` and `lxor`, which bind tighter than `+`, `-` and `++`, then
`::`, then the comparisons and `==`, then `&&`, then `||`.

## Terms

A term has a *kind* (its top-level node) and a *type*. The kinds are:

| kind | meaning |
|---|---|
| `Var v` | a symbolic variable |
| `Bool b`, `BitVec z`, `Float f` | literals |
| `Ptr (loc, ofs)` | a pointer |
| `Seq l` | a sequence |
| `Unop (op, a)`, `Binop (op, a, b)`, `Triop (op, a, b, c)`, `Nop (op, l)` | operations |
| `Exists (binders, body)` | a quantifier |
| `Extension e` | an extension |

The operators are those of `soteria/lib/bv_values/svalue_ast.ml` (and
`bvr/syntax.ml`): for example `Add checked`, `Lt signed`, `BvExtract (from_,
to_)`, `Ite`, `Distinct`. An operator can be used as a node directly:
`Add (c, a, b)` stands for `Binop (Add c, a, b)`, `Not p` for `Unop (Not, p)`,
`BvExtract (i, j, v)` for `Unop (BvExtract (i, j), v)`, and `Ite (b, t, e)`
for `Triop (Ite, b, t, e)`. The long forms can be used too.

### Building terms

There are two ways of building a term:

- **Through a smart constructor**, which simplifies it: `bv_add c a b`,
  `b_ite b l r`, or an operator on terms, such as `a + b`. This is how rules
  should build their results.
- **As a raw node**, without simplification: `kind <| ty`, e.g.
  `BvNot v <| ty v` or `Add (c, a, b) <| TBitVector (size a)`. This is how
  specs are written.

Literals are built by primitives: `lit l` (the literal of a `bv`),
`mk_bv n z`, `bv_zero n`, `bv_one n`, `v_true`, `v_false`, `of_bool b`.

## Patterns

Patterns are those of OCaml: `_`, variables, literals, tuples, constructors,
`p as x`, or-patterns `p | q`, `when` guards, `Some`/`None`, lists
(`[]`, `[p]`, `p :: q`), `()`, and records of type `checked`, closed
(`{ signed = s; unsigned = u }`) or partial (`{ unsigned = true; _ }`).

On terms, patterns match the kind of the term directly:

| pattern | matches |
|---|---|
| `Ite (b, l, r)`, `Ptr (l, o)`, `Float f`, ... | a term of that kind |
| `Add (c, a, b)` | an addition, binding its overflow checks to `c` |
| `a + b`, `a - b`, `a * b`, `-a` | the same node, with any overflow checks |
| `a land b`, `a lor b`, `a lxor b`, `~a`, `a lsl b`, `a lsr b`, `a asr b`, `a ++ b` | the node of the operator |
| `a && b`, `a \|\| b`, `not a`, `a == b` | `And`, `Or`, `Not`, `Eq` nodes |
| `0`, `1`, ... | the bit-vector literal of that (unsigned) value, of any width |
| `true`, `false` | the boolean literals |
| `#_` | any bit-vector literal |
| `#x` | a bit-vector literal, bound to `x` |
| `Add _` | any addition: `_` stands for all the arguments |

- `#x` (or `BitVec x`) binds `x` to the *value* of the literal. In rule
  functions, this is a `bv` (its width and its value). In helpers, it is the
  value as an unsigned `int`. To also bind the literal term, use `as`:
  `(#bv_l as l) + y` binds the value to `bv_l` and the term to `l`.
- A variable repeated in a pattern matches equal values: `| p, not p -> ...`
  matches `p` and the negation of that same `p`. On terms this is physical
  (hash-consing) equality, i.e. the two are the same term.
- Integer fields of nodes (widths and indices, like the bounds of
  `BvExtract`) can only be matched by variables, `_` or integer literals.
- Each alternative of an or-pattern is tried in turn, together with the
  guard: if the guard fails on the first alternative, the second one is
  tried.
- The alternatives of an or-pattern must bind the same variables.

## Rule functions

A rule function has the form

```ocaml
rule f (x1 : ty1) ... (xn : tyn) : spec =
  match x1, ..., xk with
  | name1: pattern1 -> result1
  | name2: pattern2 when guard -> result2
  ...
```

- **The spec** is the raw term that the function simplifies, written with
  `<|` (it can call helpers, such as `size`). The function must return a term
  that *refines* the spec: it has the same type, and it has the same value
  whenever the spec has one. See [README.md](README.md#soundness-refinement)
  for what this means precisely.
- **The body** is a `match` on some of the parameters (any subset, in any
  order), optionally preceded by `assert c;`.
- **Every case is named**, by a label before its pattern (`lit:`). The label
  is the name of the rule, and appears in the names of its Lean statements
  and in the error messages of the proofs. Consecutive cases with the same
  name form a single rule. Any lowercase name can be used, as well as `not`.
- **When no case matches, the result is the spec**: the raw node, which
  needs no proof. A last case that always matches is only needed when the
  fallback is not the spec itself, for example to put the operands of a
  commutative node in a normal order (`b_and` ends with
  `| default: _ -> mk_commut_binop And v1 v2 <| TBool`).
- The result of a case can use anything: helpers, other rule functions
  (including the function itself, recursively), `let`, `if`, a nested
  `match`, etc.

### Matching on the operands of the spec

When the spec is an operator on terms, a rule can match on that operator:

```ocaml
rule bv_sub (checked : checked) (v1 v2 : t) : Sub (checked, v1, v2) <| ty v1 =
  match v1 - v2 with
  | sub_sub: l - (l - r) -> r
  ...
```

`match v1 - v2 with | l - (l - r) -> ...` stands for
`match v1, v2 with | l, (l - r) -> ...`: every case must then have the form
`p - q` (or `_`).

## Commutative operators

The operands of commutative operators are matched in either order, so that
rules do not need to be written twice. The commutative operators are `+`,
`*`, `land`, `lor`, `lxor`, `&&`, `||`, `==`, and the nodes `FEq`, `AddOvf`
and `MulOvf`.

- **In patterns**, `x + #k` also matches `#k + x`. The swapped version is left
  out when it would match the same terms: when both operands are `_` or
  variables used nowhere else in the pattern.
- **In rules whose spec is commutative**, such as `And (v1, v2)`, the cases
  of `match v1, v2 with` (or `match v1 && v2 with`) match the two operands in
  either order, unless the pattern is symmetric (the same once swapped, up to
  renaming the variables). For example, in `b_and`,
  `| true_: true && x -> x` covers both `true && x` and `x && true`.
  In these cases, the result and the guard must refer to the operands by the
  names given in the pattern, not as `v1` and `v2`, which would be the wrong
  ones in the swapped version (`ty v1` and `size v1` are allowed, since both
  operands have the same type).
- **`p [@comm]`** matches a pair in either order: `(1, ~v) [@comm]` matches
  both `1, ~v` and `~v, 1`. It also applies to binary operators, e.g.
  `Sub (c, #_, _) [@comm]`, but in rule functions only to commutative ones.

In the proofs, a swapped alternative is usually proved from the unswapped one
automatically.

## Restrictions

The tool rejects programs that it could not translate faithfully to OCaml and
Lean. The main restrictions are:

- Rule functions `match` directly on their parameters, with no `let` before
  the `match` (but `assert` is allowed).
- In a rule function, pattern variables cannot have the name of a parameter
  that the `match` does not match on.
- No variable (parameter, pattern variable, `let`) can have the name of a
  function.
- Every name is defined once, across all files.
- `=` and `<>` are only allowed on types where OCaml's structural equality is
  meaningful (not on terms, where `equal` is used, nor on floats, where
  `f_equal` and `f_bits_equal` are used).
- A literal bound with `#x` cannot be repeated in a pattern.
- There are no labelled arguments, higher-order functions, or user-defined
  types.
