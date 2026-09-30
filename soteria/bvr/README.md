# bvr: the rule language of Bv_values

The simplifying smart constructors of `Bv_values.Svalue` (`Bool.and_`,
`BitVec.add`, `Float.eq`, ...) are written in bvr, in
`soteria/lib/bv_values/rules/*.bvr`. The `bvr` tool generates their OCaml
implementation from them, `svalue_rules.gen.ml`: dune regenerates it and
promotes it to the source tree, where it is committed, and
`[%%include_file "svalue_rules.gen.ml"]` (a ppx, in `ppx/`) includes it in
`Svalue.Make`, so that it is compiled along with the primitives it uses.

It also generates a Lean model of the rules, with one soundness statement per
rule, which are proved in `lean/` (see [Proofs](#proofs)).

The smart constructors of `Tiny_values.Svalue` are generated in the same way,
from `soteria/lib/tiny_values/rules/*.bvr`, into a plain module with its own
primitives; they have no Lean model yet.

bvr is a small, pure, first-order language with its own typing. Its syntax is
that of OCaml, apart from the declarations and rule names below; it is parsed
by `bvr_parser.mly`.

## The language

bvr does not hard-code the language of Bv_values: the types of its terms,
their constructors and the operators on them are declared in `.bvl` files,
`soteria/lib/bv_values/rules/lang.bvl` and the declarations of its modules
(see [Modules](#modules)), which `bvr` reads before the rules
(`bvr BACKEND lang.bvl bool.bvl ... bool.bvr ...`: the `.bvl`
files, then the `.bvr` files, each in order). Attributes mark the literals, the
commutative operators and the kind constructors that operators stand for, and
declare the laws of operators (see [Laws](#laws)); `infix` and `prefix` declare
what the operators on terms build and match (see
[Operators on terms](#operators-on-terms)).

Names flow from bvr to Lean: bvr generates the Lean definitions of the
declared types (`Types.lean` and `Syntax.lean`),
with the same constructor names, and with type names CamelCased (`ext_ty` is
`ExtTy`). The abstract types, declared without a definition, are defined by
hand in `Abstract.lean`. In OCaml, the types are those of `Svalue_ast`, which
bvr does not generate: `[@ocaml "..."]` gives the OCaml type when it is not
the bvr one. `bvr ocaml-check` generates `lang_check.gen.ml`, included next to
`svalue_rules.gen.ml`, which fails to compile unless the OCaml types have
exactly the declared constructors and record fields, with the declared
arguments.

The typing of the operators is declared with their constructors, as sorts
(`BvExtract of nat * nat (i, j) : TBitVector n -> TBitVector (j - i + 1) when
0 <= i && i <= j && j < n`), from which bvr generates the Lean typing
predicates (`Typing.lean`).

`t` (terms), `bv` and `var` are built into bvr, as are `int`, `bool` and
`unit`; `type`, `of`, `infix`, `prefix`, `node`, `extend` and `before` are
keywords.

## Modules

A language is made of modules, each with its declarations (`bool.bvl`) and
its rules, primitives and helpers (`bool.bvr`): Bv_values of `bool`, `exists`,
`bitvec`, `float` and `ptr`. The modules that several languages share are in
`modules/`. The language itself (`lang.bvl`) only declares its types, as its
OCaml AST has them, and implements the primitives of its modules.

- `node C ...`, in a module, declares the constructor `C` as a type would
  (`node And : TBool -> TBool -> TBool [@comm] [@idem]`), and the language
  places it in one of its types, where it names it alone (`| And` in
  `binop`). The module declares what the node is (its arguments, typing,
  laws and operators), and the language where its AST has it.
- `extend rule f = | r: p -> e ...`, in the rules of a module, adds rules to
  the rule function `f` of a module below it, as if they were written in `f`:
  last, but before its final catch-all case `_`, or with `extend rule f before
  r`, before its rule `r`. The rules of `bool` on bit-vectors are in
  `bitvec.bvr`, for instance. A function's rules are tried in order, so this
  keeps the order of the rules independent of the modules they are written
  in.
- `extend fn f = | p -> e ...` adds cases to the helper `f` in the same way,
  e.g. the literals of each module to `sure_neq`. The cases go into the match
  that ends `f`, behind `let`s and the right operands of `||` and `&&`.
- A node placed in `kind` itself, rather than in a type of operators, has its
  operands as arguments (`Ite of t * t * t`) and no typing.

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
  `l` as an integer, `of_z n z` is `z mod 2^n` (see `bitvec.bvr`).
- `rule f params : e = body` declares a *rule function*, which returns a term
  that must refine the raw term `e` (its spec). Every case of its top-level
  `match` is a rule, named by the label before its pattern (`lit:`).
- `fn f params : ty = body` declares a helper. All functions can call each
  other.
- `prim f : a -> b` declares a primitive, implemented by hand in
  `Svalue.Make.Prims` and in `lean/Bvr/Prims.lean` (the generated
  `svalue_rules.gen.ml` and `Signatures.lean` check that both define it, at
  this type); `oracle f : a -> b`
  declares one that the Lean model takes as a parameter, so that the proofs
  may not rely on its behaviour (Floatml's arithmetic, the hash-consing order).

## Rules

- `#l` (or `BitVec l`) binds `l : bv`, the value of the literal.
- A rule may only match on the parameters of its function, with no `let`
  before the match, and its pattern variables may not shadow the parameters
  it does not match on.
- When the spec of a rule is a commutative node over `v1, v2` (e.g.
  `And (v1, v2)`, `AddOvf (signed, v1, v2)`), the cases of `match v1, v2 with`
  match them in either order, unless the pattern is symmetric (the same once
  swapped, up to renaming), so `| true_: true, x -> x` covers both
  `true && x` and `x && true`. The cases must then name the operands rather
  than use `v1` and `v2` (other than in `ty v1` and `size v1`).
- A rule may match on the operands of its spec, when the spec is an operator
  on terms: in `rule bv_sub (checked : checked) (v1 v2 : t) : Sub (checked,
  v1, v2) <| ty v1`, `match v1 - v2 with | sub_sub: l - (l - r) -> r` stands
  for `match v1, v2 with | sub_sub: l, (l - r) -> r`.

## Laws

Attributes on an operator in its declaration declare its algebraic laws, from which
bvr derives the first rules of its *rule function* (the rule function whose
spec is the operator over the function's parameters, e.g. `bv_mul` for
`Mul (checked, v1, v2)`), in this order, before the rules written by hand. The
derived rules are ordinary rules: they are generated and proved like the others,
and a hand-written rule may not reuse their names.

| law | derived rule, in `bv_add (checked) (v1 v2)`, `bv_sub`, `bv_neg`, ... |
|---|---|
| `[@fold "f"]` | `lits: #l + #r -> f l r`, `lit: #bv -> f bv` |
| `[@unit "c"]` | `zero: x + 0 -> x` (commutative), `zero: _ lsl 0 -> v1` (otherwise) |
| `[@zero "c"]` | `zero: _ * 0 -> bv_zero (size v1)`, `false_: _ && false -> v_false` |
| `[@idem]` | `same: v && v -> v` |
| `[@invol]` | `neg: -x -> x`, named after the operator (unary operators) |
| `[@distrib_ite]` | `ite: Ite (b, l, r) -> b_ite b (bv_neg checked l) (bv_neg checked r)` (unary operators) |

- `[@fold "f"]`: `f` takes the last parameters of the node that it has room
  for (`lit_extract from_ to_ bv`, `add_overflows signed l r`), then the
  literals, of the types of its arguments: bit-vector literals are bound to `l`
  and `r` (`bv` for one operand), the others to the first letter of their type
  (`Float f1`, `Float f2`, `Float f`). A `bool` result is lifted with `of_bool`,
  and a result of another type `T` with its literal constructor, `C (f ...) <|
  s`, where `s` is the sort of the spec (`Float (f_add f1 f2) <| ty v1`).
- `[@unit "c"]` and `[@zero "c"]` take the literal `0`, `1`, `true` or `false`,
  which names the rule (`zero`, `one`, `true_`, `false_`). On an operator that
  does not commute, `c` is on the right; on one that does, the rule matches it
  on either side.
- `[@distrib_ite]` rebuilds the branches with the rule function itself, and
  the `Ite` with the rule function of `Ite`.

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
  `false` match boolean literals. When the literals are integers
  (`[@literal "int"]`), `#x` binds its integer in rules too.
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

## Proofs

`lean/` is a Lean project. `bvr lean-all` generates its generated files, which
`dune test` checks to be up to date (run `dune promote` after changing the
rules):

- `Types.lean` and `Syntax.lean` define the types of the language, around
  `Abstract.lean` (written by hand), and which operators commute
  (`Binop.Comm`, from `[@comm]`; `Lib/Cases.lean` proves that they do), and
  `Typing.lean` the typing of the operators.
- `Model.lean` is a Lean model of the rule functions, over the primitives of
  `Prims.lean`, and `Semantics.lean` gives terms their meaning (written by
  hand).
- `Statements.lean` states that every alternative of every rule is sound: its
  result *refines* its spec (the raw term it simplifies): it has the same
  sort, and the same value wherever the raw term has one.
- `Soundness.lean` proves each rule from its alternatives, and every function
  from its rules, up to `Bvr.opsN_sound`: the whole simplifier is sound.

An alternative (an arm) is one case of a rule, after expanding its or-patterns
and the swaps of commutative operands; its statement is over the variables of
its pattern, with its guard as a hypothesis (`f.r_name.arm.Stmt`). An arm is
named after the choices that produced it, so that reordering patterns does not
rename it: the head constructor (or operator) of each or-pattern branch taken,
with an index when both branches have the same head (`lt_leq`, `lt1`), and
`swap` for a swap (numbered when there are several), prefixed by `cN` when the
rule has several cases; an arm with no choice is `main`.

Its proof is the theorem tagged `@[bvr_arm]` that proves `f.r_name.arm.Stmt`
in `lean/Bvr/Proofs/`, if there is one; otherwise the tactic given to its
function by `attribute [bvr_tactic tac] f.spec`, in the library that defines
`tac` (`lean/Bvr/Lib/`); otherwise `bvr_auto`. `bvr_arm` rejects a theorem that
proves no arm, or an arm that already has a proof. An alternative that only
swaps commutative operands is proved from the unswapped one, if its guard and
body do not depend on the swap.

`lake build` checks every proof, and CI checks that the soundness theorem
depends on no `sorry` (`check_axioms.lean`).

## Tests

`bvr ocaml-tests` generates, for every rule function, its spec, a call to it
and the name of the rule that fires, from random arguments. The test in
`soteria/tests/bv_rules/`, which runs with `dune test`, draws small well-typed
arguments, and checks with `Eval` that the result of each rule function refines
its spec under random assignments of the variables. `BVR_RULE_STATS=1` prints
how often each rule fired.
