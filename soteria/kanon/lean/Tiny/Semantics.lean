import Tiny.Model
import Tiny.Typing

/-!
# Semantics of Tiny_values, and soundness of simplifications

`eval ρ t` is the value of the term `t` under the environment `ρ`, a boolean or
a mathematical integer, following the SMT-LIB encoding of
`soteria/lib/tiny_values/encoding.ml` (which is what path conditions mean),
with `none` standing for *poison*:

- ill-typed terms (see `Term.WT`) are poison, and so are variables that the
  environment does not give a value of their type;
- `div` and `mod` are SMT-LIB's, Euclidean (Lean's `/` and `%` on `Int`):
  `0 ≤ a mod b < |b|` and `a = b * (a div b) + a mod b`;
- `rem` is Z3's (it is not in SMT-LIB): `a mod b`, negated when `b < 0`, so it
  has the sign of `b` (unlike OCaml's `Z.rem`, which has the sign of `a`);
- division, `mod` and `rem` by zero are undefined behaviour, which is poison
  here: `Typed.div`, `Typed.rem` and `Typed.mod_` take a non-zero divisor, which
  the interpreters check before dividing (e.g. `check_nonzero` in
  soteria-linear), so the rules may assume that the divisor is not zero (e.g.
  `leq.const_mod`, `0 ≤ x mod y`, or `rem.mul`);
- `=` compares values (booleans or integers) and `distinct` holds when its
  operands (all of the same type) are pairwise different values; both are
  poison when one of their operands is;
- `ite` only evaluates the branch it selects, and `&&` / `||` are "parallel":
  a `false` (resp. `true`) operand wins over a poisoned one, as it would over
  any value of the unspecified one;
- the other operators are strict: poison when one of their operands is.

The evaluator `soteria/lib/tiny_values/eval.ml` evaluates terms with the smart
constructors, on literals, so its arithmetic is that of the rules on literals
(`lits`), which compute with `Z.ediv` and `Z.erem` to agree with the encoding.
It returns `None` on any division by zero, even in an operand of `&&` or `||`
whose other operand is `false` (resp. `true`), where this semantics gives a
value.

A smart constructor is sound when its result *refines* the raw node it
simplifies (`Refines`): the result is well-typed, of the same type, and
whenever the raw node evaluates to a value, the result evaluates to the same
value. `Oracle.Compat` states what the proofs assume of the oracles: that
sorting by tags permutes a list (the hash-consing order `tag_le` is arbitrary).
-/

noncomputable section

namespace Tiny

open Classical Kanon

/-! ## Values -/

inductive Val where
  | bool (b : Bool)
  | int (z : Int)
  deriving DecidableEq

/-- The type of a value. -/
def Val.ty : Val → Ty
  | .bool _ => .TBool
  | .int _ => .TInt

/-- An environment: the values of the variables. -/
abbrev Env := Int → Option Val

/-! ## Well-typed terms -/

/-! The typing of the operators, `Unop.WT` and `Binop.WT`, is generated from
`lang.knl` in `Typing.lean`. -/

mutual
/-- Syntactic well-typedness. -/
def Term.WT : Term → Prop
  | .mk (.Var _) _ => True
  | .mk (.Bool _) t => t = .TBool
  | .mk (.Int _) t => t = .TInt
  | .mk (.Unop op a) t => op.WT a.ty t ∧ a.WT
  | .mk (.Binop op a b) t => op.WT a.ty b.ty t ∧ a.WT ∧ b.WT
  | .mk (.Nop _ l) t => t = .TBool ∧ ∃ e, Term.WTList e l
  | .mk (.Ite g a b) t => g.ty = .TBool ∧ a.ty = t ∧ b.ty = t ∧ g.WT ∧ a.WT ∧ b.WT

/-- All the terms are well-typed, of type `e`. -/
def Term.WTList (e : Ty) : List Term → Prop
  | [] => True
  | x :: xs => x.ty = e ∧ x.WT ∧ Term.WTList e xs
end

/-! ## Evaluation -/

/-- Parallel conjunction: `false` wins over poison. -/
def pand : Option Val → Option Val → Option Val
  | some (.bool false), _ => some (.bool false)
  | _, some (.bool false) => some (.bool false)
  | some (.bool true), some (.bool true) => some (.bool true)
  | _, _ => none

/-- Parallel disjunction: `true` wins over poison. -/
def por : Option Val → Option Val → Option Val
  | some (.bool true), _ => some (.bool true)
  | _, some (.bool true) => some (.bool true)
  | some (.bool false), some (.bool false) => some (.bool false)
  | _, _ => none

/-- A binary operation on integers. -/
def intOp (f : Int → Int → Val) : Option Val → Option Val → Option Val
  | some (.int x), some (.int y) => some (f x y)
  | _, _ => none

/-- A division-like operation on integers, poison on a zero divisor. -/
def divOp (f : Int → Int → Int) : Option Val → Option Val → Option Val
  | some (.int x), some (.int y) => if y = 0 then none else some (.int (f x y))
  | _, _ => none

/-- Equality of values. -/
def eqOp : Option Val → Option Val → Option Val
  | some a, some b => some (.bool (decide (a = b)))
  | _, _ => none

/-- Z3's `rem`: `mod`, negated for a negative divisor. -/
def zrem (x y : Int) : Int := if 0 ≤ y then x % y else -(x % y)

def evUnop : Unop → Option Val → Option Val
  | .Not, some (.bool b) => some (.bool !b)
  | _, _ => none

def evBinop : Binop → Option Val → Option Val → Option Val
  | .And, a, b => pand a b
  | .Or, a, b => por a b
  | .Eq, a, b => eqOp a b
  | .Leq, a, b => intOp (fun x y => .bool (decide (x ≤ y))) a b
  | .Lt, a, b => intOp (fun x y => .bool (decide (x < y))) a b
  | .Plus, a, b => intOp (fun x y => .int (x + y)) a b
  | .Minus, a, b => intOp (fun x y => .int (x - y)) a b
  | .Times, a, b => intOp (fun x y => .int (x * y)) a b
  | .Div, a, b => divOp (· / ·) a b
  | .Rem, a, b => divOp zrem a b
  | .Mod, a, b => divOp (· % ·) a b

mutual
/-- Evaluation, assuming well-typedness. -/
def ev (ρ : Env) : Term → Option Val
  | .mk (.Var v) t =>
      match ρ v with
      | some x => if x.ty = t then some x else none
      | none => none
  | .mk (.Bool b) _ => some (.bool b)
  | .mk (.Int z) _ => some (.int z)
  | .mk (.Unop op a) _ => evUnop op (ev ρ a)
  | .mk (.Binop op a b) _ => evBinop op (ev ρ a) (ev ρ b)
  | .mk (.Nop .Distinct l) _ => (evList ρ l).map (fun vs => .bool (decide vs.Nodup))
  | .mk (.Ite g a b) _ =>
      match ev ρ g with
      | some (.bool true) => ev ρ a
      | some (.bool false) => ev ρ b
      | _ => none

def evList (ρ : Env) : List Term → Option (List Val)
  | [] => some []
  | t :: ts =>
      match ev ρ t, evList ρ ts with
      | some v, some vs => some (v :: vs)
      | _, _ => none
end

/-- The value of a term; `none` for poison. -/
def eval (ρ : Env) (t : Term) : Option Val :=
  if t.WT then ev ρ t else none

/-! ## Refinement -/

/-- `r` refines `spec`: it has the same type, and the same value whenever
`spec` is not poison. -/
def Refines (spec r : Term) : Prop :=
  (spec.WT → r.WT ∧ r.ty = spec.ty) ∧ ∀ ρ v, eval ρ spec = some v → eval ρ r = some v

theorem Refines.refl {t : Term} : Refines t t :=
  ⟨fun h => ⟨h, rfl⟩, fun _ _ h => h⟩

theorem Refines.trans {a b c : Term} (h1 : Refines a b) (h2 : Refines b c) : Refines a c := by
  refine ⟨fun w => ?_, fun ρ v e => h2.2 ρ v (h1.2 ρ v e)⟩
  obtain ⟨wb, sb⟩ := h1.1 w
  obtain ⟨wc, sc⟩ := h2.1 wb
  exact ⟨wc, sc.trans sb⟩

instance : Kanon.Refinement Refines := ⟨Refines.refl, Refines.trans⟩

/-! ## Assumptions on the oracles -/

/-- What the proofs assume of the oracles: that sorting by tags permutes a
list. -/
structure Oracle.Compat (orc : Oracle) : Prop where
  sort_by_tag : ∀ l, (orc.sort_by_tag l).Perm l

end Tiny

end
