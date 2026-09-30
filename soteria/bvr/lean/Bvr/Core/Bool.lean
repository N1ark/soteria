import Lean
import Bvr.Core.Lang

/-!
# The Bool module (trial)

The operators of booleans, the laws that a language including them satisfies
(`HasBool`), and the pure boolean rules of `b_and`, `b_or` and `b_not`, proved
once for every such language by one tactic (`bool_rule`).
-/

namespace Bvr.Core

inductive BoolOp where
  | tt | ff | not | and | or
  deriving DecidableEq

def pnot : Option Bool → Option Bool := Option.map (!·)

/-- Non-strict conjunction: false as soon as one operand is. -/
def pand : Option Bool → Option Bool → Option Bool
  | some false, _ | _, some false => some false
  | some true, some true => some true
  | _, _ => none

/-- Non-strict disjunction: true as soon as one operand is. -/
def por : Option Bool → Option Bool → Option Bool
  | some true, _ | _, some true => some true
  | some false, some false => some false
  | _, _ => none

class HasBool (L : Lang) where
  op : BoolOp → L.Op
  view : L.Op → Option BoolOp
  view_op : ∀ o, view (op o) = some o
  op_of_view : ∀ {o b}, view o = some b → o = op b
  tBool : L.Ty
  ofBool : Bool → L.Val
  toBool : L.Val → Option Bool
  toBool_ofBool : ∀ b, toBool (ofBool b) = some b
  ofBool_of_toBool : ∀ {v b}, toBool v = some b → ofBool b = v
  wt_tt : ∀ {as t}, L.wt (op .tt) as t ↔ as = [] ∧ t = tBool
  wt_ff : ∀ {as t}, L.wt (op .ff) as t ↔ as = [] ∧ t = tBool
  wt_not : ∀ {as t}, L.wt (op .not) as t ↔ as = [tBool] ∧ t = tBool
  wt_and : ∀ {as t}, L.wt (op .and) as t ↔ as = [tBool, tBool] ∧ t = tBool
  wt_or : ∀ {as t}, L.wt (op .or) as t ↔ as = [tBool, tBool] ∧ t = tBool
  den_tt : L.den (op .tt) [] = some (ofBool true)
  den_ff : L.den (op .ff) [] = some (ofBool false)
  den_not : ∀ v, L.den (op .not) [v] = (pnot (v.bind toBool)).map ofBool
  den_and : ∀ v w, L.den (op .and) [v, w] = (pand (v.bind toBool) (w.bind toBool)).map ofBool
  den_or : ∀ v w, L.den (op .or) [v, w] = (por (v.bind toBool) (w.bind toBool)).map ofBool

variable {L : Lang} [HasBool L]

open HasBool

def mkBool (b : Bool) : Term L := .app (op (if b then .tt else .ff)) [] tBool
def mkNot (a : Term L) : Term L := .app (op .not) [a] tBool
def mkAnd (a b : Term L) : Term L := .app (op .and) [a, b] tBool
def mkOr (a b : Term L) : Term L := .app (op .or) [a, b] tBool

/-- The Bool operator at the head of a term, and its operands. -/
def bview : Term L → Option (BoolOp × List (Term L))
  | .app o args _ => (view o).map (·, args)
  | _ => none

theorem bview_some {t : Term L} {b args} (h : bview t = some (b, args)) :
    ∃ ty, t = .app (op b) args ty := by
  cases t with
  | var => simp [bview] at h
  | app o as ty =>
    simp only [bview, Option.map_eq_some_iff, Prod.mk.injEq] at h
    obtain ⟨b', hv, rfl, rfl⟩ := h
    exact ⟨ty, by rw [op_of_view hv]⟩

/-! ## Typing -/

attribute [simp] wt_tt wt_ff wt_not wt_and wt_or

/-! ## Values: terms of booleans are refined through their booleans -/

/-- The boolean that a term stands for, if any. -/
def bval (ρ : Env L) (t : Term L) : Option Bool := (ev ρ t).bind toBool

@[simp] theorem map_ofBool_bind (x : Option Bool) :
    (x.map ofBool).bind (toBool (L := L)) = x := by
  cases x <;> simp [toBool_ofBool]

@[simp] theorem bval_tt {ρ : Env L} {ty} : bval ρ (.app (op .tt) [] ty) = some true := by
  simp [bval, ev, evs, den_tt, toBool_ofBool]
@[simp] theorem bval_ff {ρ : Env L} {ty} : bval ρ (.app (op .ff) [] ty) = some false := by
  simp [bval, ev, evs, den_ff, toBool_ofBool]
@[simp] theorem bval_not {ρ : Env L} {a ty} :
    bval ρ (.app (op .not) [a] ty) = pnot (bval ρ a) := by
  simp only [bval, ev, evs, den_not, map_ofBool_bind]
@[simp] theorem bval_and {ρ : Env L} {a b ty} :
    bval ρ (.app (op .and) [a, b] ty) = pand (bval ρ a) (bval ρ b) := by
  simp only [bval, ev, evs, den_and, map_ofBool_bind]
@[simp] theorem bval_or {ρ : Env L} {a b ty} :
    bval ρ (.app (op .or) [a, b] ty) = por (bval ρ a) (bval ρ b) := by
  simp only [bval, ev, evs, den_or, map_ofBool_bind]

theorem ev_of_bval {t : Term L} {ρ : Env L} {b} (h : bval ρ t = some b) :
    ev ρ t = some (ofBool b) := by
  simp only [bval] at h
  cases e : ev ρ t with
  | none => simp [e] at h
  | some x => simp [e] at h; rw [ofBool_of_toBool h]

/-- The value of a Bool operation is that of its boolean. -/
def IsBoolOp (t : Term L) : Prop := ∀ ρ, ev ρ t = (bval ρ t).map ofBool

theorem isBoolOp_not {a : Term L} : IsBoolOp (mkNot a) := fun _ => by
  simp only [mkNot, bval_not]; simp only [ev, evs, den_not, bval]
theorem isBoolOp_and {a b : Term L} : IsBoolOp (mkAnd a b) := fun _ => by
  simp only [mkAnd, bval_and]; simp only [ev, evs, den_and, bval]
theorem isBoolOp_or {a b : Term L} : IsBoolOp (mkOr a b) := fun _ => by
  simp only [mkOr, bval_or]; simp only [ev, evs, den_or, bval]

/-- Refining a Bool operation, through booleans. -/
theorem Refines.of_bval {spec r : Term L} (hs : IsBoolOp spec)
    (hw : spec.WT → r.WT ∧ r.ty = spec.ty)
    (hb : spec.WT → r.WT → ∀ ρ b, bval ρ spec = some b → bval ρ r = some b) :
    Refines spec r := by
  refine ⟨hw, fun ρ v e => ?_⟩
  by_cases w : spec.WT
  · have wr := (hw w).1
    rw [eval_of_WT w, hs ρ] at e
    rw [eval_of_WT wr]
    cases hx : bval ρ spec with
    | none => simp [hx] at e
    | some b => simp [hx] at e; rw [← e]; exact ev_of_bval (hb w wr ρ b hx)
  · simp [eval, w] at e


/-! ## The rule functions, and the soundness of their rules -/

/-- The smart constructors of the module, which its rules call. -/
structure BoolOps (L : Lang) [HasBool L] where
  b_not : Term L → Term L
  b_and : Term L → Term L → Term L
  b_or : Term L → Term L → Term L

structure BoolOps.Sound (O : BoolOps L) : Prop where
  b_not : ∀ a, Refines (mkNot a) (O.b_not a)
  b_and : ∀ a b, Refines (mkAnd a b) (O.b_and a b)
  b_or : ∀ a b, Refines (mkOr a b) (O.b_or a b)

theorem lift_not {O : BoolOps L} (hO : O.Sound) {a a' : Term L} (h : Refines a a') :
    Refines (mkNot a) (O.b_not a') :=
  Refines.trans (Refines.app (.cons h .nil)) (hO.b_not a')
theorem lift_and {O : BoolOps L} (hO : O.Sound) {a a' b b' : Term L} (ha : Refines a a')
    (hb : Refines b b') : Refines (mkAnd a b) (O.b_and a' b') :=
  Refines.trans (Refines.app (.cons ha (.cons hb .nil))) (hO.b_and a' b')
theorem lift_or {O : BoolOps L} (hO : O.Sound) {a a' b b' : Term L} (ha : Refines a a')
    (hb : Refines b b') : Refines (mkOr a b) (O.b_or a' b') :=
  Refines.trans (Refines.app (.cons ha (.cons hb .nil))) (hO.b_or a' b')

theorem orElse_some {α} {a b : Option α} {r : α} (h : (a <|> b) = some r) :
    a = some r ∨ b = some r := by
  cases a <;> simp_all

section tactics
open Lean Meta Elab Tactic

/-- Replaces a variable known to be headed by a Bool operator by that
operator. -/
elab "bool_view" : tactic => withMainContext do
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    let some (_, lhs, _) := ty.eq? | continue
    unless lhs.isAppOf ``Bvr.Core.bview && lhs.appArg!.isFVar do continue
    let h ← Term.exprToSyntax (mkFVar d.fvarId)
    evalTactic (← `(tactic| (obtain ⟨_, e⟩ := bview_some $h; subst e)))
    return
  throwError "bool_view: no view"

/-- Splits on the boolean of an atom. -/
elab "bool_split" : tactic => withMainContext do
  let isAtom (e : Expr) := !e.hasLooseBVars && e.isAppOfArity ``Bvr.Core.bval 4
  let mut cand := (← instantiateMVars (← getMainTarget)).find? isAtom
  for d in ← getLCtx do
    if cand.isNone && !d.isImplementationDetail then
      cand := (← instantiateMVars d.type).find? isAtom
  let some a := cand | throwError "bool_split: no atom"
  let s ← Term.exprToSyntax a
  evalTactic (← `(tactic| generalize $s = x at *))
  evalTactic (← `(tactic| rcases x with _ | _ | _))

end tactics

/-- The proof of one alternative, `Refines spec r`: lifts the rule functions
of `r` to raw nodes, then compares the booleans of the spec and of the raw
result. -/
macro "bool_arm" hO:ident : tactic => `(tactic| (
  apply Refines.trans
  rotate_left
  focus
    repeat' (first | apply lift_and $hO | apply lift_or $hO | apply lift_not $hO)
    all_goals exact Refines.refl
  refine Refines.of_bval
    (by first | exact isBoolOp_and | exact isBoolOp_or | exact isBoolOp_not) ?_ ?_
  · intro w
    simp only [mkAnd, mkOr, mkNot, mkBool, ite_true, ite_false, Bool.false_eq_true,
      ty_app, WT_app, WTs_cons, WTs_nil, tys_cons, tys_nil, wt_tt, wt_ff, wt_not,
      wt_and, wt_or, List.cons.injEq, and_true] at w ⊢
    try simp_all
  · intro _ _ ρ b hb
    simp only [mkAnd, mkOr, mkNot, mkBool, ite_true, ite_false, Bool.false_eq_true,
      bval_tt, bval_ff, bval_not, bval_and, bval_or] at hb ⊢
    repeat' bool_split
    all_goals simp_all [pand, por, pnot]))

/-- The proof of a rule, from `h : rule args = some r`, the goal being
`Refines spec r`: splits the alternatives of the rule, replaces the views by
the terms they match, and proves each alternative (`bool_arm`). -/
macro "bool_rule" hO:ident h:ident : tactic => `(tactic| (
  repeat' rcases orElse_some $h:ident with $h:ident | $h:ident
  all_goals (repeat' split at $h:ident)
  all_goals (try simp only [reduceCtorEq, Option.some.injEq] at $h:ident)
  all_goals (try contradiction)
  all_goals (repeat bool_view)
  all_goals (try subst_vars)
  all_goals bool_arm $hO))

/-! ### The rules

As bvr generates them: one function per rule, trying its alternatives (the
orders of commutative operands) in turn. -/

variable (O : BoolOps L)

section
open Classical

/-- `v && v -> v` -/
noncomputable def b_and.r_same (v1 v2 : Term L) : Option (Term L) :=
  if v1 = v2 then some v1 else none

/-- `false && _ -> false` -/
def b_and.r_false (v1 v2 : Term L) : Option (Term L) :=
  (match bview v1 with | some (.ff, []) => some (mkBool false) | _ => none)
  <|> (match bview v2 with | some (.ff, []) => some (mkBool false) | _ => none)

/-- `true && x -> x` -/
def b_and.r_true (v1 v2 : Term L) : Option (Term L) :=
  (match bview v1 with | some (.tt, []) => some v2 | _ => none)
  <|> (match bview v2 with | some (.tt, []) => some v1 | _ => none)

/-- `p && not p -> false` -/
noncomputable def b_and.r_not (v1 v2 : Term L) : Option (Term L) :=
  (match bview v2 with
    | some (.not, [p]) => if p = v1 then some (mkBool false) else none | _ => none)
  <|> (match bview v1 with
    | some (.not, [p]) => if p = v2 then some (mkBool false) else none | _ => none)

/-- `(a && _ as x) && a -> x` -/
noncomputable def b_and.r_and (v1 v2 : Term L) : Option (Term L) :=
  (match bview v1 with
    | some (.and, [a, _]) => if a = v2 then some v1 else none | _ => none)
  <|> (match bview v1 with
    | some (.and, [_, a]) => if a = v2 then some v1 else none | _ => none)
  <|> (match bview v2 with
    | some (.and, [a, _]) => if a = v1 then some v2 else none | _ => none)
  <|> (match bview v2 with
    | some (.and, [_, a]) => if a = v1 then some v2 else none | _ => none)

/-- `(a || _) && a -> a` -/
noncomputable def b_and.r_or (v1 v2 : Term L) : Option (Term L) :=
  (match bview v1 with
    | some (.or, [a, _]) => if a = v2 then some v2 else none | _ => none)
  <|> (match bview v1 with
    | some (.or, [_, a]) => if a = v2 then some v2 else none | _ => none)
  <|> (match bview v2 with
    | some (.or, [a, _]) => if a = v1 then some v1 else none | _ => none)
  <|> (match bview v2 with
    | some (.or, [_, a]) => if a = v1 then some v1 else none | _ => none)

/-- `v || v -> v` -/
noncomputable def b_or.r_same (v1 v2 : Term L) : Option (Term L) :=
  if v1 = v2 then some v1 else none

/-- `true || _ -> true` -/
def b_or.r_true (v1 v2 : Term L) : Option (Term L) :=
  (match bview v1 with | some (.tt, []) => some (mkBool true) | _ => none)
  <|> (match bview v2 with | some (.tt, []) => some (mkBool true) | _ => none)

/-- `false || x -> x` -/
def b_or.r_false (v1 v2 : Term L) : Option (Term L) :=
  (match bview v1 with | some (.ff, []) => some v2 | _ => none)
  <|> (match bview v2 with | some (.ff, []) => some v1 | _ => none)

/-- `p || not p -> true` -/
noncomputable def b_or.r_not (v1 v2 : Term L) : Option (Term L) :=
  (match bview v2 with
    | some (.not, [p]) => if p = v1 then some (mkBool true) else none | _ => none)
  <|> (match bview v1 with
    | some (.not, [p]) => if p = v2 then some (mkBool true) else none | _ => none)

/-- `(a || _ as x) || a -> x` -/
noncomputable def b_or.r_or (v1 v2 : Term L) : Option (Term L) :=
  (match bview v1 with
    | some (.or, [a, _]) => if a = v2 then some v1 else none | _ => none)
  <|> (match bview v1 with
    | some (.or, [_, a]) => if a = v2 then some v1 else none | _ => none)
  <|> (match bview v2 with
    | some (.or, [a, _]) => if a = v1 then some v2 else none | _ => none)
  <|> (match bview v2 with
    | some (.or, [_, a]) => if a = v1 then some v2 else none | _ => none)

/-- `(a && _) || a -> a` -/
noncomputable def b_or.r_and (v1 v2 : Term L) : Option (Term L) :=
  (match bview v1 with
    | some (.and, [a, _]) => if a = v2 then some v2 else none | _ => none)
  <|> (match bview v1 with
    | some (.and, [_, a]) => if a = v2 then some v2 else none | _ => none)
  <|> (match bview v2 with
    | some (.and, [a, _]) => if a = v1 then some v1 else none | _ => none)
  <|> (match bview v2 with
    | some (.and, [_, a]) => if a = v1 then some v1 else none | _ => none)

end

/-- `not true -> false`, `not false -> true`, `not (not x) -> x`, and De
Morgan's laws, which call the rule functions. -/
def b_not.r_lit (v : Term L) : Option (Term L) :=
  (match bview v with | some (.tt, []) => some (mkBool false) | _ => none)
  <|> (match bview v with | some (.ff, []) => some (mkBool true) | _ => none)

def b_not.r_not (v : Term L) : Option (Term L) :=
  match bview v with | some (.not, [x]) => some x | _ => none

def b_not.r_or (v : Term L) : Option (Term L) :=
  match bview v with
  | some (.or, [a, b]) => some (O.b_and (O.b_not a) (O.b_not b))
  | _ => none

def b_not.r_and (v : Term L) : Option (Term L) :=
  match bview v with
  | some (.and, [a, b]) => some (O.b_or (O.b_not a) (O.b_not b))
  | _ => none

/-! ### Their proofs: one tactic for all -/

theorem b_and.r_same.sound (hO : O.Sound) {v1 v2 r : Term L} (h : r_same v1 v2 = some r) :
    Refines (mkAnd v1 v2) r := by simp only [r_same] at h; bool_rule hO h
theorem b_and.r_false.sound (hO : O.Sound) {v1 v2 r : Term L} (h : r_false v1 v2 = some r) :
    Refines (mkAnd v1 v2) r := by simp only [r_false] at h; bool_rule hO h
theorem b_and.r_true.sound (hO : O.Sound) {v1 v2 r : Term L} (h : r_true v1 v2 = some r) :
    Refines (mkAnd v1 v2) r := by simp only [r_true] at h; bool_rule hO h
theorem b_and.r_not.sound (hO : O.Sound) {v1 v2 r : Term L} (h : r_not v1 v2 = some r) :
    Refines (mkAnd v1 v2) r := by simp only [r_not] at h; bool_rule hO h
theorem b_and.r_and.sound (hO : O.Sound) {v1 v2 r : Term L} (h : r_and v1 v2 = some r) :
    Refines (mkAnd v1 v2) r := by simp only [r_and] at h; bool_rule hO h
theorem b_and.r_or.sound (hO : O.Sound) {v1 v2 r : Term L} (h : r_or v1 v2 = some r) :
    Refines (mkAnd v1 v2) r := by simp only [r_or] at h; bool_rule hO h
theorem b_or.r_same.sound (hO : O.Sound) {v1 v2 r : Term L} (h : r_same v1 v2 = some r) :
    Refines (mkOr v1 v2) r := by simp only [r_same] at h; bool_rule hO h
theorem b_or.r_true.sound (hO : O.Sound) {v1 v2 r : Term L} (h : r_true v1 v2 = some r) :
    Refines (mkOr v1 v2) r := by simp only [r_true] at h; bool_rule hO h
theorem b_or.r_false.sound (hO : O.Sound) {v1 v2 r : Term L} (h : r_false v1 v2 = some r) :
    Refines (mkOr v1 v2) r := by simp only [r_false] at h; bool_rule hO h
theorem b_or.r_not.sound (hO : O.Sound) {v1 v2 r : Term L} (h : r_not v1 v2 = some r) :
    Refines (mkOr v1 v2) r := by simp only [r_not] at h; bool_rule hO h
theorem b_or.r_or.sound (hO : O.Sound) {v1 v2 r : Term L} (h : r_or v1 v2 = some r) :
    Refines (mkOr v1 v2) r := by simp only [r_or] at h; bool_rule hO h
theorem b_or.r_and.sound (hO : O.Sound) {v1 v2 r : Term L} (h : r_and v1 v2 = some r) :
    Refines (mkOr v1 v2) r := by simp only [r_and] at h; bool_rule hO h
theorem b_not.r_lit.sound (hO : O.Sound) {v r : Term L} (h : r_lit v = some r) :
    Refines (mkNot v) r := by simp only [r_lit] at h; bool_rule hO h
theorem b_not.r_not.sound (hO : O.Sound) {v r : Term L} (h : r_not v = some r) :
    Refines (mkNot v) r := by simp only [r_not] at h; bool_rule hO h
theorem b_not.r_or.sound (hO : O.Sound) {v r : Term L} (h : r_or O v = some r) :
    Refines (mkNot v) r := by simp only [r_or] at h; bool_rule hO h
theorem b_not.r_and.sound (hO : O.Sound) {v r : Term L} (h : r_and O v = some r) :
    Refines (mkNot v) r := by simp only [r_and] at h; bool_rule hO h

end Bvr.Core
