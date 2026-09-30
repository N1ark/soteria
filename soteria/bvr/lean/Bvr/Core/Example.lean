import Bvr.Core.Bool
import Bvr.Core.Int

/-!
# A language made of modules (trial)

Booleans and integers: a flat, concrete language, as bvr would generate it
from a declaration that includes the Bool and Int modules. Its instances of
`HasBool` and `HasInt` are all it needs to reuse the rules of both modules and
their proofs.
-/

namespace Bvr.Core.Example

inductive Op where
  | tt | ff | not | and | or | int (z : Int) | add
  deriving DecidableEq

inductive Ty where
  | tbool | tint
  deriving DecidableEq

inductive Val where
  | b (x : Bool) | i (z : Int)

def Val.toBool : Val → Option Bool | .b x => some x | _ => none
def Val.toInt : Val → Option Int | .i z => some z | _ => none

def wt : Op → List Ty → Ty → Prop
  | .tt, as, t | .ff, as, t => as = [] ∧ t = .tbool
  | .not, as, t => as = [.tbool] ∧ t = .tbool
  | .and, as, t | .or, as, t => as = [.tbool, .tbool] ∧ t = .tbool
  | .int _, as, t => as = [] ∧ t = .tint
  | .add, as, t => as = [.tint, .tint] ∧ t = .tint

def den : Op → List (Option Val) → Option Val
  | .tt, [] => some (.b true)
  | .ff, [] => some (.b false)
  | .not, [v] => (v.bind Val.toBool).map (fun b => .b (!b))
  | .and, [v, w] => (pand (v.bind Val.toBool) (w.bind Val.toBool)).map .b
  | .int z, [] => some (.i z)
  | .add, [v, w] => (do let a ← v.bind Val.toInt; let b ← w.bind Val.toInt; pure (a + b)).map .i
  | _, _ => none

def lang : Lang :=
  { Op, Ty, Val, wt, den, hasTy := fun v t => match v, t with
      | .b _, .tbool | .i _, .tint => True
      | _, _ => False }

instance : HasBool lang where
  op | .tt => Op.tt | .ff => .ff | .not => .not | .and => .and | .or => .or
  view | .tt => some .tt | .ff => some .ff | .not => some .not | .and => some .and
       | .or => some .or | _ => none
  view_op o := by cases o <;> rfl
  op_of_view {o b} h := by cases o <;> cases b <;> simp_all <;> rfl
  tBool := Ty.tbool
  ofBool := Val.b
  toBool := Val.toBool
  toBool_ofBool _ := rfl
  ofBool_of_toBool {v b} h := by cases v <;> simp_all [Val.toBool] <;> rfl
  wt_lit {b as t} hb h := by rcases hb with rfl | rfl <;> exact h
  wt_not := Iff.rfl
  wt_and := Iff.rfl
  wt_tt := ⟨rfl, rfl⟩
  wt_ff := ⟨rfl, rfl⟩
  den_tt := rfl
  den_ff := rfl
  den_not _ := rfl
  den_and _ _ := rfl

instance : HasInt lang where
  op | .lit z => Op.int z | .add => .add
  view | .int z => some (.lit z) | .add => some .add | _ => none
  view_op o := by cases o <;> rfl
  op_of_view {o i} h := by cases o <;> cases i <;> simp_all <;> rfl
  tInt := Ty.tint
  ofInt := Val.i
  toInt := Val.toInt
  toInt_ofInt _ := rfl
  ofInt_of_toInt {v z} h := by cases v <;> simp_all [Val.toInt] <;> rfl
  wt_lit := Iff.rfl
  wt_add := Iff.rfl
  den_lit _ := rfl
  den_add _ _ := rfl

/-- The rules of both modules are sound in this language, by their generic
proofs. -/
example (v1 v2 r : Term lang) (h : b_and.r_true v1 v2 = some r) : Refines (mkAnd v1 v2) r :=
  b_and.r_true.sound h

example (v1 v2 r : Term lang) (h : add.r_zero v1 v2 = some r) : Refines (mkAdd v1 v2) r :=
  add.r_zero.sound h

end Bvr.Core.Example
