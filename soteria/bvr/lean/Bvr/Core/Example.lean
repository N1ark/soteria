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
  | .not, [v] => (pnot (v.bind Val.toBool)).map .b
  | .and, [v, w] => (pand (v.bind Val.toBool) (w.bind Val.toBool)).map .b
  | .or, [v, w] => (por (v.bind Val.toBool) (w.bind Val.toBool)).map .b
  | .int z, [] => some (.i z)
  | .add, [v, w] => (do let a ← v.bind Val.toInt; let b ← w.bind Val.toInt; pure (a + b)).map .i
  | _, _ => none

/-- An operand that is not poison is kept; a poison one may become any value. -/
theorem mono_arg {a b : Option Val} (h : ∀ x, a = some x → b = some x) :
    (a = none ∨ (∃ x, a = some (.b x)) ∨ ∃ z, a = some (.i z)) ∧ b = a ∨
      a = none ∧ (b = none ∨ (∃ x, b = some (.b x)) ∨ ∃ z, b = some (.i z)) := by
  rcases a with _ | (x | z)
  · rcases b with _ | (x | z) <;> simp
  · exact .inl ⟨by simp, h _ rfl⟩
  · exact .inl ⟨by simp, h _ rfl⟩

theorem den_mono {o vs ws v} (h : Pointwise (fun a b => ∀ x, a = some x → b = some x) vs ws)
    (e : den o vs = some v) : den o ws = some v := by
  rcases h with _ | ⟨h1, _ | ⟨h2, _ | ⟨_, _⟩⟩⟩
  · exact e
  · rcases mono_arg h1 with ⟨rfl | ⟨_, rfl⟩ | ⟨_, rfl⟩, rfl⟩ | ⟨rfl, rfl | ⟨_, rfl⟩ | ⟨_, rfl⟩⟩ <;>
      cases o <;> simp_all [den, pnot]
  · rcases mono_arg h1 with ⟨rfl | ⟨x, rfl⟩ | ⟨_, rfl⟩, rfl⟩ | ⟨rfl, rfl | ⟨x, rfl⟩ | ⟨_, rfl⟩⟩ <;>
    rcases mono_arg h2 with ⟨rfl | ⟨y, rfl⟩ | ⟨_, rfl⟩, rfl⟩ | ⟨rfl, rfl | ⟨y, rfl⟩ | ⟨_, rfl⟩⟩ <;>
      cases o <;> (try cases x) <;> (try cases y) <;>
      simp only [den, pand, por, Val.toBool, Val.toInt, Option.bind, Option.map] at e ⊢ <;>
      simp_all
  · cases o <;> simp [den] at e

def lang : Lang :=
  { Op, Ty, Val, wt, den, den_mono, hasTy := fun v t => match v, t with
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
  wt_tt := Iff.rfl
  wt_ff := Iff.rfl
  wt_not := Iff.rfl
  wt_and := Iff.rfl
  wt_or := Iff.rfl
  den_tt := rfl
  den_ff := rfl
  den_not _ := rfl
  den_and _ _ := rfl
  den_or _ _ := rfl

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
proofs, given sound smart constructors `O` for the rules to call. -/
example (O : BoolOps lang) (hO : O.Sound) (v1 v2 r : Term lang)
    (h : b_and.r_true v1 v2 = some r) : Refines (mkAnd v1 v2) r :=
  b_and.r_true.sound O hO h

example (O : BoolOps lang) (hO : O.Sound) (v r : Term lang)
    (h : b_not.r_and O v = some r) : Refines (mkNot v) r :=
  b_not.r_and.sound O hO h

example (v1 v2 r : Term lang) (h : add.r_zero v1 v2 = some r) : Refines (mkAdd v1 v2) r :=
  add.r_zero.sound h

end Bvr.Core.Example
