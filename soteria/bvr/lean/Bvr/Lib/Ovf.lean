import Bvr.Lib.Meta
import Bvr.Lib.Lit

/-!
# Overflow

The overflow helpers of the rules, on values of known width, are Lean's
`BitVec` overflow predicates (`add_overflows_mk`, ...). Overflow facts are
then proved through `toInt` and `toNat` (`bvr_ovf`).
-/

namespace Bvr.Lib

open Classical

theorem min_for_true {n : Nat} (hn : 0 < n) : min_for true n = -2 ^ (n - 1) := by
  simp [min_for, zshiftl]

theorem max_for_true {n : Nat} (hn : 0 < n) : max_for true n = 2 ^ (n - 1) - 1 := by
  simp [max_for, zshiftl]

@[simp] theorem min_for_false (n : Int) : min_for false n = 0 := rfl

@[simp] theorem max_for_false (n : Nat) : max_for false n = 2 ^ n - 1 := by
  simp [max_for, zshiftl]

section
variable {n : Nat} (x y : BitVec n)

theorem add_overflows_mk (s : Bool) (hn : 0 < n) :
    add_overflows s ⟨n, x⟩ ⟨n, y⟩ = if s then x.saddOverflow y else x.uaddOverflow y := by
  have := BitVec.isLt x; have := BitVec.isLt y
  have e : ((2 ^ n : Nat) : Int) = (2 : Int) ^ n := by push_cast; rfl
  cases s <;> simp only [add_overflows, min_for_true hn, max_for_true hn, min_for_false,
    max_for_false, BitVec.saddOverflow, BitVec.uaddOverflow, to_z_mk, width_mk, if_true, if_false] <;>
    rw [Bool.eq_iff_iff] <;> simp <;> omega

theorem sub_overflows_mk (s : Bool) (hn : 0 < n) :
    sub_overflows s ⟨n, x⟩ ⟨n, y⟩ = if s then x.ssubOverflow y else x.usubOverflow y := by
  have := BitVec.isLt x; have := BitVec.isLt y
  have e : ((2 ^ n : Nat) : Int) = (2 : Int) ^ n := by push_cast; rfl
  cases s <;> simp only [sub_overflows, min_for_true hn, max_for_true hn, min_for_false,
    max_for_false, BitVec.ssubOverflow, BitVec.usubOverflow, to_z_mk, width_mk, if_true, if_false] <;>
    rw [Bool.eq_iff_iff] <;> simp <;> omega

theorem mul_overflows_mk (s : Bool) (hn : 0 < n) :
    mul_overflows s ⟨n, x⟩ ⟨n, y⟩ = if s then x.smulOverflow y else x.umulOverflow y := by
  have := BitVec.isLt x; have := BitVec.isLt y
  have e : ((2 ^ n : Nat) : Int) = (2 : Int) ^ n := by push_cast; rfl
  cases s <;> simp only [mul_overflows, min_for_true hn, max_for_true hn, min_for_false,
    max_for_false, BitVec.smulOverflow, BitVec.umulOverflow, to_z_mk, width_mk, if_true, if_false] <;>
    rw [Bool.eq_iff_iff] <;> simp <;> omega

theorem is_int_min_mk (hn : 0 < n) : is_int_min ⟨n, x⟩ = decide (x = BitVec.intMin n) := by
  simp only [is_int_min, to_z_mk, width_mk, min_for_true hn, if_true]
  by_cases h : x = BitVec.intMin n
  · subst h; simp [BitVec.toInt_intMin, hn]
  · have : x.toInt ≠ -2 ^ (n - 1) := by
      intro e; apply h; apply BitVec.eq_of_toInt_eq; rw [e, BitVec.toInt_intMin]; simp [hn]
    simp [h, this]

@[simp] theorem udivides_mk : udivides ⟨n, x⟩ ⟨n, y⟩ = decide (x.toNat ∣ y.toNat) := by
  simp [udivides, divisible, Int.natCast_dvd_natCast]

end

theorem fold_checked_mk {n : Nat} (hn : 0 < n) (c : Checked) (x y : BitVec n) (add : Bool) :
    fold_checked c ⟨n, x⟩ ⟨n, y⟩ add =
      { signed := c.signed && !(if add then x.saddOverflow y else x.ssubOverflow y),
        unsigned := c.unsigned && !(if add then x.uaddOverflow y else x.usubOverflow y) } := by
  cases add <;> simp [fold_checked, checked_has, add_overflows_mk _ _ _ hn,
    sub_overflows_mk _ _ _ hn]

/-! ## Overflow facts, through integers -/

section
variable {w : Nat} {x y : BitVec w}

theorem sadd_ok : x.saddOverflow y = false ↔
    -2 ^ (w - 1) ≤ x.toInt + y.toInt ∧ x.toInt + y.toInt < 2 ^ (w - 1) := by
  simp [BitVec.saddOverflow]; omega
theorem ssub_ok : x.ssubOverflow y = false ↔
    -2 ^ (w - 1) ≤ x.toInt - y.toInt ∧ x.toInt - y.toInt < 2 ^ (w - 1) := by
  simp [BitVec.ssubOverflow]; omega
theorem smul_ok : x.smulOverflow y = false ↔
    -2 ^ (w - 1) ≤ x.toInt * y.toInt ∧ x.toInt * y.toInt < 2 ^ (w - 1) := by
  simp [BitVec.smulOverflow]; omega
theorem uadd_ok : x.uaddOverflow y = false ↔ x.toNat + y.toNat < 2 ^ w := by
  simp [BitVec.uaddOverflow]
theorem usub_ok : x.usubOverflow y = false ↔ y.toNat ≤ x.toNat := by
  simp [BitVec.usubOverflow]
theorem umul_ok : x.umulOverflow y = false ↔ x.toNat * y.toNat < 2 ^ w := by
  simp [BitVec.umulOverflow]

theorem toInt_add_ok (h : x.saddOverflow y = false) : (x + y).toInt = x.toInt + y.toInt :=
  BitVec.toInt_add_of_not_saddOverflow (by simp [h])
theorem toInt_sub_ok (h : x.ssubOverflow y = false) : (x - y).toInt = x.toInt - y.toInt :=
  BitVec.toInt_sub_of_not_ssubOverflow (by simp [h])
theorem toInt_mul_ok (h : x.smulOverflow y = false) : (x * y).toInt = x.toInt * y.toInt :=
  BitVec.toInt_mul_of_not_smulOverflow (by simp [h])
theorem toNat_add_ok (h : x.uaddOverflow y = false) : (x + y).toNat = x.toNat + y.toNat :=
  BitVec.toNat_add_of_not_uaddOverflow (by simp [h])
theorem toNat_sub_ok (h : x.usubOverflow y = false) : (x - y).toNat = x.toNat - y.toNat :=
  BitVec.toNat_sub_of_not_usubOverflow (by simp [h])
theorem toNat_mul_ok (h : x.umulOverflow y = false) : (x * y).toNat = x.toNat * y.toNat :=
  BitVec.toNat_mul_of_not_umulOverflow (by simp [h])

end

theorem smulOverflow_neg_swap {n : Nat} {c v : BitVec n} (hc : c ≠ BitVec.intMin n)
    (hv : v ≠ BitVec.intMin n) : (-c).smulOverflow v = c.smulOverflow (-v) := by
  simp only [BitVec.smulOverflow, BitVec.toInt_neg_of_ne_intMin hc,
    BitVec.toInt_neg_of_ne_intMin hv, Int.neg_mul, Int.mul_neg]

theorem umul_assoc_ok {n : Nat} {x y z : BitVec n} (h1 : x.umulOverflow y = false)
    (h2 : (x * y).umulOverflow z = false) : x.umulOverflow (y * z) = false := by
  have e := toNat_mul_ok h1
  rw [umul_ok] at *
  rw [e] at h2
  have : (y * z).toNat ≤ y.toNat * z.toNat := by rw [BitVec.toNat_mul]; exact Nat.mod_le _ _
  calc x.toNat * (y * z).toNat ≤ x.toNat * (y.toNat * z.toNat) := Nat.mul_le_mul_left _ this
    _ = x.toNat * y.toNat * z.toNat := (Nat.mul_assoc ..).symm
    _ < 2 ^ n := h2
theorem smul_assoc_ok {n : Nat} {x y z : BitVec n} (h1 : x.smulOverflow y = false)
    (h2 : (x * y).smulOverflow z = false) (h3 : y.smulOverflow z = false) :
    x.smulOverflow (y * z) = false := by
  have e := toInt_mul_ok h1
  have e3 := toInt_mul_ok h3
  rw [smul_ok] at *
  rw [e3, ← Int.mul_assoc, ← e]; exact h2
theorem two_pow_pred {n : Nat} (hn : 0 < n) : (2 : Int) ^ n = 2 * 2 ^ (n - 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  simp [Int.pow_succ, Int.mul_comm]

theorem toInt_bounds {w : Nat} (x : BitVec w) :
    -2 ^ (w - 1) ≤ x.toInt ∧ x.toInt < 2 ^ (w - 1) :=
  ⟨BitVec.le_toInt x, BitVec.toInt_lt⟩

open Lean Meta Elab Tactic in
/-- Adds the integer meaning of the non-overflow hypotheses. -/
def ovfEqs (g : MVarId) : MetaM MVarId := g.withContext do
  let mut g := g
  for d in (← getLCtx) do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    let some (_, lhs, rhs) := ty.eq? | continue
    unless rhs.isConstOf ``Bool.false do continue
    let lems := [(``BitVec.saddOverflow, ``toInt_add_ok), (``BitVec.ssubOverflow, ``toInt_sub_ok),
      (``BitVec.smulOverflow, ``toInt_mul_ok), (``BitVec.uaddOverflow, ``toNat_add_ok),
      (``BitVec.usubOverflow, ``toNat_sub_ok), (``BitVec.umulOverflow, ``toNat_mul_ok)]
    for (f, lem) in lems do
      if lhs.isAppOfArity f 3 then
        let pf ← mkAppM lem #[d.toExpr]
        let (_, g') ← (← g.assert `hovf (← inferType pf) pf).intro1P
        g := g'
  return g

open Lean Meta Elab Tactic in
/-- Adds the bounds of the `toInt`s and `toNat`s of the goal and hypotheses. -/
def ovfBounds (g : MVarId) : MetaM MVarId := g.withContext do
  let mut g := g
  let mut exprs : Array Expr := #[← instantiateMVars (← g.getType)]
  for d in (← getLCtx) do
    if !d.isImplementationDetail then exprs := exprs.push (← instantiateMVars d.type)
  let mut atoms : Array Expr := #[]
  for e in exprs do
    let subs := (e.foldlM (m := Id) (init := #[]) fun acc sub =>
      if (sub.isAppOfArity ``BitVec.toInt 2 || sub.isAppOfArity ``BitVec.toNat 2) &&
          !acc.contains sub.appArg! then acc.push sub.appArg! else acc)
    atoms := atoms ++ subs.filter (!atoms.contains ·)
  for x in atoms do
    for lem in [``toInt_bounds, ``BitVec.isLt] do
      let pf ← mkAppM lem #[x]
      let (_, g') ← (← g.assert `hbd (← inferType pf) pf).intro1P
      g := g'
  return g

open Lean Meta Elab Tactic in
elab "bvr_ovf_eqs" : tactic => liftMetaTactic fun g => return [← ovfEqs g]

open Lean Meta Elab Tactic in
elab "bvr_bounds" : tactic => liftMetaTactic fun g => return [← ovfBounds g]

open Lean Meta Elab Tactic in
/-- Case splits the booleans, and the checked flags. -/
partial def splitBools (g : MVarId) : MetaM (List MVarId) := g.withContext do
  for d in (← getLCtx) do
    if d.isImplementationDetail then continue
    let ty ← whnfR (← instantiateMVars d.type)
    if ty.isConstOf ``Bool || ty.isConstOf ``Bvr.Checked then
      let subgoals ← g.cases d.fvarId
      return ← subgoals.toList.foldlM (init := []) fun acc sg =>
        return acc ++ (← splitBools sg.mvarId)
  return [g]

open Lean Meta Elab Tactic in
elab "bvr_bools" : tactic => liftMetaTactic splitBools

open Lean Meta Elab Tactic in
/-- Case splits the booleans of the context. -/
partial def splitBoolVars (g : MVarId) : MetaM (List MVarId) := g.withContext do
  for d in (← getLCtx) do
    if d.isImplementationDetail then continue
    let ty ← whnfR (← instantiateMVars d.type)
    if ty.isConstOf ``Bool then
      let subgoals ← g.cases d.fvarId
      return ← subgoals.toList.foldlM (init := []) fun acc sg =>
        return acc ++ (← splitBoolVars sg.mvarId)
  return [g]

open Lean Meta Elab Tactic in
elab "bvr_bool_vars" : tactic => liftMetaTactic splitBoolVars

/-- Proves overflow facts: splits the flags, and reasons on integers. -/
macro "bvr_ovf" : tactic => `(tactic| (
  bvr_bools
  all_goals (try simp_all)
  all_goals (repeat' (first | apply And.intro | intro))
  all_goals bvr_split
  all_goals bvr_ovf_eqs
  all_goals (try simp only [sadd_ok, ssub_ok, smul_ok, uadd_ok, usub_ok, umul_ok] at *)
  all_goals bvr_split
  all_goals bvr_bounds
  all_goals (try push_cast at *)
  all_goals (try simp only [Int.natCast_pow, Int.natCast_ofNat] at *)
  all_goals omega))

end Bvr.Lib
