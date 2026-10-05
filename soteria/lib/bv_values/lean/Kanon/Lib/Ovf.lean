import Kanon.Lib.Meta
import Kanon.Lib.Lit

/-!
# Overflow

The overflow helpers of the rules, on literals in range of a known width, are
Lean's `BitVec` overflow predicates (`overflows_add_ofInt`, ...). Overflow facts
are then proved through `toInt` and `toNat` (`kanon_ovf`).
-/

namespace Kanon.Lib

open Classical

theorem min_for_true {n : Nat} (hn : 0 < n) : Bitvec.min_for true n = -2 ^ (n - 1) := by
  simp [Bitvec.min_for, z_lsl]

theorem max_for_true {n : Nat} (hn : 0 < n) : Bitvec.max_for true n = 2 ^ (n - 1) - 1 := by
  simp [Bitvec.max_for, z_lsl]

@[simp] theorem min_for_false (n : Int) : Bitvec.min_for false n = 0 := rfl

@[simp] theorem max_for_false (n : Nat) : Bitvec.max_for false n = 2 ^ n - 1 := by
  simp [Bitvec.max_for, z_lsl]

@[simp] theorem z_asr_zero (z : Int) : zasr z 0 = z := by simp [zasr]

theorem bv_to_z_true {n : Nat} (hn : 0 < n) (z : Int) :
    Bitvec.to_z true (n : Int) z = (BitVec.ofInt n z).toInt := by
  have h2 : ((2 : Int) ^ n + 1) / 2 = 2 ^ (n - 1) := by
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    simp only [Nat.add_sub_cancel, Int.pow_succ]; omega
  have h3 : (2 : Int) ^ n = 2 * 2 ^ (n - 1) := by
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    simp only [Nat.add_sub_cancel, Int.pow_succ]; omega
  have e : ((2 ^ n : Nat) : Int) = (2 : Int) ^ n := by push_cast; rfl
  simp only [Bitvec.to_z, if_true, signed_extract, z_asr_zero, Int.toNat_natCast, BitVec.toInt_ofInt,
    Int.bmod, e, h2]
  split <;> split <;> omega

theorem bv_to_z_false {n : Nat} {z : Int} (h0 : 0 ≤ z) (h1 : z < 2 ^ n) :
    Bitvec.to_z false (n : Int) z = ((BitVec.ofInt n z).toNat : Int) := by
  have e : ((2 ^ n : Nat) : Int) = (2 : Int) ^ n := by push_cast; rfl
  simp only [Bitvec.to_z, Bool.false_eq_true, if_false, BitVec.toNat_ofInt, e,
    Int.emod_eq_of_lt h0 h1]
  omega

/-- The integer that a bit-vector stands for, in a signedness. -/
abbrev iv (s : Bool) {w : Nat} (x : BitVec w) : Int := if s then x.toInt else x.toNat

theorem bv_to_z_ofInt {n : Nat} (hn : 0 < n) (s : Bool) {z : Int} (h0 : 0 ≤ z) (h1 : z < 2 ^ n) :
    Bitvec.to_z s (n : Int) z = iv s (BitVec.ofInt n z) := by
  cases s
  · exact bv_to_z_false h0 h1
  · exact bv_to_z_true hn z

section
variable {n : Nat} (hn : 0 < n)
include hn

theorem overflows_add_ofInt (s : Bool) {l r : Int} (hl0 : 0 ≤ l) (hl1 : l < 2 ^ n) (hr0 : 0 ≤ r)
    (hr1 : r < 2 ^ n) :
    Bitvec.overflows_add s n l r =
      if s then (BitVec.ofInt n l).saddOverflow (BitVec.ofInt n r)
      else (BitVec.ofInt n l).uaddOverflow (BitVec.ofInt n r) := by
  cases s
  · simp only [Bitvec.overflows_add, bv_to_z_false hl0 hl1, bv_to_z_false hr0 hr1, min_for_false,
      max_for_false, BitVec.uaddOverflow, BitVec.toNat_ofInt, Bool.false_eq_true, if_false]
    have e : ((2 ^ n : Nat) : Int) = (2 : Int) ^ n := by push_cast; rfl
    rw [Bool.eq_iff_iff]; simp [Int.emod_eq_of_lt hl0 hl1, Int.emod_eq_of_lt hr0 hr1]
    omega
  · have := BitVec.le_toInt (BitVec.ofInt n l); have := BitVec.toInt_lt (x := BitVec.ofInt n l)
    simp only [Bitvec.overflows_add, bv_to_z_true hn, min_for_true hn, max_for_true hn,
      BitVec.saddOverflow, if_true]
    rw [Bool.eq_iff_iff]; simp; omega

theorem overflows_sub_ofInt (s : Bool) {l r : Int} (hl0 : 0 ≤ l) (hl1 : l < 2 ^ n) (hr0 : 0 ≤ r)
    (hr1 : r < 2 ^ n) :
    Bitvec.overflows_sub s n l r =
      if s then (BitVec.ofInt n l).ssubOverflow (BitVec.ofInt n r)
      else (BitVec.ofInt n l).usubOverflow (BitVec.ofInt n r) := by
  cases s
  · simp only [Bitvec.overflows_sub, bv_to_z_false hl0 hl1, bv_to_z_false hr0 hr1, min_for_false,
      max_for_false, BitVec.usubOverflow, BitVec.toNat_ofInt, Bool.false_eq_true, if_false]
    have e : ((2 ^ n : Nat) : Int) = (2 : Int) ^ n := by push_cast; rfl
    rw [Bool.eq_iff_iff]; simp [Int.emod_eq_of_lt hl0 hl1, Int.emod_eq_of_lt hr0 hr1]
    omega
  · have := BitVec.le_toInt (BitVec.ofInt n l); have := BitVec.toInt_lt (x := BitVec.ofInt n l)
    simp only [Bitvec.overflows_sub, bv_to_z_true hn, min_for_true hn, max_for_true hn,
      BitVec.ssubOverflow, if_true]
    rw [Bool.eq_iff_iff]; simp; omega

theorem overflows_mul_ofInt (s : Bool) {l r : Int} (hl0 : 0 ≤ l) (hl1 : l < 2 ^ n) (hr0 : 0 ≤ r)
    (hr1 : r < 2 ^ n) :
    Bitvec.overflows_mul s n l r =
      if s then (BitVec.ofInt n l).smulOverflow (BitVec.ofInt n r)
      else (BitVec.ofInt n l).umulOverflow (BitVec.ofInt n r) := by
  cases s
  · obtain ⟨l, rfl⟩ := Int.eq_ofNat_of_zero_le hl0
    obtain ⟨r, rfl⟩ := Int.eq_ofNat_of_zero_le hr0
    have e : ((2 ^ n : Nat) : Int) = (2 : Int) ^ n := by push_cast; rfl
    have hl : l < 2 ^ n := by exact_mod_cast hl1
    have hr : r < 2 ^ n := by exact_mod_cast hr1
    simp only [Bitvec.overflows_mul, bv_to_z_false (Int.natCast_nonneg l) hl1,
      bv_to_z_false (Int.natCast_nonneg r) hr1, min_for_false, max_for_false, BitVec.umulOverflow,
      BitVec.toNat_ofInt, Bool.false_eq_true, if_false, e, Int.emod_eq_of_lt (Int.natCast_nonneg l) hl1,
      Int.emod_eq_of_lt (Int.natCast_nonneg r) hr1, Int.toNat_natCast]
    rw [Bool.eq_iff_iff]
    simp only [Bool.or_eq_true, decide_eq_true_eq]
    have : (0 : Int) ≤ l * r := Int.mul_nonneg (Int.natCast_nonneg l) (Int.natCast_nonneg r)
    have e2 : ((l * r : Nat) : Int) = (l : Int) * r := by push_cast; rfl
    rw [← e2] at *
    omega
  · simp only [Bitvec.overflows_mul, bv_to_z_true hn, min_for_true hn, max_for_true hn,
      BitVec.smulOverflow, if_true]
    rw [Bool.eq_iff_iff]; simp; omega

theorem is_int_min_ofInt (z : Int) : Bitvec.is_int_min n z = decide (BitVec.ofInt n z = BitVec.intMin n) := by
  simp only [Bitvec.is_int_min, bv_to_z_true hn, min_for_true hn]
  rw [← BitVec.toInt_intMin_of_pos hn]
  simp only [BitVec.toInt_inj]

end

theorem udivides_ofInt {n : Nat} {d z : Int} (hd0 : 0 ≤ d) (hd1 : d < 2 ^ n) (hz0 : 0 ≤ z)
    (hz1 : z < 2 ^ n) :
    Bitvec.udivides d z = decide ((BitVec.ofInt n d).toNat ∣ (BitVec.ofInt n z).toNat) := by
  obtain ⟨d, rfl⟩ := Int.eq_ofNat_of_zero_le hd0
  obtain ⟨z, rfl⟩ := Int.eq_ofNat_of_zero_le hz0
  have e : ((2 ^ n : Nat) : Int) = (2 : Int) ^ n := by push_cast; rfl
  simp only [Bitvec.udivides, divisible, BitVec.toNat_ofInt, e, Int.emod_eq_of_lt hd0 hd1,
    Int.emod_eq_of_lt hz0 hz1, Int.toNat_natCast, Int.natCast_dvd_natCast]

theorem add_overflows_ofInt {n : Nat} (hn : 0 < n) (s : Bool) {s2 : Ty} {l r : Int} (hl0 : 0 ≤ l)
    (hl1 : l < 2 ^ n) (hr0 : 0 ≤ r) (hr1 : r < 2 ^ n) :
    Bitvec.lit_add_overflows s (.TBitVector (n : Int)) s2 l r =
      if s then (BitVec.ofInt n l).saddOverflow (BitVec.ofInt n r)
      else (BitVec.ofInt n l).uaddOverflow (BitVec.ofInt n r) :=
  overflows_add_ofInt hn s hl0 hl1 hr0 hr1

theorem sub_overflows_ofInt {n : Nat} (hn : 0 < n) (s : Bool) {s2 : Ty} {l r : Int} (hl0 : 0 ≤ l)
    (hl1 : l < 2 ^ n) (hr0 : 0 ≤ r) (hr1 : r < 2 ^ n) :
    Bitvec.lit_sub_overflows s (.TBitVector (n : Int)) s2 l r =
      if s then (BitVec.ofInt n l).ssubOverflow (BitVec.ofInt n r)
      else (BitVec.ofInt n l).usubOverflow (BitVec.ofInt n r) :=
  overflows_sub_ofInt hn s hl0 hl1 hr0 hr1

theorem mul_overflows_ofInt {n : Nat} (hn : 0 < n) (s : Bool) {s2 : Ty} {l r : Int} (hl0 : 0 ≤ l)
    (hl1 : l < 2 ^ n) (hr0 : 0 ≤ r) (hr1 : r < 2 ^ n) :
    Bitvec.lit_mul_overflows s (.TBitVector (n : Int)) s2 l r =
      if s then (BitVec.ofInt n l).smulOverflow (BitVec.ofInt n r)
      else (BitVec.ofInt n l).umulOverflow (BitVec.ofInt n r) :=
  overflows_mul_ofInt hn s hl0 hl1 hr0 hr1

theorem fold_checked_ofInt {n : Nat} (hn : 0 < n) {a b : Int} (ha0 : 0 ≤ a) (ha1 : a < 2 ^ n)
    (hb0 : 0 ≤ b) (hb1 : b < 2 ^ n) (c : Checked) (add : Bool) :
    Bitvec.fold_checked c n a b add =
      { signed := c.signed && !(if add then (BitVec.ofInt n a).saddOverflow (BitVec.ofInt n b)
          else (BitVec.ofInt n a).ssubOverflow (BitVec.ofInt n b)),
        unsigned := c.unsigned && !(if add then (BitVec.ofInt n a).uaddOverflow (BitVec.ofInt n b)
          else (BitVec.ofInt n a).usubOverflow (BitVec.ofInt n b)) } := by
  cases add <;> simp [Bitvec.fold_checked, Bitvec.checked_has, overflows_add_ofInt hn _ ha0 ha1 hb0 hb1,
    overflows_sub_ofInt hn _ ha0 ha1 hb0 hb1]

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
  rwa [← BitVec.smulOverflow_assoc (by simp [h1]) (by simp [h3])]

attribute [kanon_close_simp] BitVec.mul_assoc smulOverflow_neg_swap umul_assoc_ok smul_assoc_ok

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
elab "kanon_ovf_eqs" : tactic => liftMetaTactic fun g => return [← ovfEqs g]

open Lean Meta Elab Tactic in
elab "kanon_bounds" : tactic => liftMetaTactic fun g => return [← ovfBounds g]

open Lean Meta Elab Tactic in
/-- Case splits the booleans, and the checked flags. -/
partial def splitBools (g : MVarId) : MetaM (List MVarId) := g.withContext do
  for d in (← getLCtx) do
    if d.isImplementationDetail then continue
    let ty ← whnfR (← instantiateMVars d.type)
    if ty.isConstOf ``Bool || ty.isConstOf ``Kanon.Checked then
      let subgoals ← g.cases d.fvarId
      return ← subgoals.toList.foldlM (init := []) fun acc sg =>
        return acc ++ (← splitBools sg.mvarId)
  return [g]

open Lean Meta Elab Tactic in
elab "kanon_bools" : tactic => liftMetaTactic splitBools

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
elab "kanon_bool_vars" : tactic => liftMetaTactic splitBoolVars

/-- Proves overflow facts: splits the flags, and reasons on integers. -/
macro "kanon_ovf" : tactic => `(tactic| (
  kanon_bools
  all_goals (try simp_all)
  all_goals (repeat' (first | apply And.intro | intro))
  all_goals kanon_split
  all_goals kanon_ovf_eqs
  all_goals (try simp only [sadd_ok, ssub_ok, smul_ok, uadd_ok, usub_ok, umul_ok] at *)
  all_goals kanon_split
  all_goals kanon_bounds
  all_goals (try push_cast at *)
  all_goals (try simp only [Int.natCast_pow, Int.natCast_ofNat] at *)
  all_goals omega))

end Kanon.Lib
