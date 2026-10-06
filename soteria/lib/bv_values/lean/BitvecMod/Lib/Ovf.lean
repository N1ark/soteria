import BitvecMod.Lib.Tactic

/-!
# Overflows and literals in range

The lemmas that the tactics of several families of rules share (`Lib/Arith.lean`,
`Lib/Compare.lean`, `Lib/Eq.lean`, `Lib/Resize.lean`):

- the helpers of the rules on overflows (`to_z`, `min_for`, `max_for`, `overflows_*`,
  `is_int_min`) on literals in range, as the operations of `BitVec`;
- integers modulo powers of two;
- the overflow flags of `BitVec` through integers (`sadd_ok`, …, `toInt_add_ok`, …, and
  `ovfEqs`, which adds the latter for the hypotheses of the context).
-/

namespace BitvecMod.Lib

open Classical Kanon Prim

set_option linter.unusedSectionVars false

theorem two_pow_pos (n : Nat) : (0 : Int) < 2 ^ n := Int.pow_pos (by decide)


/-- The integer that a bit-vector stands for, in a signedness. -/
abbrev iv (s : Bool) {w : Nat} (x : BitVec w) : Int := if s then x.toInt else x.toNat

theorem zasr_zero (z : Int) : zasr z 0 = z := by simp [zasr]

theorem signed_extract_zero {n : Nat} (hn : 0 < n) (z : Int) :
    signed_extract z 0 (n : Int) = (BitVec.ofInt n z).toInt := by
  have h2 : ((2 : Int) ^ n + 1) / 2 = 2 ^ (n - 1) := by
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    simp only [Nat.add_sub_cancel, Int.pow_succ]; omega
  have e : ((2 ^ n : Nat) : Int) = (2 : Int) ^ n := by push_cast; rfl
  simp only [signed_extract, zasr_zero, Int.toNat_natCast, BitVec.toInt_ofInt, Int.bmod, e, h2]
  split <;> split <;> omega

theorem z_lsl_one (k : Int) : z_lsl 1 k = 2 ^ k.toNat := by simp [z_lsl]

section
variable {S : Kanon.Sem} [DecidableEq S.Term] [DecidableEq S.Ty] {B : Kanon.Base S}
  {LBool : KanonBool.Syntax B} {LCore : CoreMod.Syntax B} {L : Syntax B LBool LCore}
  [KanonBool.Sem LBool] [CoreMod.Sem LCore] [Sem L]

theorem to_z_ofInt {n : Nat} (hn : 0 < n) (s : Bool) {z : Int} (h0 : 0 ≤ z) (h1 : z < 2 ^ n) :
    L.bitvec_to_z s (n : Int) z = iv s (BitVec.ofInt n z) := by
  rw [L.bitvec_to_z_eq, Sem.signed_extract_eq]
  cases s
  · have e : ((2 ^ n : Nat) : Int) = (2 : Int) ^ n := by push_cast; rfl
    simp only [iv, Bool.false_eq_true, ite_false, BitVec.toNat_ofInt, e, Int.emod_eq_of_lt h0 h1]
    omega
  · simp only [iv, ite_true, signed_extract_zero hn]

theorem min_for_true {n : Nat} (hn : 0 < n) : L.bitvec_min_for true n = -2 ^ (n - 1) := by
  simp only [L.bitvec_min_for_eq, Sem.z_lsl_eq, z_lsl_one, ite_true]; congr 2; omega

theorem max_for_true {n : Nat} (hn : 0 < n) : L.bitvec_max_for true n = 2 ^ (n - 1) - 1 := by
  simp only [L.bitvec_max_for_eq, Sem.z_lsl_eq, z_lsl_one, ite_true]; congr 2; omega

theorem min_for_false (n : Int) : L.bitvec_min_for false n = 0 := by
  rw [L.bitvec_min_for_eq]; rfl

theorem max_for_false (n : Nat) : L.bitvec_max_for false n = 2 ^ n - 1 := by
  simp [L.bitvec_max_for_eq, Sem.z_lsl_eq, z_lsl_one]

section
variable {n : Nat} (hn : 0 < n)
include hn

theorem overflows_add_ofInt (s : Bool) {l r : Int} (hl0 : 0 ≤ l) (hl1 : l < 2 ^ n) (hr0 : 0 ≤ r)
    (hr1 : r < 2 ^ n) :
    L.bitvec_overflows_add s n l r =
      if s then (BitVec.ofInt n l).saddOverflow (BitVec.ofInt n r)
      else (BitVec.ofInt n l).uaddOverflow (BitVec.ofInt n r) := by
  rw [L.bitvec_overflows_add_eq, to_z_ofInt hn _ hl0 hl1, to_z_ofInt hn _ hr0 hr1]
  cases s
  · simp only [iv, min_for_false, max_for_false, BitVec.uaddOverflow, BitVec.toNat_ofInt]
    rw [Bool.eq_iff_iff]; simp [Int.emod_eq_of_lt hl0 hl1, Int.emod_eq_of_lt hr0 hr1]
    have e : ((2 ^ n : Nat) : Int) = (2 : Int) ^ n := by push_cast; rfl
    omega
  · have := BitVec.le_toInt (BitVec.ofInt n l); have := BitVec.toInt_lt (x := BitVec.ofInt n l)
    simp only [min_for_true hn, max_for_true hn, BitVec.saddOverflow, iv, ite_true]
    rw [Bool.eq_iff_iff]; simp; omega

theorem overflows_sub_ofInt (s : Bool) {l r : Int} (hl0 : 0 ≤ l) (hl1 : l < 2 ^ n) (hr0 : 0 ≤ r)
    (hr1 : r < 2 ^ n) :
    L.bitvec_overflows_sub s n l r =
      if s then (BitVec.ofInt n l).ssubOverflow (BitVec.ofInt n r)
      else (BitVec.ofInt n l).usubOverflow (BitVec.ofInt n r) := by
  rw [L.bitvec_overflows_sub_eq, to_z_ofInt hn _ hl0 hl1, to_z_ofInt hn _ hr0 hr1]
  cases s
  · simp only [iv, min_for_false, max_for_false, BitVec.usubOverflow, BitVec.toNat_ofInt]
    rw [Bool.eq_iff_iff]; simp [Int.emod_eq_of_lt hl0 hl1, Int.emod_eq_of_lt hr0 hr1]
    push_cast at *; omega
  · have := BitVec.le_toInt (BitVec.ofInt n l); have := BitVec.toInt_lt (x := BitVec.ofInt n l)
    simp only [min_for_true hn, max_for_true hn, BitVec.ssubOverflow, iv, ite_true]
    rw [Bool.eq_iff_iff]; simp; omega

theorem overflows_mul_ofInt (s : Bool) {l r : Int} (hl0 : 0 ≤ l) (hl1 : l < 2 ^ n) (hr0 : 0 ≤ r)
    (hr1 : r < 2 ^ n) :
    L.bitvec_overflows_mul s n l r =
      if s then (BitVec.ofInt n l).smulOverflow (BitVec.ofInt n r)
      else (BitVec.ofInt n l).umulOverflow (BitVec.ofInt n r) := by
  rw [L.bitvec_overflows_mul_eq, to_z_ofInt hn _ hl0 hl1, to_z_ofInt hn _ hr0 hr1]
  cases s
  · obtain ⟨l, rfl⟩ := Int.eq_ofNat_of_zero_le hl0
    obtain ⟨r, rfl⟩ := Int.eq_ofNat_of_zero_le hr0
    have e : ((2 ^ n : Nat) : Int) = (2 : Int) ^ n := by push_cast; rfl
    simp only [min_for_false, max_for_false, BitVec.umulOverflow, BitVec.toNat_ofInt, iv,
      Bool.false_eq_true, ite_false, e, Int.emod_eq_of_lt (Int.natCast_nonneg l) hl1,
      Int.emod_eq_of_lt (Int.natCast_nonneg r) hr1, Int.toNat_natCast]
    rw [Bool.eq_iff_iff]
    simp only [Bool.or_eq_true, decide_eq_true_eq]
    have : (0 : Int) ≤ l * r := Int.mul_nonneg (Int.natCast_nonneg l) (Int.natCast_nonneg r)
    have e2 : ((l * r : Nat) : Int) = (l : Int) * r := by push_cast; rfl
    rw [← e2] at *
    omega
  · simp only [min_for_true hn, max_for_true hn, BitVec.smulOverflow, iv, ite_true]
    rw [Bool.eq_iff_iff]; simp; omega

theorem is_int_min_ofInt {z : Int} (h0 : 0 ≤ z) (h1 : z < 2 ^ n) :
    L.bitvec_is_int_min n z = decide (BitVec.ofInt n z = BitVec.intMin n) := by
  rw [L.bitvec_is_int_min_eq, to_z_ofInt hn _ h0 h1, min_for_true hn]
  rw [← BitVec.toInt_intMin_of_pos hn]
  simp only [iv, ite_true, BitVec.toInt_inj]

end

theorem asTBitVector_TBool : L.asTBitVector LBool.TBool = none := by
  cases h : L.asTBitVector LBool.TBool with
  | none => rfl
  | some m => exact absurd (L.asTBitVector_sound _ _ h).symm (L.TBitVector_ne_TBool m)

end

/-! ## Integers modulo powers of two -/

theorem ofInt_emod_two_pow (n : Nat) (z : Int) :
    BitVec.ofInt n (z % 2 ^ n) = BitVec.ofInt n z := by
  apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_ofInt]

theorem emod_two_pow_nonneg (z : Int) (n : Nat) : 0 ≤ z % 2 ^ n :=
  Int.emod_nonneg _ (Int.ne_of_gt (Int.pow_pos (by decide)))

theorem emod_two_pow_lt (z : Int) (n : Nat) : z % 2 ^ n < 2 ^ n :=
  Int.emod_lt_of_pos _ (Int.pow_pos (by decide))

theorem toNat_ofInt_of_lt {n : Nat} {k : Int} (h0 : 0 ≤ k) (h1 : k < 2 ^ n) :
    (BitVec.ofInt n k).toNat = k.toNat := by
  rw [BitVec.toNat_ofInt, Int.emod_eq_of_lt h0 (by push_cast; exact h1)]

theorem emod_two_pow_of_lt {n : Nat} {k : Int} (h0 : 0 ≤ k) (h1 : k < 2 ^ n) :
    k % 2 ^ n = k := Int.emod_eq_of_lt h0 h1

theorem smtUDiv_toNat {n : Nat} {a b : BitVec n} (hb : b.toNat ≠ 0) :
    (a.smtUDiv b).toNat = a.toNat / b.toNat := by
  simp [BitVec.smtUDiv_eq, ← BitVec.toNat_inj, hb]

theorem popcountNat_eq_zero : ∀ {m : Nat}, popcountNat m = 0 → m = 0
  | 0, _ => rfl
  | k + 1, h => by
      rw [popcountNat] at h
      have : (k + 1) / 2 < k + 1 := by omega
      have := popcountNat_eq_zero (m := (k + 1) / 2) (by omega)
      omega

theorem popcountNat_eq_one : ∀ {m : Nat}, popcountNat m = 1 → ∃ j, m = 2 ^ j
  | 0, h => by simp [popcountNat] at h
  | k + 1, h => by
      rw [popcountNat] at h
      have : (k + 1) / 2 < k + 1 := by omega
      by_cases hm : (k + 1) % 2 = 1
      · have := popcountNat_eq_zero (m := (k + 1) / 2) (by omega)
        exact ⟨0, by omega⟩
      · obtain ⟨j, hj⟩ := popcountNat_eq_one (m := (k + 1) / 2) (by omega)
        exact ⟨j + 1, by rw [Nat.pow_succ]; omega⟩

/-! ## Overflows, through integers -/

theorem ovf_comm {n : Nat} (x y : BitVec n) : (x.saddOverflow y = y.saddOverflow x) ∧
    (x.uaddOverflow y = y.uaddOverflow x) ∧ (x.smulOverflow y = y.smulOverflow x) ∧
    (x.umulOverflow y = y.umulOverflow x) := by
  simp [BitVec.saddOverflow, BitVec.uaddOverflow, BitVec.smulOverflow,
    BitVec.umulOverflow, Int.add_comm, Nat.add_comm, Int.mul_comm, Nat.mul_comm]

theorem ssubOverflow_zero_left {n : Nat} (hn : 0 < n) (x : BitVec n) :
    (0#n).ssubOverflow x = decide (x = BitVec.intMin n) := by
  have := BitVec.le_toInt x; have := BitVec.toInt_lt (x := x)
  rw [Bool.eq_iff_iff]
  simp [BitVec.ssubOverflow, ← BitVec.toInt_inj, BitVec.toInt_intMin_of_pos hn]; omega

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

end BitvecMod.Lib
