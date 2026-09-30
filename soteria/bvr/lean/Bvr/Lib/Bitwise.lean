import Bvr.Lib.Tactic

/-!
# Bitwise operations and shifts

The bitwise helpers of the rules, on values of known width (`ones_nat`,
`is_ones_mk`, `bits_in_mk`, `disjoint_mk`), and the `BitVec` facts behind the
rules on masks, shifts and concatenations.
-/

namespace Bvr.Lib

open Classical

/-! ## Typing of the resizing nodes

The unfolded typing conditions of concatenations and extensions, at widths
that are known. -/

@[simp] theorem exists_concat_width {a b : Int} {P : Int → Int → Prop} :
    (∃ n, 0 < n ∧ ∃ m, 0 < m ∧ a = n ∧ b = m ∧ P n m) ↔ 0 < a ∧ 0 < b ∧ P a b :=
  ⟨fun ⟨_, h0, _, h1, e1, e2, h⟩ => by subst e1 e2; exact ⟨h0, h1, h⟩,
    fun ⟨h0, h1, h⟩ => ⟨_, h0, _, h1, rfl, rfl, h⟩⟩

@[simp] theorem exists_extend_width {a : Int} {P : Int → Prop} :
    (∃ n, 0 < n ∧ a = n ∧ P n) ↔ 0 < a ∧ P a :=
  ⟨fun ⟨_, h0, e, h⟩ => by subst e; exact ⟨h0, h⟩, fun ⟨h0, h⟩ => ⟨_, h0, rfl, h⟩⟩

/-! ## Helpers -/

@[simp] theorem ones_w (n : Int) : (ones n).w = n.toNat := rfl

@[simp] theorem ones_nat (n : Nat) : ones n = ⟨n, BitVec.allOnes n⟩ := by
  have : BitVec.ofInt n 0 = 0#n := by simp
  simp only [ones, lit_not, of_z_nat, bv_equal_mk, this]
  exact BitVec.not_zero

theorem is_ones_mk {n : Nat} (hn : 0 < n) (x : BitVec n) :
    is_ones ⟨n, x⟩ = decide (x = BitVec.allOnes n) := by
  have e : (BitVec.allOnes n).toInt = -1 := by simp [BitVec.toInt_allOnes, hn]
  simp only [is_ones, to_z_mk, ite_true, ← e, BitVec.toInt_inj]

@[simp] theorem bits_in_mk {n : Nat} (x y : BitVec n) :
    bits_in ⟨n, x⟩ ⟨n, y⟩ = decide (x &&& y = x) := by
  simp only [bits_in, lit_and_mk, to_z_mk, Bool.false_eq_true, ite_false, Int.natCast_inj,
    BitVec.toNat_inj]

@[simp] theorem disjoint_mk {n : Nat} (x y : BitVec n) :
    disjoint ⟨n, x⟩ ⟨n, y⟩ = decide (x &&& y = 0) := by
  simp only [disjoint, lit_and_mk, to_z_mk, Bool.false_eq_true, ite_false, Int.natCast_eq_zero,
    ← BitVec.toNat_inj]
  rfl

/-! ## Masks -/

section
variable {w : Nat}

theorem bit_of_eq {x y : BitVec w} (h : x = y) (i : Nat) (hi : i < w) : x[i] = y[i] := by rw [h]

theorem and_or_of_disjoint {m n : BitVec w} (h : m &&& n = 0) (v : BitVec w) :
    m &&& (v ||| n) = v &&& m := by
  ext i hi; have := bit_of_eq h i hi; simp at this ⊢; grind

theorem lshr_and_of_bits_in {s : Nat} {m : BitVec w}
    (h : BitVec.allOnes w >>> s &&& m = BitVec.allOnes w >>> s) (x : BitVec w) :
    x >>> s &&& m = x >>> s := by
  ext i hi; have := bit_of_eq h i hi
  simp [BitVec.getLsbD_allOnes] at this ⊢
  by_cases hs : s + i < w
  · grind
  · simp [BitVec.getLsbD_of_ge x (s + i) (by omega)]

/-! ## Shifts -/

theorem shl_shl (x : BitVec w) (a b : Nat) : x <<< a <<< b = x <<< min (a + b) w := by
  rw [← BitVec.shiftLeft_add]
  by_cases h : a + b ≤ w
  · rw [Nat.min_eq_left h]
  · rw [Nat.min_eq_right (by omega), BitVec.shiftLeft_eq_zero (by omega),
      BitVec.shiftLeft_eq_zero (by omega)]

theorem lshr_lshr (x : BitVec w) (a b : Nat) : x >>> a >>> b = x >>> min (a + b) w := by
  rw [← BitVec.shiftRight_add]
  by_cases h : a + b ≤ w
  · rw [Nat.min_eq_left h]
  · rw [Nat.min_eq_right (by omega), BitVec.ushiftRight_eq_zero (by omega),
      BitVec.ushiftRight_eq_zero (by omega)]

theorem ashr_of_ge (x : BitVec w) {a : Nat} (h : w - 1 ≤ a) :
    x.sshiftRight a = x.sshiftRight (w - 1) := by
  ext i hi
  simp only [BitVec.getElem_sshiftRight]
  by_cases h1 : a + i < w
  · obtain ⟨rfl, rfl⟩ : i = 0 ∧ a = w - 1 := by omega
    rfl
  · by_cases h2 : w - 1 + i < w
    · obtain rfl : i = 0 := by omega
      have ha : ¬ a < w := by omega
      simp [ha, BitVec.msb_eq_getLsbD_last]
      intro h; rw [BitVec.getLsbD_eq_getElem h]
    · simp [h1, h2]

theorem ashr_ashr (x : BitVec w) (a b : Nat) :
    (x.sshiftRight a).sshiftRight b = x.sshiftRight (min (a + b) (w - 1)) := by
  rw [← BitVec.sshiftRight_add]
  by_cases h : a + b ≤ w - 1
  · rw [Nat.min_eq_left h]
  · rw [Nat.min_eq_right (by omega), ashr_of_ge x (by omega)]

theorem lshr_shl_le (x : BitVec w) {a b : Nat} (h : b ≤ a) :
    x >>> a <<< b = x >>> (a - b) &&& BitVec.allOnes w <<< b := by
  ext i hi
  simp only [BitVec.getElem_shiftLeft, BitVec.getElem_and, BitVec.getElem_ushiftRight,
    BitVec.getElem_allOnes]
  by_cases hb : i < b
  · simp [hb]
  · simp only [hb, decide_false, Bool.not_false, Bool.true_and, Bool.and_true]
    rw [show a + (i - b) = a - b + i by omega]

theorem lshr_shl_gt (x : BitVec w) {a b : Nat} (h : a < b) :
    x >>> a <<< b = (x &&& BitVec.allOnes w <<< a) <<< (b - a) := by
  ext i hi
  simp only [BitVec.getElem_shiftLeft, BitVec.getElem_and, BitVec.getElem_ushiftRight,
    BitVec.getElem_allOnes]
  by_cases hb : i < b
  · simp [hb]; omega
  · simp only [hb, show ¬ i < b - a by omega, show ¬ i - (b - a) < a by omega, decide_false,
      Bool.not_false, Bool.true_and, Bool.and_true]
    rw [show a + (i - b) = i - (b - a) by omega, BitVec.getLsbD_eq_getElem]

end

/-! Shift amounts, as the rules compute them -/

/-- Normalizes the shift amounts of the literals, and substitutes the values. -/
macro "bvr_amounts" : tactic => `(tactic| (
  simp (disch := assumption) only [emod_two_pow_of_lt, Int.max_eq_left] at *
  subst_vars))

theorem emod_two_pow_of_le {z : Int} {n : Nat} (h0 : 0 ≤ z) (h : z ≤ n) : z % 2 ^ n = z :=
  Int.emod_eq_of_lt h0 (by
    have : ((n : Nat) : Int) < 2 ^ n := by exact_mod_cast Nat.lt_two_pow_self
    omega)

theorem zmin_emod {z m : Int} {n : Nat} (h0 : 0 ≤ z) (hm : 0 ≤ m) (hmn : m ≤ n) :
    (zmin z m % 2 ^ n).toNat = min z.toNat m.toNat := by
  simp only [zmin, decide_eq_true_eq]
  split <;> rw [emod_two_pow_of_le (by omega) (by omega)] <;> omega

theorem sub_mod_two_pow {a b n : Nat} (h : b ≤ a) (ha : (a : Int) < 2 ^ n) :
    (2 ^ n - b + a) % 2 ^ n = a - b := by
  have : a < 2 ^ n := by exact_mod_cast ha
  rw [show 2 ^ n - b + a = a - b + 2 ^ n by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]

theorem ashr_big_ok {n : Nat} (hn : 0 < n) (x : BitVec n) {s : Int} (h : n ≤ s) :
    x.sshiftRight (((n : Int) - 1) % 2 ^ n).toNat = x.sshiftRight s.toNat := by
  rw [emod_two_pow_of_le (by omega) (by omega), ashr_of_ge x (a := s.toNat) (by omega)]
  congr 1; omega

/-! ## Concatenation through a mask and a shift -/

theorem or_shl_append {nb nt n s : Nat} (xb : BitVec nb) (xt : BitVec nt) (hs : s = nb) :
    xb.setWidth n ||| xt.setWidth n <<< s = (xt ++ xb).setWidth n := by
  subst hs
  ext i hi
  simp [BitVec.getElem_shiftLeft, BitVec.getElem_setWidth, BitVec.getLsbD_append]
  by_cases h : i < s
  · simp [h]
  · simp [h]; grind

theorem setWidth_append_extract {nb nt n k : Nat} (xb : BitVec nb) (xt : BitVec nt)
    (h : n ≤ k + nb) : (xt.extractLsb' 0 k ++ xb).setWidth n = (xt ++ xb).setWidth n := by
  ext i hi
  simp [BitVec.getElem_setWidth, BitVec.getLsbD_append]
  split
  · rfl
  · simp; omega

theorem setWidth_setWidth_of_ge {w l n : Nat} (x : BitVec w) (h : w ≤ l) :
    (x.setWidth l).setWidth n = x.setWidth n := by
  ext i hi
  simp [BitVec.getElem_setWidth]
  intro h1
  have := BitVec.lt_of_getLsbD h1
  omega

/-- Proves the alternatives of the shifts on shifts. -/
macro "bvr_shift" : tactic => `(tactic| (
  bvr_rule_sem
  all_goals bvr_amounts
  all_goals first
    | exact ashr_big_ok (by omega) _ (by omega)
    | (rw [lshr_shl_le _ (by omega), sub_mod_two_pow (by omega) (by omega)]; done)
    | (rw [lshr_shl_gt _ (by omega), sub_mod_two_pow (by omega) (by omega)]; done)
    | ((first | rw [shl_shl] | rw [lshr_lshr] | rw [ashr_ashr])
       congr 1
       rw [zmin_emod (by omega) (by omega) (by omega)]; omega)))

attribute [bvr_tactic "bvr_shift"] bv_shl.spec bv_lshr.spec bv_ashr.spec

end Bvr.Lib
