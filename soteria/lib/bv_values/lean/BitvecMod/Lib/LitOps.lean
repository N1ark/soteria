import BitvecMod.Prim
import BitvecMod.Lib.Attr

/-!
# The operations on literals

The primitives `Prim.lit_add`, …, on the integers of the bit-vector literals
(in `[0, 2 ^ n)`), are the operations of `BitVec` on their values, at the width
`n` of their first operand (`ofInt_lit_*`); their results are in range
(`lit_*_nonneg`, `lit_*_lt`).
-/

namespace BitvecMod.Lib

open Prim

theorem masked_nonneg (w z : Int) : 0 ≤ masked w z :=
  Int.emod_nonneg _ (Int.ne_of_gt (Int.pow_pos (by decide)))

theorem masked_lt (w z : Int) : masked w z < 2 ^ w.toNat :=
  Int.emod_lt_of_pos _ (Int.pow_pos (by decide))

theorem ofInt_masked {n : Nat} {w : Int} (h : w = n) (z : Int) :
    BitVec.ofInt n (masked w z) = BitVec.ofInt n z := by
  subst h
  apply BitVec.eq_of_toNat_eq
  simp [masked, BitVec.toNat_ofInt]

section
variable {n : Nat}

theorem ofInt_lit_add (a b : Int) :
    BitVec.ofInt n (lit_add n a b) = BitVec.ofInt n a + BitVec.ofInt n b := by
  rw [lit_add, ofInt_masked rfl, BitVec.ofInt_add]

theorem ofInt_lit_mul (a b : Int) :
    BitVec.ofInt n (lit_mul n a b) = BitVec.ofInt n a * BitVec.ofInt n b := by
  rw [lit_mul, ofInt_masked rfl, BitVec.ofInt_mul]

theorem ofInt_lit_neg (a : Int) : BitVec.ofInt n (lit_neg n a) = -BitVec.ofInt n a := by
  rw [lit_neg, ofInt_masked rfl, BitVec.ofInt_neg]

theorem ofInt_lit_sub (a b : Int) :
    BitVec.ofInt n (lit_sub n a b) = BitVec.ofInt n a - BitVec.ofInt n b := by
  rw [lit_sub, ofInt_masked rfl, Int.sub_eq_add_neg, BitVec.ofInt_add, BitVec.ofInt_neg,
    BitVec.sub_eq_add_neg]

theorem ofInt_lit_not (a : Int) : BitVec.ofInt n (lit_not n a) = ~~~BitVec.ofInt n a := by
  rw [lit_not, ofInt_masked rfl, BitVec.not_eq_neg_add]
  simp only [zlognot, Int.sub_eq_add_neg, BitVec.sub_eq_add_neg, BitVec.ofInt_add, BitVec.ofInt_neg]
  rw [BitVec.ofInt_ofNat]

end

/-! ## Bitwise operations and shifts -/

theorem masked_eq_toNat {n : Nat} (z : Int) :
    masked (n : Int) z = ((BitVec.ofInt n z).toNat : Int) := by
  have e : ((2 ^ n : Nat) : Int) = (2 : Int) ^ n := by push_cast; rfl
  have h2 : (0 : Int) < 2 ^ n := Int.pow_pos (by decide)
  rw [BitVec.toNat_ofInt, e, masked, Int.toNat_natCast]
  exact (Int.toNat_of_nonneg (Int.emod_nonneg _ (by omega))).symm

theorem ofInt_two_pow {n : Nat} (k : Nat) : BitVec.ofInt n ((2 : Int) ^ k) = BitVec.twoPow n k := by
  rw [← BitVec.toNat_inj, BitVec.toNat_twoPow]; norm_cast

theorem ofInt_masked_toNat {n : Nat} (z : Int) :
    BitVec.ofInt n ((BitVec.ofInt n z).toNat : Int) = BitVec.ofInt n z := by
  rw [BitVec.ofInt_natCast, BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem zasr_natCast (p k : Nat) : zasr (p : Int) (k : Int) = ((p / 2 ^ k : Nat) : Int) := by
  simp only [zasr, Int.toNat_natCast]; norm_cast

theorem sext_of_eq {n : Nat} (hn : 0 < n) (z : Int) :
    sext_of (n : Int) z = (BitVec.ofInt n z).toInt := by
  have h2 : ((2 : Int) ^ n + 1) / 2 = 2 ^ (n - 1) := by
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    simp only [Nat.add_sub_cancel, Int.pow_succ]; omega
  have h3 : (2 : Int) ^ n = 2 * 2 ^ (n - 1) := by
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    simp only [Nat.add_sub_cancel, Int.pow_succ]; omega
  have e : ((2 ^ n : Nat) : Int) = (2 : Int) ^ n := by push_cast; rfl
  simp only [sext_of, signed_extract, zasr, Int.toNat_zero, Int.pow_zero, Int.ediv_one,
    Int.toNat_natCast, BitVec.toInt_ofInt, Int.bmod, e, h2]
  split <;> split <;> omega

theorem shiftRight_big {X : Int} {n k : Nat} (hn : 0 < n) (hk : n ≤ k)
    (h0 : -2 ^ (n - 1) ≤ X) (h1 : X < 2 ^ (n - 1)) : X >>> k = if X < 0 then -1 else 0 := by
  have hp : (2 : Int) ^ (n - 1) ≤ 2 ^ k := by
    have := Nat.pow_le_pow_right (by omega : 0 < 2) (by omega : n - 1 ≤ k)
    exact_mod_cast this
  have hpos : (0 : Int) < 2 ^ k := Int.pow_pos (by decide)
  rw [Int.shiftRight_eq_div_pow]
  push_cast
  split
  · exact ((Int.ediv_emod_unique (a := X) (b := 2 ^ k) (q := -1) (r := X + 2 ^ k) hpos).2
      ⟨by omega, by omega, by omega⟩).1
  · exact Int.ediv_eq_zero_of_lt (by omega) (by omega)

section
variable {n : Nat}

theorem ofInt_lit_and {a b : Int} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    BitVec.ofInt n (lit_and n a b) = BitVec.ofInt n a &&& BitVec.ofInt n b := by
  obtain ⟨p, rfl⟩ := Int.eq_ofNat_of_zero_le ha
  obtain ⟨q, rfl⟩ := Int.eq_ofNat_of_zero_le hb
  rw [lit_and, ofInt_masked rfl]
  apply BitVec.eq_of_toNat_eq
  simp only [z_land, BitVec.toNat_ofInt, BitVec.toNat_and, Int.ofNat_eq_natCast]
  rw [← Int.natCast_emod, ← Int.natCast_emod, ← Int.natCast_emod, Int.toNat_natCast,
    Int.toNat_natCast, Int.toNat_natCast, Nat.and_mod_two_pow]

theorem ofInt_lit_or {a b : Int} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    BitVec.ofInt n (lit_or n a b) = BitVec.ofInt n a ||| BitVec.ofInt n b := by
  obtain ⟨p, rfl⟩ := Int.eq_ofNat_of_zero_le ha
  obtain ⟨q, rfl⟩ := Int.eq_ofNat_of_zero_le hb
  rw [lit_or, ofInt_masked rfl]
  apply BitVec.eq_of_toNat_eq
  simp only [zlor, BitVec.toNat_ofInt, BitVec.toNat_or, Int.ofNat_eq_natCast]
  rw [← Int.natCast_emod, ← Int.natCast_emod, ← Int.natCast_emod, Int.toNat_natCast,
    Int.toNat_natCast, Int.toNat_natCast, Nat.or_mod_two_pow]

theorem ofInt_lit_xor {a b : Int} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    BitVec.ofInt n (lit_xor n a b) = BitVec.ofInt n a ^^^ BitVec.ofInt n b := by
  obtain ⟨p, rfl⟩ := Int.eq_ofNat_of_zero_le ha
  obtain ⟨q, rfl⟩ := Int.eq_ofNat_of_zero_le hb
  rw [lit_xor, ofInt_masked rfl]
  apply BitVec.eq_of_toNat_eq
  simp only [zlxor, BitVec.toNat_ofInt, BitVec.toNat_xor, Int.ofNat_eq_natCast]
  rw [← Int.natCast_emod, ← Int.natCast_emod, ← Int.natCast_emod, Int.toNat_natCast,
    Int.toNat_natCast, Int.toNat_natCast, Nat.xor_mod_two_pow]

theorem ofInt_lit_shl (a b : Int) :
    BitVec.ofInt n (lit_shl n a b) = BitVec.ofInt n a <<< BitVec.ofInt n b := by
  unfold lit_shl shift_amount
  simp only [masked_eq_toNat]
  rw [BitVec.shiftLeft_eq']
  by_cases hlt : (BitVec.ofInt n b).toNat < n
  · have h1 : ((BitVec.ofInt n b).toNat : Int) < n := by omega
    simp only [h1, ite_true]
    rw [ofInt_masked_toNat]
    simp only [z_lsl, Int.toNat_natCast]
    rw [BitVec.ofInt_mul, ofInt_two_pow, BitVec.shiftLeft_eq_mul_twoPow]
  · have h1 : ¬ ((BitVec.ofInt n b).toNat : Int) < n := by omega
    simp only [h1, ite_false]
    rw [ofInt_masked_toNat, BitVec.shiftLeft_eq_zero (by omega)]
    simp

theorem ofInt_lit_lshr {a : Int} (ha0 : 0 ≤ a) (ha1 : a < 2 ^ n) (b : Int) :
    BitVec.ofInt n (lit_lshr n a b) = BitVec.ofInt n a >>> BitVec.ofInt n b := by
  obtain ⟨p, rfl⟩ := Int.eq_ofNat_of_zero_le ha0
  have hp : p < 2 ^ n := by exact_mod_cast ha1
  unfold lit_lshr shift_amount
  simp only [masked_eq_toNat]
  rw [BitVec.ushiftRight_eq']
  have hx : (BitVec.ofInt n (p : Int)).toNat = p := by
    rw [BitVec.ofInt_natCast, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hp]
  by_cases hlt : (BitVec.ofInt n b).toNat < n
  · have h1 : ((BitVec.ofInt n b).toNat : Int) < n := by omega
    simp only [h1, ite_true]
    rw [ofInt_masked_toNat, zasr_natCast]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, hx, BitVec.ofInt_natCast, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hp), Nat.shiftRight_eq_div_pow]
  · have h1 : ¬ ((BitVec.ofInt n b).toNat : Int) < n := by omega
    simp only [h1, ite_false]
    rw [ofInt_masked_toNat, BitVec.ushiftRight_eq_zero (by omega)]
    simp

theorem ofInt_lit_ashr (hn : 0 < n) (a b : Int) :
    BitVec.ofInt n (lit_ashr n a b) =
      (BitVec.ofInt n a).sshiftRight' (BitVec.ofInt n b) := by
  unfold lit_ashr shift_amount
  simp only [masked_eq_toNat, sext_of_eq hn]
  show _ = BitVec.ofInt n ((BitVec.ofInt n a).toInt >>> (BitVec.ofInt n b).toNat)
  by_cases hlt : (BitVec.ofInt n b).toNat < n
  · have h1 : ((BitVec.ofInt n b).toNat : Int) < n := by omega
    simp only [h1, ite_true]
    rw [ofInt_masked_toNat, zasr, Int.toNat_natCast, Int.shiftRight_eq_div_pow]
    push_cast; rfl
  · have h1 : ¬ ((BitVec.ofInt n b).toNat : Int) < n := by omega
    simp only [h1, ite_false]
    rw [ofInt_masked_toNat, shiftRight_big hn (by omega) (BitVec.le_toInt _) BitVec.toInt_lt]

theorem ofInt_lit_udiv {a : Int} (ha0 : 0 ≤ a) (ha1 : a < 2 ^ n) (b : Int) :
    BitVec.ofInt n (lit_udiv n a b) = (BitVec.ofInt n a).smtUDiv (BitVec.ofInt n b) := by
  obtain ⟨p, rfl⟩ := Int.eq_ofNat_of_zero_le ha0
  have hp : p < 2 ^ n := by exact_mod_cast ha1
  unfold lit_udiv
  simp only [masked_eq_toNat]
  have hx : BitVec.ofInt n (p : Int) = BitVec.ofNat n p := BitVec.ofInt_natCast _ _
  have hxn : (BitVec.ofNat n p).toNat = p := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hp]
  generalize BitVec.ofInt n b = y
  rw [hx, BitVec.smtUDiv_eq]
  by_cases hy : y = 0#n
  · subst hy
    simp only [BitVec.toNat_zero, Int.natCast_zero, ite_true, ofInt_masked_toNat]
    rw [BitVec.ofInt_neg, BitVec.ofInt_ofNat, BitVec.neg_one_eq_allOnes]
  · have h0 : (y.toNat : Int) ≠ 0 := by
      intro h; apply hy; apply BitVec.eq_of_toNat_eq; simpa using h
    simp only [h0, hy, ite_false, ofInt_masked_toNat]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_udiv, hxn, BitVec.toNat_ofInt]
    have e : tdiv (p : Int) (y.toNat : Int) = ((p / y.toNat : Nat) : Int) := rfl
    rw [e, ← Int.natCast_emod, Int.toNat_natCast,
      Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hp)]

end

section
variable {w : Int}

theorem lit_add_nonneg (a b : Int) : 0 ≤ lit_add w a b := masked_nonneg _ _
theorem lit_add_lt (a b : Int) : lit_add w a b < 2 ^ w.toNat := masked_lt _ _
theorem lit_sub_nonneg (a b : Int) : 0 ≤ lit_sub w a b := masked_nonneg _ _
theorem lit_sub_lt (a b : Int) : lit_sub w a b < 2 ^ w.toNat := masked_lt _ _
theorem lit_mul_nonneg (a b : Int) : 0 ≤ lit_mul w a b := masked_nonneg _ _
theorem lit_mul_lt (a b : Int) : lit_mul w a b < 2 ^ w.toNat := masked_lt _ _
theorem lit_and_nonneg (a b : Int) : 0 ≤ lit_and w a b := masked_nonneg _ _
theorem lit_and_lt (a b : Int) : lit_and w a b < 2 ^ w.toNat := masked_lt _ _
theorem lit_or_nonneg (a b : Int) : 0 ≤ lit_or w a b := masked_nonneg _ _
theorem lit_or_lt (a b : Int) : lit_or w a b < 2 ^ w.toNat := masked_lt _ _
theorem lit_xor_nonneg (a b : Int) : 0 ≤ lit_xor w a b := masked_nonneg _ _
theorem lit_xor_lt (a b : Int) : lit_xor w a b < 2 ^ w.toNat := masked_lt _ _
theorem lit_neg_nonneg (a : Int) : 0 ≤ lit_neg w a := masked_nonneg _ _
theorem lit_neg_lt (a : Int) : lit_neg w a < 2 ^ w.toNat := masked_lt _ _
theorem lit_not_nonneg (a : Int) : 0 ≤ lit_not w a := masked_nonneg _ _
theorem lit_not_lt (a : Int) : lit_not w a < 2 ^ w.toNat := masked_lt _ _
theorem lit_shl_nonneg (a b : Int) : 0 ≤ lit_shl w a b := by
  unfold lit_shl; split <;> exact masked_nonneg _ _
theorem lit_shl_lt (a b : Int) : lit_shl w a b < 2 ^ w.toNat := by
  unfold lit_shl; split <;> exact masked_lt _ _
theorem lit_lshr_nonneg (a b : Int) : 0 ≤ lit_lshr w a b := by
  unfold lit_lshr; split <;> exact masked_nonneg _ _
theorem lit_lshr_lt (a b : Int) : lit_lshr w a b < 2 ^ w.toNat := by
  unfold lit_lshr; split <;> exact masked_lt _ _
theorem lit_ashr_nonneg (a b : Int) : 0 ≤ lit_ashr w a b := by
  unfold lit_ashr; split <;> exact masked_nonneg _ _
theorem lit_ashr_lt (a b : Int) : lit_ashr w a b < 2 ^ w.toNat := by
  unfold lit_ashr; split <;> exact masked_lt _ _
theorem lit_udiv_nonneg (a b : Int) : 0 ≤ lit_udiv w a b := by
  unfold lit_udiv; dsimp only; split <;> exact masked_nonneg _ _
theorem lit_udiv_lt (a b : Int) : lit_udiv w a b < 2 ^ w.toNat := by
  unfold lit_udiv; dsimp only; split <;> exact masked_lt _ _

end

/-! At a natural width (`bv_nat_widths`). -/

section
variable {w : Nat}

theorem masked_lt_nat (z : Int) : masked (w : Int) z < 2 ^ w := by
  simpa using masked_lt (w : Int) z
theorem lit_add_lt_nat (a b : Int) : lit_add (w : Int) a b < 2 ^ w := masked_lt_nat _
theorem lit_sub_lt_nat (a b : Int) : lit_sub (w : Int) a b < 2 ^ w := masked_lt_nat _
theorem lit_mul_lt_nat (a b : Int) : lit_mul (w : Int) a b < 2 ^ w := masked_lt_nat _
theorem lit_and_lt_nat (a b : Int) : lit_and (w : Int) a b < 2 ^ w := masked_lt_nat _
theorem lit_or_lt_nat (a b : Int) : lit_or (w : Int) a b < 2 ^ w := masked_lt_nat _
theorem lit_xor_lt_nat (a b : Int) : lit_xor (w : Int) a b < 2 ^ w := masked_lt_nat _
theorem lit_neg_lt_nat (a : Int) : lit_neg (w : Int) a < 2 ^ w := masked_lt_nat _
theorem lit_not_lt_nat (a : Int) : lit_not (w : Int) a < 2 ^ w := masked_lt_nat _
theorem lit_shl_lt_nat (a b : Int) : lit_shl (w : Int) a b < 2 ^ w := by
  simpa using lit_shl_lt (w := (w : Int)) a b
theorem lit_lshr_lt_nat (a b : Int) : lit_lshr (w : Int) a b < 2 ^ w := by
  simpa using lit_lshr_lt (w := (w : Int)) a b
theorem lit_ashr_lt_nat (a b : Int) : lit_ashr (w : Int) a b < 2 ^ w := by
  simpa using lit_ashr_lt (w := (w : Int)) a b
theorem lit_udiv_lt_nat (a b : Int) : lit_udiv (w : Int) a b < 2 ^ w := by
  simpa using lit_udiv_lt (w := (w : Int)) a b

end

attribute [bv_ofInt] ofInt_lit_add ofInt_lit_sub ofInt_lit_mul ofInt_lit_neg ofInt_lit_not
  ofInt_lit_and ofInt_lit_or ofInt_lit_xor ofInt_lit_shl ofInt_lit_lshr ofInt_lit_ashr
  ofInt_lit_udiv

attribute [bv_range] masked_nonneg masked_lt lit_add_nonneg lit_add_lt lit_sub_nonneg lit_sub_lt
  lit_mul_nonneg lit_mul_lt lit_and_nonneg lit_and_lt lit_or_nonneg lit_or_lt lit_xor_nonneg
  lit_xor_lt lit_neg_nonneg lit_neg_lt lit_not_nonneg lit_not_lt masked_lt_nat lit_add_lt_nat
  lit_sub_lt_nat lit_mul_lt_nat lit_and_lt_nat lit_or_lt_nat lit_xor_lt_nat lit_neg_lt_nat
  lit_not_lt_nat lit_shl_nonneg lit_shl_lt lit_lshr_nonneg lit_lshr_lt lit_ashr_nonneg lit_ashr_lt
  lit_shl_lt_nat lit_lshr_lt_nat lit_ashr_lt_nat lit_udiv_nonneg lit_udiv_lt lit_udiv_lt_nat

end BitvecMod.Lib
