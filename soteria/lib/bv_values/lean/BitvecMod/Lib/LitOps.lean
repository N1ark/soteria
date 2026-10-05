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

end

attribute [bv_ofInt] ofInt_lit_add ofInt_lit_sub ofInt_lit_mul ofInt_lit_neg ofInt_lit_not

attribute [bv_range] masked_nonneg masked_lt lit_add_nonneg lit_add_lt lit_sub_nonneg lit_sub_lt
  lit_mul_nonneg lit_mul_lt lit_and_nonneg lit_and_lt lit_or_nonneg lit_or_lt lit_xor_nonneg
  lit_xor_lt lit_neg_nonneg lit_neg_lt lit_not_nonneg lit_not_lt masked_lt_nat lit_add_lt_nat
  lit_sub_lt_nat lit_mul_lt_nat lit_and_lt_nat lit_or_lt_nat lit_xor_lt_nat lit_neg_lt_nat
  lit_not_lt_nat

end BitvecMod.Lib
