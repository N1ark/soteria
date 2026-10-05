import Kanon.Lib.Ovf
import Kanon.Model.Bitvec.is_pow2
import Kanon.Model.Bitvec.overflows_mul
import Kanon.Model.Bitvec.udivides

/-!
# The operations on literals

The primitives `lit_add`, ..., on the integers of the bit-vector literals (in
`[0, 2 ^ n)`), are the operations of `BitVec` on their values, at the width of
their first operand.
-/

namespace Kanon.Lib

open CoreMod

open Classical

theorem ofInt_masked {n : Nat} {w : Int} (h : w = n) (z : Int) :
    BitVec.ofInt n (masked w z) = BitVec.ofInt n z := by
  subst h; simp only [masked, Int.toNat_natCast]; exact BitVec.ofInt_emod_two_pow z

variable {n : Nat} in
theorem ofInt_masked_ty (z : Int) :
    BitVec.ofInt n (masked (size_of_ty (.TBitVector (n : Int))) z) = BitVec.ofInt n z :=
  ofInt_masked rfl z

theorem sext_of_eq {n : Nat} (hn : 0 < n) (z : Int) :
    sext_of (n : Int) z = (BitVec.ofInt n z).toInt := bv_to_z_true hn z

theorem sext_of_ty {n : Nat} (hn : 0 < n) (z : Int) :
    sext_of (size_of_ty (.TBitVector (n : Int))) z = (BitVec.ofInt n z).toInt := bv_to_z_true hn z

variable {n : Nat} in
theorem masked_eq_toNat (z : Int) : masked (n : Int) z = ((BitVec.ofInt n z).toNat : Int) := by
  have e : ((2 ^ n : Nat) : Int) = (2 : Int) ^ n := by push_cast; rfl
  have h2 : (0 : Int) < 2 ^ n := Int.pow_pos (by decide)
  rw [BitVec.toNat_ofInt, e, masked, Int.toNat_natCast]
  exact (Int.toNat_of_nonneg (Int.emod_nonneg _ (by omega))).symm

variable {n : Nat} in
theorem ofInt_two_pow (k : Nat) : BitVec.ofInt n ((2 : Int) ^ k) = BitVec.twoPow n k := by
  rw [← BitVec.toNat_inj, BitVec.toNat_twoPow]; norm_cast

variable {n : Nat} in
theorem ofInt_masked_toNat (z : Int) :
    BitVec.ofInt n ((BitVec.ofInt n z).toNat : Int) = BitVec.ofInt n z := by
  rw [BitVec.ofInt_natCast, BitVec.ofNat_toNat, BitVec.setWidth_eq]

variable {n : Nat} in
theorem zasr_natCast (p k : Nat) : zasr (p : Int) (k : Int) = ((p / 2 ^ k : Nat) : Int) := by
  simp only [zasr, Int.toNat_natCast]; norm_cast

variable {n : Nat} in
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

variable {n : Nat} in
theorem smtSDiv_eq_sdiv {n : Nat} {x y : BitVec n} (hy : y ≠ 0#n) : x.smtSDiv y = x.sdiv y := by
  have hny : -y ≠ 0#n := by simpa using hy
  rw [BitVec.smtSDiv, BitVec.sdiv]
  cases x.msb <;> cases y.msb <;> simp [BitVec.smtUDiv_eq, hy, hny, BitVec.udiv_eq]

theorem ofInt_neg_one' {n : Nat} : BitVec.ofInt n (-1) = BitVec.allOnes n := by
  rw [BitVec.ofInt_neg, BitVec.ofInt_ofNat, BitVec.neg_one_eq_allOnes]

theorem smod_formula (X d : Int) (hd : d ≠ 0) :
    (if (Int.tmod X d) = 0 ∨ (Int.tmod X d).sign = d.sign then Int.tmod X d else Int.tmod X d + d) = Int.fmod X d := by
  rw [Int.fmod_eq_tmod]
  have hz : d ∣ X ↔ Int.tmod X d = 0 := Int.dvd_iff_tmod_eq_zero
  have h1 : 0 ≤ X → 0 ≤ Int.tmod X d := fun h => Int.tmod_nonneg d h
  have h2 : X < 0 → Int.tmod X d ≤ 0 := fun h => by
    have := Int.tmod_nonneg d (a := -X) (by omega)
    rw [Int.neg_tmod] at this; omega
  generalize Int.tmod X d = r at *
  by_cases hdv : d ∣ X
  · have := hz.1 hdv
    simp [this, hdv]
  · have hne : r ≠ 0 := fun h => hdv (hz.2 h)
    simp only [hdv, hne, false_or, ite_false]
    rcases Int.lt_trichotomy d 0 with hneg | hzero | hpos
    · have hs : d.sign = -1 := Int.sign_eq_neg_one_iff_neg.2 hneg
      rcases Int.lt_or_le X 0 with hx | hx
      · have hr : r < 0 := by have := h2 hx; omega
        rw [Int.sign_eq_neg_one_iff_neg.2 hr, hs]
        (repeat' split) <;> omega
      · have hr : 0 < r := by have := h1 hx; omega
        rw [Int.sign_eq_one_iff_pos.2 hr, hs]
        (repeat' split) <;> omega
    · exact absurd hzero hd
    · have hs : d.sign = 1 := Int.sign_eq_one_iff_pos.2 hpos
      rcases Int.lt_or_le X 0 with hx | hx
      · have hr : r < 0 := by have := h2 hx; omega
        rw [Int.sign_eq_neg_one_iff_neg.2 hr, hs]
        (repeat' split) <;> omega
      · have hr : 0 < r := by have := h1 hx; omega
        rw [Int.sign_eq_one_iff_pos.2 hr, hs]
        (repeat' split) <;> omega

section
variable {n : Nat} {s2 : Ty}

theorem ofInt_lit_add (a b : Int) :
    BitVec.ofInt n (lit_add (.TBitVector (n : Int)) s2 a b) = BitVec.ofInt n a + BitVec.ofInt n b := by
  rw [lit_add, ofInt_masked_ty, BitVec.ofInt_add]

theorem ofInt_lit_mul (a b : Int) :
    BitVec.ofInt n (lit_mul (.TBitVector (n : Int)) s2 a b) = BitVec.ofInt n a * BitVec.ofInt n b := by
  rw [lit_mul, ofInt_masked_ty, BitVec.ofInt_mul]

theorem ofInt_lit_neg (a : Int) : BitVec.ofInt n (lit_neg (.TBitVector (n : Int)) a) = -BitVec.ofInt n a := by
  rw [lit_neg, ofInt_masked_ty, BitVec.ofInt_neg]

theorem ofInt_lit_sub (a b : Int) :
    BitVec.ofInt n (lit_sub (.TBitVector (n : Int)) s2 a b) = BitVec.ofInt n a - BitVec.ofInt n b := by
  rw [lit_sub, ofInt_masked_ty, Int.sub_eq_add_neg, BitVec.ofInt_add, BitVec.ofInt_neg,
    BitVec.sub_eq_add_neg]

theorem ofInt_lit_not (a : Int) : BitVec.ofInt n (lit_not (.TBitVector (n : Int)) a) = ~~~BitVec.ofInt n a := by
  rw [lit_not, ofInt_masked_ty, BitVec.not_eq_neg_add]
  simp only [zlognot, Int.sub_eq_add_neg, BitVec.sub_eq_add_neg, BitVec.ofInt_add, BitVec.ofInt_neg]
  rw [BitVec.ofInt_ofNat]

theorem ofInt_lit_and {a b : Int} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    BitVec.ofInt n (lit_and (.TBitVector (n : Int)) s2 a b) = BitVec.ofInt n a &&& BitVec.ofInt n b := by
  obtain ⟨p, rfl⟩ := Int.eq_ofNat_of_zero_le ha
  obtain ⟨q, rfl⟩ := Int.eq_ofNat_of_zero_le hb
  rw [lit_and, ofInt_masked_ty]
  apply BitVec.eq_of_toNat_eq
  simp only [z_land, BitVec.toNat_ofInt, BitVec.toNat_and, Int.ofNat_eq_natCast]
  rw [← Int.natCast_emod, ← Int.natCast_emod, ← Int.natCast_emod, Int.toNat_natCast, Int.toNat_natCast,
    Int.toNat_natCast, Nat.and_mod_two_pow]

theorem ofInt_lit_or {a b : Int} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    BitVec.ofInt n (lit_or (.TBitVector (n : Int)) s2 a b) = BitVec.ofInt n a ||| BitVec.ofInt n b := by
  obtain ⟨p, rfl⟩ := Int.eq_ofNat_of_zero_le ha
  obtain ⟨q, rfl⟩ := Int.eq_ofNat_of_zero_le hb
  rw [lit_or, ofInt_masked_ty]
  apply BitVec.eq_of_toNat_eq
  simp only [zlor, BitVec.toNat_ofInt, BitVec.toNat_or, Int.ofNat_eq_natCast]
  rw [← Int.natCast_emod, ← Int.natCast_emod, ← Int.natCast_emod, Int.toNat_natCast, Int.toNat_natCast,
    Int.toNat_natCast, Nat.or_mod_two_pow]

theorem ofInt_lit_xor {a b : Int} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    BitVec.ofInt n (lit_xor (.TBitVector (n : Int)) s2 a b) = BitVec.ofInt n a ^^^ BitVec.ofInt n b := by
  obtain ⟨p, rfl⟩ := Int.eq_ofNat_of_zero_le ha
  obtain ⟨q, rfl⟩ := Int.eq_ofNat_of_zero_le hb
  rw [lit_xor, ofInt_masked_ty]
  apply BitVec.eq_of_toNat_eq
  simp only [zlxor, BitVec.toNat_ofInt, BitVec.toNat_xor, Int.ofNat_eq_natCast]
  rw [← Int.natCast_emod, ← Int.natCast_emod, ← Int.natCast_emod, Int.toNat_natCast, Int.toNat_natCast,
    Int.toNat_natCast, Nat.xor_mod_two_pow]

theorem ofInt_lit_shl (a b : Int) :
    BitVec.ofInt n (lit_shl (.TBitVector (n : Int)) s2 a b) = BitVec.ofInt n a <<< BitVec.ofInt n b := by
  unfold lit_shl shift_amount
  simp only [size_of_ty, masked_eq_toNat]
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
    BitVec.ofInt n (lit_lshr (.TBitVector (n : Int)) s2 a b) = BitVec.ofInt n a >>> BitVec.ofInt n b := by
  obtain ⟨p, rfl⟩ := Int.eq_ofNat_of_zero_le ha0
  have hp : p < 2 ^ n := by exact_mod_cast ha1
  unfold lit_lshr shift_amount
  simp only [size_of_ty, masked_eq_toNat]
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
    BitVec.ofInt n (lit_ashr (.TBitVector (n : Int)) s2 a b) = (BitVec.ofInt n a).sshiftRight' (BitVec.ofInt n b) := by
  unfold lit_ashr shift_amount
  simp only [size_of_ty, masked_eq_toNat]
  simp only [sext_of_eq hn, sext_of_ty hn]
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
    BitVec.ofInt n (lit_udiv (.TBitVector (n : Int)) s2 a b) = (BitVec.ofInt n a).smtUDiv (BitVec.ofInt n b) := by
  obtain ⟨p, rfl⟩ := Int.eq_ofNat_of_zero_le ha0
  have hp : p < 2 ^ n := by exact_mod_cast ha1
  unfold lit_udiv
  simp only [size_of_ty, masked_eq_toNat]
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

theorem ofInt_lit_urem {a : Int} (ha0 : 0 ≤ a) (ha1 : a < 2 ^ n) (b : Int) :
    BitVec.ofInt n (lit_urem (.TBitVector (n : Int)) s2 a b) = BitVec.ofInt n a % BitVec.ofInt n b := by
  obtain ⟨p, rfl⟩ := Int.eq_ofNat_of_zero_le ha0
  have hp : p < 2 ^ n := by exact_mod_cast ha1
  unfold lit_urem
  simp only [size_of_ty, masked_eq_toNat]
  have hx : BitVec.ofInt n (p : Int) = BitVec.ofNat n p := BitVec.ofInt_natCast _ _
  have hxn : (BitVec.ofNat n p).toNat = p := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hp]
  generalize BitVec.ofInt n b = y
  rw [hx]
  by_cases hy : y = 0#n
  · subst hy
    simp only [BitVec.toNat_zero, Int.natCast_zero, ite_true, hx, BitVec.umod_zero]
  · have h0 : (y.toNat : Int) ≠ 0 := by
      intro h; apply hy; apply BitVec.eq_of_toNat_eq; simpa using h
    simp only [h0, ite_false, ofInt_masked_toNat]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_umod, hxn, BitVec.toNat_ofInt]
    have e : trem (p : Int) (y.toNat : Int) = ((p % y.toNat : Nat) : Int) := rfl
    rw [e, ← Int.natCast_emod, Int.toNat_natCast,
      Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.mod_le _ _) hp)]

theorem ofInt_lit_srem (hn : 0 < n) (a b : Int) :
    BitVec.ofInt n (lit_srem (.TBitVector (n : Int)) s2 a b) = (BitVec.ofInt n a).srem (BitVec.ofInt n b) := by
  unfold lit_srem
  simp only [size_of_ty]
  simp only [sext_of_eq hn, sext_of_ty hn]
  by_cases hd : (BitVec.ofInt n b).toInt = 0
  · have hy : BitVec.ofInt n b = 0#n := by
      apply BitVec.eq_of_toInt_eq; simpa using hd
    simp only [hd, ite_true]
    rw [hy, BitVec.srem_zero]
  · simp only [hd, ite_false, ofInt_masked]
    rw [trem, ← BitVec.toInt_srem, BitVec.ofInt_toInt]

theorem ofInt_lit_sdiv (hn : 0 < n) (a b : Int) :
    BitVec.ofInt n (lit_sdiv (.TBitVector (n : Int)) s2 a b) = (BitVec.ofInt n a).smtSDiv (BitVec.ofInt n b) := by
  unfold lit_sdiv
  simp only [size_of_ty]
  simp only [sext_of_eq hn, sext_of_ty hn]
  generalize BitVec.ofInt n a = x
  generalize BitVec.ofInt n b = y
  by_cases hd : y.toInt = 0
  · have hy : y = 0#n := by apply BitVec.eq_of_toInt_eq; simpa using hd
    simp only [hd, ite_true, ofInt_masked]
    subst hy
    rw [BitVec.smtSDiv_zero]
    have : (x.slt 0#n = true) ↔ x.toInt < 0 := by simp [BitVec.slt]
    by_cases hx : x.toInt < 0
    · simp [hx, this.2 hx]
    · simp [hx, mt this.1 hx]
      exact ofInt_neg_one'
  · have hy : y ≠ 0#n := fun h => hd (by simp [h])
    simp only [hd, ite_false, ofInt_masked]
    rw [smtSDiv_eq_sdiv hy]
    apply BitVec.eq_of_toInt_eq
    rw [BitVec.toInt_ofInt, BitVec.toInt_sdiv]; rfl

theorem ofInt_lit_smod (hn : 0 < n) (a b : Int) :
    BitVec.ofInt n (lit_smod (.TBitVector (n : Int)) s2 a b) = (BitVec.ofInt n a).smod (BitVec.ofInt n b) := by
  unfold lit_smod
  simp only [size_of_ty]
  simp only [sext_of_eq hn, sext_of_ty hn]
  by_cases hd : (BitVec.ofInt n b).toInt = 0
  · have hy : BitVec.ofInt n b = 0#n := by
      apply BitVec.eq_of_toInt_eq; simpa using hd
    simp only [hd, ite_true]
    rw [hy]
    apply BitVec.eq_of_toInt_eq
    rw [BitVec.toInt_smod]; simp
  · simp only [hd, ite_false]
    have key : (BitVec.ofInt n a).smod (BitVec.ofInt n b) =
        BitVec.ofInt n (Int.fmod (BitVec.ofInt n a).toInt (BitVec.ofInt n b).toInt) := by
      rw [← BitVec.toInt_smod, BitVec.ofInt_toInt]
    rw [key, ← smod_formula _ _ hd, trem]
    split <;> exact ofInt_masked rfl _

theorem ofInt_lit_extract {m : Nat} {from_ to_ a : Int} (ha0 : 0 ≤ a) (ha1 : a < 2 ^ n)
    (hf : 0 ≤ from_) (hm : to_ - from_ + 1 = m) :
    BitVec.ofInt m (lit_extract from_ to_ (.TBitVector (n : Int)) a) = (BitVec.ofInt n a).extractLsb' from_.toNat m := by
  obtain ⟨p, rfl⟩ := Int.eq_ofNat_of_zero_le ha0
  obtain ⟨f, rfl⟩ := Int.eq_ofNat_of_zero_le hf
  have hp : p < 2 ^ n := by exact_mod_cast ha1
  rw [lit_extract, hm, ofInt_masked rfl, zasr_natCast]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofInt, BitVec.extractLsb'_toNat, BitVec.ofInt_natCast, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hp, Int.toNat_natCast, Nat.shiftRight_eq_div_pow, ← Int.natCast_emod]
  rfl

theorem ofInt_emod_two_pow_toNat {n : Nat} {k : Int} (hk : k = n) (z : Int) :
    BitVec.ofInt n (z % 2 ^ k.toNat) = BitVec.ofInt n z := by
  subst hk; simp only [Int.toNat_natCast]; exact Kanon.BitVec.ofInt_emod_two_pow z

theorem ofInt_lit_extract_zero {m : Nat} {to_ a : Int} (ha0 : 0 ≤ a) (ha1 : a < 2 ^ n)
    (hm : to_ + 1 = m) :
    BitVec.ofInt m (lit_extract 0 to_ (.TBitVector (n : Int)) a) = (BitVec.ofInt n a).extractLsb' 0 m :=
  ofInt_lit_extract ha0 ha1 (Int.le_refl 0) (by omega)

theorem ofInt_lit_concat {m : Nat} {a b : Int} (ha0 : 0 ≤ a)
    (ha1 : a < 2 ^ n) (hb0 : 0 ≤ b) (hb1 : b < 2 ^ m) :
    BitVec.ofInt (n + m) (lit_concat (.TBitVector (n : Int)) (.TBitVector (m : Int)) a b) = BitVec.ofInt n a ++ BitVec.ofInt m b := by
  obtain ⟨p, rfl⟩ := Int.eq_ofNat_of_zero_le ha0
  obtain ⟨q, rfl⟩ := Int.eq_ofNat_of_zero_le hb0
  have hp : p < 2 ^ n := by exact_mod_cast ha1
  have hq : q < 2 ^ m := by exact_mod_cast hb1
  have hx : (BitVec.ofInt n (p : Int)).toNat = p := by
    rw [BitVec.ofInt_natCast, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hp]
  have hy : (BitVec.ofInt m (q : Int)).toNat = q := by
    rw [BitVec.ofInt_natCast, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hq]
  apply BitVec.eq_of_toNat_eq
  have hlt := BitVec.toNat_shiftLeft_or_toNat_lt_two_pow_add (BitVec.ofInt n (p : Int))
    (BitVec.ofInt m (q : Int))
  rw [hx, hy] at hlt
  rw [BitVec.toNat_append, hx, hy, BitVec.toNat_ofInt]
  have e : lit_concat (.TBitVector (n : Int)) (.TBitVector (m : Int)) (p : Int) (q : Int) = ((p <<< m ||| q : Nat) : Int) := by
    simp only [lit_concat, size_of_ty, z_lsl, zlor, Int.toNat_natCast, Nat.shiftLeft_eq]
    rfl
  rw [e, ← Int.natCast_emod, Int.toNat_natCast, Nat.mod_eq_of_lt hlt]

theorem ofInt_lit_zext {k : Nat} {a : Int} (ha0 : 0 ≤ a) (ha1 : a < 2 ^ n) :
    BitVec.ofInt (n + k) (lit_zext k (.TBitVector (n : Int)) a) = (BitVec.ofInt n a).setWidth (n + k) := by
  obtain ⟨p, rfl⟩ := Int.eq_ofNat_of_zero_le ha0
  have hp : p < 2 ^ n := by exact_mod_cast ha1
  apply BitVec.eq_of_toNat_eq
  have hx : (BitVec.ofInt n (p : Int)).toNat = p := by
    rw [BitVec.ofInt_natCast, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hp]
  rw [lit_zext, BitVec.toNat_setWidth, hx, BitVec.toNat_ofInt, ← Int.natCast_emod,
    Int.toNat_natCast]

theorem ofInt_lit_sext (hn : 0 < n) (k : Nat) (a : Int) :
    BitVec.ofInt (n + k) (lit_sext k (.TBitVector (n : Int)) a) = (BitVec.ofInt n a).signExtend (n + k) := by
  rw [lit_sext, size_of_ty, show (n : Int) + (k : Int) = ((n + k : Nat) : Int) by push_cast; rfl,
    ofInt_masked rfl, show sext_of (n : Int) a = (BitVec.ofInt n a).toInt from bv_to_z_true hn a]
  rfl

theorem ofInt_lit_concat' {m N : Nat} {a b : Int} (ha0 : 0 ≤ a) (ha1 : a < 2 ^ n) (hb0 : 0 ≤ b)
    (hb1 : b < 2 ^ m) (hN : (n : Int) + m = N) :
    BitVec.ofInt N (lit_concat (.TBitVector (n : Int)) (.TBitVector (m : Int)) a b) =
      (BitVec.ofInt n a ++ BitVec.ofInt m b).setWidth N := by
  obtain rfl : N = n + m := by omega
  rw [BitVec.setWidth_eq]
  exact ofInt_lit_concat ha0 ha1 hb0 hb1

theorem ofInt_lit_zext' {m : Nat} {by_ a : Int} (ha0 : 0 ≤ a) (ha1 : a < 2 ^ n) (hb : 0 ≤ by_)
    (hm : (n : Int) + by_ = m) :
    BitVec.ofInt m (lit_zext by_ (.TBitVector (n : Int)) a) = (BitVec.ofInt n a).setWidth m := by
  obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hb
  obtain rfl : m = n + k := by omega
  exact ofInt_lit_zext ha0 ha1

theorem ofInt_lit_sext' {m : Nat} {by_ : Int} (hn : 0 < n) (a : Int) (hb : 0 ≤ by_)
    (hm : (n : Int) + by_ = m) :
    BitVec.ofInt m (lit_sext by_ (.TBitVector (n : Int)) a) = (BitVec.ofInt n a).signExtend m := by
  obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hb
  obtain rfl : m = n + k := by omega
  exact ofInt_lit_sext hn k a

/-! ## Ranges

The results of the operations are literals in range (with the hypotheses that the operations that
return an operand need): `lit_X_nonneg` and `lit_X_lt` give the typing of the literals built by the
rules. -/

theorem masked_nonneg (w z : Int) : 0 ≤ masked w z := emod_two_pow_nonneg z w.toNat

theorem masked_lt (w z : Int) : masked w z < 2 ^ w.toNat := emod_two_pow_lt z w.toNat


theorem ite_nonneg' {c : Prop} [Decidable c] {x y : Int} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    0 ≤ if c then x else y := by
  split <;> assumption

theorem ite_lt' {c : Prop} [Decidable c] {x y B : Int} (hx : x < B) (hy : y < B) :
    (if c then x else y) < B := by
  split <;> assumption

macro "kanon_lit_range" : tactic => `(tactic| (
  simp only [size_of_ty]
  repeat' first
    | exact masked_nonneg _ _
    | exact masked_lt _ _
    | apply ite_nonneg'
    | apply ite_lt'
    | split
    | omega))

theorem lit_add_nonneg (a b : Int) : 0 ≤ lit_add (.TBitVector w) s2 a b := masked_nonneg _ _
theorem lit_add_lt (a b : Int) : lit_add (.TBitVector w) s2 a b < 2 ^ w.toNat := masked_lt _ _
theorem lit_sub_nonneg (a b : Int) : 0 ≤ lit_sub (.TBitVector w) s2 a b := masked_nonneg _ _
theorem lit_sub_lt (a b : Int) : lit_sub (.TBitVector w) s2 a b < 2 ^ w.toNat := masked_lt _ _
theorem lit_mul_nonneg (a b : Int) : 0 ≤ lit_mul (.TBitVector w) s2 a b := masked_nonneg _ _
theorem lit_mul_lt (a b : Int) : lit_mul (.TBitVector w) s2 a b < 2 ^ w.toNat := masked_lt _ _
theorem lit_and_nonneg (a b : Int) : 0 ≤ lit_and (.TBitVector w) s2 a b := masked_nonneg _ _
theorem lit_and_lt (a b : Int) : lit_and (.TBitVector w) s2 a b < 2 ^ w.toNat := masked_lt _ _
theorem lit_or_nonneg (a b : Int) : 0 ≤ lit_or (.TBitVector w) s2 a b := masked_nonneg _ _
theorem lit_or_lt (a b : Int) : lit_or (.TBitVector w) s2 a b < 2 ^ w.toNat := masked_lt _ _
theorem lit_xor_nonneg (a b : Int) : 0 ≤ lit_xor (.TBitVector w) s2 a b := masked_nonneg _ _
theorem lit_xor_lt (a b : Int) : lit_xor (.TBitVector w) s2 a b < 2 ^ w.toNat := masked_lt _ _
theorem lit_neg_nonneg (a : Int) : 0 ≤ lit_neg (.TBitVector w) a := masked_nonneg _ _
theorem lit_neg_lt (a : Int) : lit_neg (.TBitVector w) a < 2 ^ w.toNat := masked_lt _ _
theorem lit_not_nonneg (a : Int) : 0 ≤ lit_not (.TBitVector w) a := masked_nonneg _ _
theorem lit_not_lt (a : Int) : lit_not (.TBitVector w) a < 2 ^ w.toNat := masked_lt _ _
theorem lit_shl_nonneg (a b : Int) : 0 ≤ lit_shl (.TBitVector w) s2 a b := by
  unfold lit_shl; kanon_lit_range
theorem lit_shl_lt (a b : Int) : lit_shl (.TBitVector w) s2 a b < 2 ^ w.toNat := by
  unfold lit_shl; kanon_lit_range
theorem lit_lshr_nonneg (a b : Int) : 0 ≤ lit_lshr (.TBitVector w) s2 a b := by
  unfold lit_lshr; kanon_lit_range
theorem lit_lshr_lt (a b : Int) : lit_lshr (.TBitVector w) s2 a b < 2 ^ w.toNat := by
  unfold lit_lshr; kanon_lit_range
theorem lit_ashr_nonneg (a b : Int) : 0 ≤ lit_ashr (.TBitVector w) s2 a b := by
  unfold lit_ashr; kanon_lit_range
theorem lit_ashr_lt (a b : Int) : lit_ashr (.TBitVector w) s2 a b < 2 ^ w.toNat := by
  unfold lit_ashr; kanon_lit_range
theorem lit_udiv_nonneg (a b : Int) : 0 ≤ lit_udiv (.TBitVector w) s2 a b := by
  unfold lit_udiv; kanon_lit_range
theorem lit_udiv_lt (a b : Int) : lit_udiv (.TBitVector w) s2 a b < 2 ^ w.toNat := by
  unfold lit_udiv; kanon_lit_range
theorem lit_sdiv_nonneg (a b : Int) : 0 ≤ lit_sdiv (.TBitVector w) s2 a b := by
  unfold lit_sdiv; kanon_lit_range
theorem lit_sdiv_lt (a b : Int) : lit_sdiv (.TBitVector w) s2 a b < 2 ^ w.toNat := by
  unfold lit_sdiv; kanon_lit_range
theorem lit_urem_nonneg {a : Int} (ha : 0 ≤ a) (b : Int) :
    0 ≤ lit_urem (.TBitVector w) s2 a b := by
  unfold lit_urem; kanon_lit_range
theorem lit_urem_lt {a : Int} (ha : a < 2 ^ w.toNat) (b : Int) :
    lit_urem (.TBitVector w) s2 a b < 2 ^ w.toNat := by
  unfold lit_urem; kanon_lit_range
theorem lit_srem_nonneg {a : Int} (ha : 0 ≤ a) (b : Int) :
    0 ≤ lit_srem (.TBitVector w) s2 a b := by
  unfold lit_srem; kanon_lit_range
theorem lit_srem_lt {a : Int} (ha : a < 2 ^ w.toNat) (b : Int) :
    lit_srem (.TBitVector w) s2 a b < 2 ^ w.toNat := by
  unfold lit_srem; kanon_lit_range
theorem lit_smod_nonneg {a : Int} (ha : 0 ≤ a) (b : Int) :
    0 ≤ lit_smod (.TBitVector w) s2 a b := by
  unfold lit_smod; kanon_lit_range
theorem lit_smod_lt {a : Int} (ha : a < 2 ^ w.toNat) (b : Int) :
    lit_smod (.TBitVector w) s2 a b < 2 ^ w.toNat := by
  unfold lit_smod; kanon_lit_range

theorem lit_extract_nonneg (from_ to_ : Int) (a : Int) :
    0 ≤ lit_extract from_ to_ (.TBitVector w) a := masked_nonneg _ _
theorem lit_extract_lt (from_ to_ : Int) (a : Int) :
    lit_extract from_ to_ (.TBitVector w) a < 2 ^ (to_ - from_ + 1).toNat := masked_lt _ _

theorem lit_sext_nonneg (k : Int) (a : Int) : 0 ≤ lit_sext k (.TBitVector w) a := masked_nonneg _ _
theorem lit_sext_lt (k : Int) (a : Int) : lit_sext k (.TBitVector w) a < 2 ^ (w + k).toNat := by
  simp only [lit_sext, size_of_ty]; exact masked_lt _ _

theorem lit_zext_nonneg {a : Int} (k : Int) (ha : 0 ≤ a) :
    0 ≤ lit_zext k (.TBitVector w) a := ha
theorem lit_zext_lt {a : Int} {k : Int} (hw : 0 ≤ w) (hk : 0 ≤ k) (ha : a < 2 ^ w.toNat) :
    lit_zext k (.TBitVector w) a < 2 ^ (w + k).toNat := by
  have : (2 : Int) ^ w.toNat ≤ 2 ^ (w + k).toNat := by
    exact_mod_cast Nat.pow_le_pow_right (by omega) (by omega)
  exact Int.lt_of_lt_of_le ha this

theorem lit_concat_nat {n m : Nat} (p q : Nat) :
    lit_concat (.TBitVector (n : Int)) (.TBitVector (m : Int)) (p : Int) (q : Int) =
      ((p <<< m ||| q : Nat) : Int) := by
  simp only [lit_concat, size_of_ty, z_lsl, zlor, Int.toNat_natCast, Nat.shiftLeft_eq]
  rfl

theorem lit_concat_nonneg {m : Int} {a b : Int} (hm : 0 ≤ m) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ lit_concat (.TBitVector w) (.TBitVector m) a b := by
  obtain ⟨p, rfl⟩ := Int.eq_ofNat_of_zero_le ha
  obtain ⟨q, rfl⟩ := Int.eq_ofNat_of_zero_le hb
  obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hm
  simp only [lit_concat, size_of_ty, z_lsl, zlor, Int.toNat_natCast, Nat.shiftLeft_eq]
  exact Int.natCast_nonneg (p * 2 ^ m ||| q)

theorem lit_concat_lt {m : Int} {a b : Int} (hw : 0 ≤ w) (hm : 0 ≤ m) (ha : 0 ≤ a)
    (ha1 : a < 2 ^ w.toNat) (hb : 0 ≤ b) (hb1 : b < 2 ^ m.toNat) :
    lit_concat (.TBitVector w) (.TBitVector m) a b < 2 ^ (w + m).toNat := by
  obtain ⟨p, rfl⟩ := Int.eq_ofNat_of_zero_le ha
  obtain ⟨q, rfl⟩ := Int.eq_ofNat_of_zero_le hb
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hw
  obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hm
  simp only [Int.toNat_natCast] at ha1 hb1 ⊢
  have hp : p < 2 ^ n := by exact_mod_cast ha1
  have hq : q < 2 ^ m := by exact_mod_cast hb1
  have hlt := BitVec.toNat_shiftLeft_or_toNat_lt_two_pow_add (BitVec.ofInt n (p : Int))
    (BitVec.ofInt m (q : Int))
  have hx : (BitVec.ofInt n (p : Int)).toNat = p := by
    rw [BitVec.ofInt_natCast, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hp]
  have hy : (BitVec.ofInt m (q : Int)).toNat = q := by
    rw [BitVec.ofInt_natCast, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hq]
  rw [hx, hy] at hlt
  rw [lit_concat_nat]
  have e : (((n : Int) + (m : Int)).toNat) = n + m := by omega
  rw [e]
  exact_mod_cast hlt

theorem lit_concat_nonneg' {m : Int} {a b : Int} (hm : 0 < m) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ lit_concat (.TBitVector w) (.TBitVector m) a b :=
  lit_concat_nonneg (Int.le_of_lt hm) ha hb

theorem lit_concat_lt' {m : Int} {a b : Int} (hw : 0 < w) (hm : 0 < m) (ha : 0 ≤ a)
    (ha1 : a < 2 ^ w.toNat) (hb : 0 ≤ b) (hb1 : b < 2 ^ m.toNat) :
    lit_concat (.TBitVector w) (.TBitVector m) a b < 2 ^ (w + m).toNat :=
  lit_concat_lt (Int.le_of_lt hw) (Int.le_of_lt hm) ha ha1 hb hb1

end

theorem nonzero_extract_pow2 {m to_ n : Int} {T : Ty} (hp : Bitvec.is_pow2 n = true) (hl : log2 n < to_)
    (hm : m = to_ + 1) : Nonzero (mk_masked m (lit_extract 0 to_ T n)) := by
  subst hm
  have h0 := (is_pow2_eq hp).2
  have hpos : 0 < n := by obtain ⟨h, _⟩ := is_pow2_eq hp; rw [h]; exact Int.pow_pos (by decide)
  have hlt := lt_two_pow_log2 hpos (by omega : log2 n < to_ + 1)
  refine nonzero_mk_masked (by omega) ?_
  simp only [lit_extract, masked, z_asr_zero, Int.sub_zero, Int.emod_emod]
  rw [Int.emod_eq_of_lt (Int.le_of_lt hpos) (by simpa using hlt)]
  omega

theorem nonzero_udiv_core {FS : FloatSem} {N : Nat} {t10 T : Ty} {d n : Int}
    (ht : t10 = .TBitVector N) (hN : 0 < N) (hd0 : 0 ≤ d) (hd1 : d < 2 ^ N) (hn0 : 0 ≤ n)
    (hn1 : n < 2 ^ N) (hs : Nonzero (.mk (.BitVec d) t10)) (hn : n ≠ 0)
    (hdv : Bitvec.udivides n d = true) : Nonzero (mk_masked N (lit_udiv t10 T d n)) := by
  have hz := ne_zero_of_nonzero_bitVec (FS := FS) ht hN hd0 hd1 hs
  have hnp : 0 < n := by omega
  simp only [Bitvec.udivides, divisible, decide_eq_true_eq] at hdv
  obtain ⟨q, rfl⟩ := hdv
  have hq : 0 < q := by
    by_cases h : 0 < q
    · exact h
    · have := Int.mul_nonpos_of_nonneg_of_nonpos (Int.le_of_lt hnp) (Int.not_lt.mp h)
      omega
  have hqd : q ≤ n * q := by
    have : 1 * q ≤ n * q := Int.mul_le_mul_of_nonneg_right (by omega) (Int.le_of_lt hq)
    omega
  have hp : (0 : Int) < 2 ^ N := Int.pow_pos (by decide)
  refine nonzero_mk_masked (by omega) ?_
  simp only [ht, lit_udiv, masked, size_of_ty_bitVector, Int.toNat_natCast,
    Int.emod_eq_of_lt hn0 hn1, hn, ite_false, tdiv, Int.mul_tdiv_cancel_left _ hn, Int.emod_emod]
  rw [Int.emod_eq_of_lt (Int.le_of_lt hq) (by omega)]
  omega

theorem nonzero_div_mul {FS : FloatSem} {s2 : Bool} {x : Term} {n d : Int} {t5 t7 t10 : Ty}
    (kw : (sem FS).WT (Bitvec.div.spec false (.mk (.Op2 (.Mul ⟨s2, true⟩) (.mk (.BitVec n) t5) x) t7)
      (.mk (.BitVec d) t10)))
    (hs : Nonzero (.mk (.BitVec d) t10)) (hn : n ≠ 0) (hdv : Bitvec.udivides n d = true) :
    Nonzero (mk_bv (Bitvec.size (.mk (.Op2 (.Mul ⟨s2, true⟩) (.mk (.BitVec n) t5) x) t7)) (lit_udiv t10 t7 d n)) := by
  simp only [sem, Bitvec.div.spec, WT_op2, WT_bitVec, Op2.WT, Term.ty_mk] at kw
  obtain ⟨⟨_, h107, _⟩, ⟨⟨_, _, h75⟩, ⟨m, hm, h5, hn0, hn1⟩, _⟩, ⟨k, hk, h10, hd0, hd1⟩⟩ := kw
  have e : t7 = .TBitVector k := h107.symm.trans h10
  have hmk : m = k := by
    have h' := (h75.symm.trans e).symm.trans h5
    simp only [Ty.TBitVector.injEq] at h'
    omega
  subst hmk
  simp only [size_eq, Term.ty_mk, e, size_of_ty_bitVector]
  exact nonzero_udiv_core (FS := FS) h10 hk hd0 hd1 hn0 hn1 hs hn hdv

theorem nonzero_div_mul' {FS : FloatSem} {s2 : Bool} {x : Term} {n d : Int} {t5 t7 t10 : Ty}
    (kw : (sem FS).WT (Bitvec.div.spec false (.mk (.Op2 (.Mul ⟨s2, true⟩) x (.mk (.BitVec n) t5)) t7)
      (.mk (.BitVec d) t10)))
    (hs : Nonzero (.mk (.BitVec d) t10)) (hn : n ≠ 0) (hdv : Bitvec.udivides n d = true) :
    Nonzero (mk_bv (Bitvec.size (.mk (.Op2 (.Mul ⟨s2, true⟩) x (.mk (.BitVec n) t5)) t7)) (lit_udiv t10 t7 d n)) := by
  simp only [sem, Bitvec.div.spec, WT_op2, WT_bitVec, Op2.WT, Term.ty_mk] at kw
  obtain ⟨⟨_, h107, _⟩, ⟨⟨_, h5x, h7x⟩, _, ⟨m, hm, h5, hn0, hn1⟩⟩, ⟨k, hk, h10, hd0, hd1⟩⟩ := kw
  have e : t7 = .TBitVector k := h107.symm.trans h10
  have hmk : m = k := by
    have h' := e.symm.trans ((h7x.trans h5x.symm).trans h5)
    simp only [Ty.TBitVector.injEq] at h'
    omega
  subst hmk
  simp only [size_eq, Term.ty_mk, e, size_of_ty_bitVector]
  exact nonzero_udiv_core (FS := FS) h10 hk hd0 hd1 hn0 hn1 hs hn hdv

theorem nonzero_div_div {FS : FloatSem} {x : Term} {n d : Int} {t5 t6 t8 : Ty}
    (kw : (sem FS).WT (Bitvec.div.spec false (.mk (.Op2 (.Div false) x (.mk (.BitVec n) t5)) t6)
      (.mk (.BitVec d) t8)))
    (hs : Nonzero (.mk (.BitVec d) t8)) (hn : n ≠ 0)
    (hov : Bitvec.overflows_mul false (Bitvec.size (.mk (.Op2 (.Div false) x (.mk (.BitVec n) t5)) t6)) n d = false) :
    Nonzero (mk_bv (Bitvec.size (.mk (.Op2 (.Div false) x (.mk (.BitVec n) t5)) t6)) (lit_mul t6 t8 n d)) := by
  simp only [sem, Bitvec.div.spec, WT_op2, WT_bitVec, Op2.WT, Term.ty_mk] at kw
  obtain ⟨⟨_, h86, _⟩, ⟨⟨_, h5x, h6x⟩, _, ⟨m, hm, h5, hn0, hn1⟩⟩, ⟨k, hk, h8, hd0, hd1⟩⟩ := kw
  have e : t6 = .TBitVector k := h86.symm.trans h8
  have hmk : m = k := by
    have h' := e.symm.trans ((h6x.trans h5x.symm).trans h5)
    simp only [Ty.TBitVector.injEq] at h'
    omega
  subst hmk
  have hz := ne_zero_of_nonzero_bitVec (FS := FS) h8 hk hd0 hd1 hs
  simp only [size_eq, Term.ty_mk, e, size_of_ty_bitVector] at hov ⊢
  rw [Bitvec.overflows_mul, bv_to_z_false hn0 hn1, bv_to_z_false hd0 hd1, toNat_ofInt_of_lt hn0 hn1,
    toNat_ofInt_of_lt hd0 hd1, Int.toNat_of_nonneg hn0, Int.toNat_of_nonneg hd0] at hov
  simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not, max_for_false, min_for_false] at hov
  try simp only [decide_eq_false_iff_not] at hov
  have hlt : n * d < 2 ^ m := by omega
  have hnp : 0 < n := by omega
  have hdp : 0 < d := by omega
  refine nonzero_mk_masked (by omega) ?_
  simp only [lit_mul, masked, size_of_ty_bitVector, Int.toNat_natCast, e, Int.emod_emod]
  rw [Int.emod_eq_of_lt (Int.le_of_lt (Int.mul_pos hnp hdp)) hlt]
  exact Int.ne_of_gt (Int.mul_pos hnp hdp)

end Kanon.Lib
