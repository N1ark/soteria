import BitvecMod.Tactic
import BitvecMod.LitOps

/-!
# Lemmas for the shifts, resizings, divisions and remainders of the bitvec module

The divisions and remainders of literals as those of their values (`ofInt_lit_smod`, …, and
at the integer width of a sort, `ofInt_lit_smod'`, …), their ranges, ported from option B.
-/

noncomputable section

namespace BitvecMod.ResizeLib

open Classical Kanon Prim LitOps

theorem ofInt_emod_two_pow (n : Nat) (z : Int) :
    BitVec.ofInt n (z % 2 ^ n) = BitVec.ofInt n z := by
  apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_ofInt]

theorem zasr_zero (z : Int) : zasr z 0 = z := by simp [zasr]

attribute [local simp] zasr_zero ofInt_emod_two_pow


/-! ## Division and remainders of literals -/

section
variable {n : Nat}

theorem ofInt_masked' (z : Int) : BitVec.ofInt n (masked (n : Int) z) = BitVec.ofInt n z := by
  simp only [masked, Int.toNat_natCast, ofInt_emod_two_pow]

theorem smtSDiv_eq_sdiv {x y : BitVec n} (hy : y ≠ 0#n) : x.smtSDiv y = x.sdiv y := by
  have hny : -y ≠ 0#n := by simpa using hy
  rw [BitVec.smtSDiv, BitVec.sdiv]
  cases x.msb <;> cases y.msb <;> simp [BitVec.smtUDiv_eq, hy, hny, BitVec.udiv_eq]

theorem ofInt_neg_one' : BitVec.ofInt n (-1) = BitVec.allOnes n := by
  rw [BitVec.ofInt_neg, BitVec.ofInt_ofNat, BitVec.neg_one_eq_allOnes]

end

theorem smod_formula (X d : Int) (hd : d ≠ 0) :
    (if (Int.tmod X d) = 0 ∨ (Int.tmod X d).sign = d.sign then Int.tmod X d
      else Int.tmod X d + d) = Int.fmod X d := by
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
variable {n : Nat}

theorem ofInt_lit_urem {a : Int} (ha0 : 0 ≤ a) (ha1 : a < 2 ^ n) (b : Int) :
    BitVec.ofInt n (Prim.lit_urem (n : Int) a b) = BitVec.ofInt n a % BitVec.ofInt n b := by
  obtain ⟨p, rfl⟩ := Int.eq_ofNat_of_zero_le ha0
  have hp : p < 2 ^ n := by exact_mod_cast ha1
  unfold Prim.lit_urem
  simp only [masked_eq_toNat]
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
    have e : Prim.trem (p : Int) (y.toNat : Int) = ((p % y.toNat : Nat) : Int) := rfl
    rw [e, ← Int.natCast_emod, Int.toNat_natCast,
      Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.mod_le _ _) hp)]

theorem ofInt_lit_srem (hn : 0 < n) (a b : Int) :
    BitVec.ofInt n (Prim.lit_srem (n : Int) a b) = (BitVec.ofInt n a).srem (BitVec.ofInt n b) := by
  unfold Prim.lit_srem
  simp only [sext_of_eq hn]
  by_cases hd : (BitVec.ofInt n b).toInt = 0
  · have hy : BitVec.ofInt n b = 0#n := by
      apply BitVec.eq_of_toInt_eq; simpa using hd
    simp only [hd, ite_true]
    rw [hy, BitVec.srem_zero]
  · simp only [hd, ite_false, ofInt_masked']
    rw [Prim.trem, ← BitVec.toInt_srem, BitVec.ofInt_toInt]

theorem ofInt_lit_sdiv (hn : 0 < n) (a b : Int) :
    BitVec.ofInt n (Prim.lit_sdiv (n : Int) a b) = (BitVec.ofInt n a).smtSDiv (BitVec.ofInt n b) := by
  unfold Prim.lit_sdiv
  simp only [sext_of_eq hn]
  generalize BitVec.ofInt n a = x
  generalize BitVec.ofInt n b = y
  by_cases hd : y.toInt = 0
  · have hy : y = 0#n := by apply BitVec.eq_of_toInt_eq; simpa using hd
    simp only [hd, ite_true, ofInt_masked']
    subst hy
    rw [BitVec.smtSDiv_zero]
    have : (x.slt 0#n = true) ↔ x.toInt < 0 := by simp [BitVec.slt]
    by_cases hx : x.toInt < 0
    · simp [hx, this.2 hx]
    · simp [hx, mt this.1 hx]
      exact ofInt_neg_one'
  · have hy : y ≠ 0#n := fun h => hd (by simp [h])
    simp only [hd, ite_false, ofInt_masked']
    rw [smtSDiv_eq_sdiv hy]
    apply BitVec.eq_of_toInt_eq
    rw [BitVec.toInt_ofInt, BitVec.toInt_sdiv]; rfl

theorem ofInt_lit_smod (hn : 0 < n) (a b : Int) :
    BitVec.ofInt n (Prim.lit_smod (n : Int) a b) = (BitVec.ofInt n a).smod (BitVec.ofInt n b) := by
  unfold Prim.lit_smod
  simp only [sext_of_eq hn]
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
    rw [key, ← smod_formula _ _ hd, Prim.trem]
    split <;> exact ofInt_masked' _

@[simp] theorem smtUDiv_one (x : BitVec n) : x.smtUDiv 1#n = x := by
  rcases n with _ | n
  · exact Subsingleton.elim _ _
  · simp [BitVec.smtUDiv_eq]

@[simp] theorem smtSDiv_one (x : BitVec n) : x.smtSDiv 1#n = x := by
  rcases n with _ | _ | n
  · exact Subsingleton.elim _ _
  · revert x; decide
  · cases h : x.msb <;> simp [BitVec.smtSDiv_eq, BitVec.smtUDiv_eq, h]

theorem lit_sdiv_nonneg (a b : Int) : 0 ≤ Prim.lit_sdiv (n : Int) a b := by
  unfold Prim.lit_sdiv; dsimp only; split <;> exact masked_nonneg _ _
theorem lit_sdiv_lt (a b : Int) : Prim.lit_sdiv (n : Int) a b < 2 ^ n := by
  unfold Prim.lit_sdiv; dsimp only; split <;> exact masked_lt_nat _
theorem lit_urem_nonneg {a : Int} (ha : 0 ≤ a) (b : Int) : 0 ≤ Prim.lit_urem (n : Int) a b := by
  unfold Prim.lit_urem; dsimp only; split <;> first | exact ha | exact masked_nonneg _ _
theorem lit_urem_lt {a : Int} (ha : a < 2 ^ n) (b : Int) : Prim.lit_urem (n : Int) a b < 2 ^ n := by
  unfold Prim.lit_urem; dsimp only; split <;> first | exact ha | exact masked_lt_nat _
theorem lit_srem_nonneg {a : Int} (ha : 0 ≤ a) (b : Int) : 0 ≤ Prim.lit_srem (n : Int) a b := by
  unfold Prim.lit_srem; dsimp only; split <;> first | exact ha | exact masked_nonneg _ _
theorem lit_srem_lt {a : Int} (ha : a < 2 ^ n) (b : Int) : Prim.lit_srem (n : Int) a b < 2 ^ n := by
  unfold Prim.lit_srem; dsimp only; split <;> first | exact ha | exact masked_lt_nat _
theorem lit_smod_nonneg {a : Int} (ha : 0 ≤ a) (b : Int) : 0 ≤ Prim.lit_smod (n : Int) a b := by
  unfold Prim.lit_smod; dsimp only; split
  · exact ha
  · split <;> exact masked_nonneg _ _
theorem lit_smod_lt {a : Int} (ha : a < 2 ^ n) (b : Int) : Prim.lit_smod (n : Int) a b < 2 ^ n := by
  unfold Prim.lit_smod; dsimp only; split
  · exact ha
  · split <;> exact masked_lt_nat _

end

/-! At the integer width `w` of a sort, positive. -/

section
variable {w : Int} (hw : 0 < w)
include hw

theorem ofInt_lit_smod' (a b : Int) :
    BitVec.ofInt w.toNat (Prim.lit_smod w a b) = (BitVec.ofInt w.toNat a).smod (BitVec.ofInt w.toNat b) := by
  have := ofInt_lit_smod (n := w.toNat) (by omega) a b; rwa [toNat_cast_of_pos hw] at this
theorem ofInt_lit_srem' (a b : Int) :
    BitVec.ofInt w.toNat (Prim.lit_srem w a b) = (BitVec.ofInt w.toNat a).srem (BitVec.ofInt w.toNat b) := by
  have := ofInt_lit_srem (n := w.toNat) (by omega) a b; rwa [toNat_cast_of_pos hw] at this
theorem ofInt_lit_sdiv' (a b : Int) :
    BitVec.ofInt w.toNat (Prim.lit_sdiv w a b) =
      (BitVec.ofInt w.toNat a).smtSDiv (BitVec.ofInt w.toNat b) := by
  have := ofInt_lit_sdiv (n := w.toNat) (by omega) a b; rwa [toNat_cast_of_pos hw] at this
theorem ofInt_lit_urem' {a : Int} (ha0 : 0 ≤ a) (ha1 : a < 2 ^ w.toNat) (b : Int) :
    BitVec.ofInt w.toNat (Prim.lit_urem w a b) = BitVec.ofInt w.toNat a % BitVec.ofInt w.toNat b := by
  have := ofInt_lit_urem (n := w.toNat) ha0 ha1 b; rwa [toNat_cast_of_pos hw] at this
theorem lit_sdiv_range' (a b : Int) : 0 ≤ Prim.lit_sdiv w a b ∧ Prim.lit_sdiv w a b < 2 ^ w.toNat := by
  have h1 := lit_sdiv_nonneg (n := w.toNat) a b; have h2 := lit_sdiv_lt (n := w.toNat) a b
  rw [toNat_cast_of_pos hw] at h1 h2; exact ⟨h1, h2⟩
theorem lit_urem_range' {a : Int} (ha0 : 0 ≤ a) (ha1 : a < 2 ^ w.toNat) (b : Int) :
    0 ≤ Prim.lit_urem w a b ∧ Prim.lit_urem w a b < 2 ^ w.toNat := by
  have h1 := lit_urem_nonneg (n := w.toNat) ha0 b; have h2 := lit_urem_lt (n := w.toNat) ha1 b
  rw [toNat_cast_of_pos hw] at h1 h2; exact ⟨h1, h2⟩
theorem lit_srem_range' {a : Int} (ha0 : 0 ≤ a) (ha1 : a < 2 ^ w.toNat) (b : Int) :
    0 ≤ Prim.lit_srem w a b ∧ Prim.lit_srem w a b < 2 ^ w.toNat := by
  have h1 := lit_srem_nonneg (n := w.toNat) ha0 b; have h2 := lit_srem_lt (n := w.toNat) ha1 b
  rw [toNat_cast_of_pos hw] at h1 h2; exact ⟨h1, h2⟩
theorem lit_smod_range' {a : Int} (ha0 : 0 ≤ a) (ha1 : a < 2 ^ w.toNat) (b : Int) :
    0 ≤ Prim.lit_smod w a b ∧ Prim.lit_smod w a b < 2 ^ w.toNat := by
  have h1 := lit_smod_nonneg (n := w.toNat) ha0 b; have h2 := lit_smod_lt (n := w.toNat) ha1 b
  rw [toNat_cast_of_pos hw] at h1 h2; exact ⟨h1, h2⟩

end

/-! ## Resizing literals (option B) -/


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

theorem rs_ofInt_emod {n : Nat} {k : Int} (hk : k = n) (z : Int) :
    BitVec.ofInt n (z % 2 ^ k.toNat) = BitVec.ofInt n z := by
  subst hk
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_ofInt]

theorem rs_ofInt_emod_nat {n k : Nat} (hk : k = n) (z : Int) :
    BitVec.ofInt n (z % 2 ^ k) = BitVec.ofInt n z := by
  subst hk
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_ofInt]

theorem rs_sext_of {n : Nat} (hn : 0 < n) (z : Int) :
    sext_of (n : Int) z = (BitVec.ofInt n z).toInt := 
  sext_of_eq hn z

theorem rs_ofInt_lit_sext {n m : Nat} (hn : 0 < n) {k : Int} (hm : (n : Int) + k = m) (a : Int) :
    BitVec.ofInt m (Prim.lit_sext k n a) = (BitVec.ofInt n a).signExtend m := by
  rw [Prim.lit_sext, ofInt_masked hm, rs_sext_of hn]
  rfl

theorem rs_ofInt_lit_zext {n m : Nat} {a : Int} (ha0 : 0 ≤ a) (ha1 : a < 2 ^ n) :
    BitVec.ofInt m (Prim.lit_zext a) = (BitVec.ofInt n a).setWidth m := by
  obtain ⟨p, rfl⟩ := Int.eq_ofNat_of_zero_le ha0
  have hp : p < 2 ^ n := by exact_mod_cast ha1
  apply BitVec.eq_of_toNat_eq
  have hx : (BitVec.ofInt n (p : Int)).toNat = p := by
    rw [BitVec.ofInt_natCast, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hp]
  rw [Prim.lit_zext, BitVec.toNat_setWidth, hx, BitVec.toNat_ofInt, ← Int.natCast_emod,
    Int.toNat_natCast]

/-- The existentials of the typing of the resizing nodes, at known widths. -/
theorem rs_exists_pos_eq {a : Int} {p : Int → Prop} :
    (∃ n, 0 < n ∧ a = n ∧ p n) ↔ 0 < a ∧ p a :=
  ⟨fun ⟨_, h1, h2, h3⟩ => by subst h2; exact ⟨h1, h3⟩,
    fun ⟨h1, h2⟩ => ⟨_, h1, rfl, h2⟩⟩

theorem rs_exists_pos_eq₂ {a b : Int} {p : Int → Int → Prop} :
    (∃ n, 0 < n ∧ ∃ m, 0 < m ∧ a = n ∧ b = m ∧ p n m) ↔ 0 < a ∧ 0 < b ∧ p a b :=
  ⟨fun ⟨_, h1, _, h2, h3, h4, h5⟩ => by subst h3 h4; exact ⟨h1, h2, h5⟩,
    fun ⟨h1, h2, h3⟩ => ⟨_, h1, _, h2, rfl, rfl, h3⟩⟩

theorem rs_lit_concat_nat (m p q : Nat) :
    Prim.lit_concat (m : Int) (p : Int) (q : Int) = ((p <<< m ||| q : Nat) : Int) := by
  simp only [Prim.lit_concat, Prim.z_lsl, Prim.zlor, Int.toNat_natCast, Nat.shiftLeft_eq]
  rfl

theorem rs_concat_lt {n m p q : Nat} (hp : (p : Int) < 2 ^ n) (hq : (q : Int) < 2 ^ m) :
    ((p <<< m ||| q : Nat) : Int) < 2 ^ (n + m) := by
  have hp' : p < 2 ^ n := by exact_mod_cast hp
  have hq' : q < 2 ^ m := by exact_mod_cast hq
  have hlt := BitVec.toNat_shiftLeft_or_toNat_lt_two_pow_add (BitVec.ofNat n p) (BitVec.ofNat m q)
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hp', Nat.mod_eq_of_lt hq'] at hlt
  exact_mod_cast hlt

theorem rs_ofInt_append {n m p q : Nat} (hp : (p : Int) < 2 ^ n) (hq : (q : Int) < 2 ^ m) :
    BitVec.ofInt n (p : Int) ++ BitVec.ofInt m (q : Int) =
      BitVec.ofInt (n + m) ((p <<< m ||| q : Nat) : Int) := by
  have hp' : p < 2 ^ n := by exact_mod_cast hp
  have hq' : q < 2 ^ m := by exact_mod_cast hq
  have hx : (BitVec.ofInt n (p : Int)).toNat = p := by
    rw [BitVec.ofInt_natCast, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hp']
  have hy : (BitVec.ofInt m (q : Int)).toNat = q := by
    rw [BitVec.ofInt_natCast, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hq']
  have hlt := rs_concat_lt hp hq
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_append, hx, hy, BitVec.ofInt_natCast, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by exact_mod_cast hlt)]

theorem rs_zasr_nat (p f : Nat) : Prim.zasr (p : Int) (f : Int) = ((p >>> f : Nat) : Int) := by
  simp only [Prim.zasr, Int.toNat_natCast, Nat.shiftRight_eq_div_pow]; norm_cast
theorem rs_toNat_ofInt_nat {w p : Nat} (hp : (p : Int) < 2 ^ w) :
    (BitVec.ofInt w (p : Int)).toNat = p := by
  have : p < 2 ^ w := by exact_mod_cast hp
  rw [BitVec.ofInt_natCast, BitVec.toNat_ofNat, Nat.mod_eq_of_lt this]
theorem rs_extractLsb'_ofInt {w f n p : Nat} (hp : (p : Int) < 2 ^ w) :
    (BitVec.ofInt w (p : Int)).extractLsb' f n = BitVec.ofInt n ((p >>> f : Nat) : Int) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.extractLsb'_toNat, rs_toNat_ofInt_nat hp, BitVec.ofInt_natCast, BitVec.toNat_ofNat]

theorem rs_ofInt_zero (n : Nat) : BitVec.ofInt n 0 = 0#n := by
  apply BitVec.eq_of_toNat_eq; simp

theorem rs_toNat_natCast_add (a b : Nat) : ((a : Int) + (b : Int)).toNat = a + b := by
  omega

/-! ## Lowest set bits and powers of two -/

theorem rs_lowbit_spec : ∀ m : Nat, 0 < m →
    ∃ t, Nat.bitwise (fun a b => a && !b) m (m - 1) = 2 ^ t ∧ 2 ^ t ∣ m
  | m, hm => by
    by_cases ho : m % 2 = 1
    · refine ⟨0, Nat.eq_of_testBit_eq (fun i => ?_), by simp⟩
      rw [Nat.testBit_bitwise rfl]
      cases i with
      | zero => simp [ho]; omega
      | succ i =>
        simp only [Nat.testBit_succ, Nat.pow_zero]
        rw [show (m - 1) / 2 = m / 2 by omega]
        simp
    · have h2 : m / 2 < m := by omega
      obtain ⟨t, ht, hd⟩ := rs_lowbit_spec (m / 2) (by omega)
      refine ⟨t + 1, Nat.eq_of_testBit_eq (fun i => ?_), ?_⟩
      · rw [Nat.pow_add 2 t 1, ← ht, Nat.testBit_mul_two_pow, Nat.testBit_bitwise rfl]
        cases i with
        | zero => simp; omega
        | succ i =>
          simp only [Nat.testBit_succ, Nat.add_sub_cancel]
          rw [Nat.testBit_bitwise rfl, show (m - 1) / 2 = m / 2 - 1 by omega]
          simp
      · rw [Nat.pow_succ]
        have := Nat.mul_dvd_mul hd (Nat.dvd_refl 2)
        rwa [Nat.div_mul_cancel (by omega : 2 ∣ m)] at this
termination_by m => m

/-- The bits of a literal below its lowest set bit are zero. -/
theorem rs_lsb_dvd {p : Nat} {j : Int} (hj0 : 0 ≤ j)
    (hj : j < if (p : Int) = 0 then 128 else Prim.log2 (Prim.z_land (p : Int) (-(p : Int)))) :
    2 ^ (j.toNat + 1) ∣ p := by
  rcases p with _ | k
  · exact Nat.dvd_zero _
  obtain ⟨t, ht, hd⟩ := rs_lowbit_spec (k + 1) (by omega)
  have : Prim.log2 (Prim.z_land ((k + 1 : Nat) : Int) (-((k + 1 : Nat) : Int))) = t := by
    show Prim.log2 (Prim.z_land (Int.ofNat (k + 1)) (Int.negSucc k)) = t
    simp only [Nat.add_sub_cancel] at ht
    simp only [Prim.z_land, Prim.log2, ht]
    exact congrArg Nat.cast (Nat.log2_two_pow (n := t))
  have hne : ((k + 1 : Nat) : Int) ≠ 0 := by omega
  simp only [hne, ↓reduceIte, this] at hj
  exact Nat.dvd_trans (Nat.pow_dvd_pow 2 (by omega)) hd

theorem rs_getLsbD_add_of_dvd {w : Nat} (a b : BitVec w) {q : Nat} (h : 2 ^ q ∣ a.toNat) {p : Nat}
    (hp : p < q) : (a + b).getLsbD p = b.getLsbD p := by
  by_cases hw : p < w
  · simp only [BitVec.getLsbD, BitVec.toNat_add]
    rw [Nat.testBit_mod_two_pow, decide_eq_true hw, Bool.true_and]
    have e1 : (a.toNat + b.toNat).testBit p = ((a.toNat + b.toNat) % 2 ^ q).testBit p := by
      rw [Nat.testBit_mod_two_pow]; simp [hp]
    have e2 : b.toNat.testBit p = (b.toNat % 2 ^ q).testBit p := by
      rw [Nat.testBit_mod_two_pow]; simp [hp]
    rw [e1, e2, Nat.add_mod, (Nat.dvd_iff_mod_eq_zero ..).1 h, Nat.zero_add, Nat.mod_mod]
  · rw [BitVec.getLsbD_of_ge _ _ (by omega), BitVec.getLsbD_of_ge _ _ (by omega)]

theorem rs_log2_nat (p : Nat) : Prim.log2 (p : Int) = (Nat.log2 p : Int) := by
  simp [Prim.log2]

/-- The lowest set bit of a literal (`Bitvec.lsb`), on integers. -/
def rs_lsb (z : Int) : Int := if z = 0 then 128 else Prim.log2 (Prim.z_land z (-z))

/-- Whether a literal is a power of two (`Bitvec.is_pow2`), on integers. -/
def rs_is_pow2 (z : Int) : Bool := decide (z > 0) && decide (Prim.popcount z = 1)

/-- Adding a literal whose lowest set bit is above the extracted bits. -/
theorem rs_extractLsb'_add_lsb {w i n p : Nat} (x : BitVec w) (h1 : (p : Int) < 2 ^ w)
    (hj : (i : Int) + n - 1 < rs_lsb (p : Int)) :
    (BitVec.ofInt w (p : Int) + x).extractLsb' i n = x.extractLsb' i n := by
  rcases n with _ | n
  · exact Subsingleton.elim _ _
  have hp : p < 2 ^ w := by exact_mod_cast h1
  have hd := rs_lsb_dvd (j := (i : Int) + (n + 1 : Nat) - 1) (by omega) hj
  ext t ht
  simp only [BitVec.getElem_extractLsb']
  rw [rs_getLsbD_add_of_dvd _ _ (q := ((i : Int) + (n + 1 : Nat) - 1).toNat + 1)
    (by rw [BitVec.ofInt_natCast, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hp]; exact hd) (by omega)]

theorem rs_extractLsb'_add_lsb' {w i n p : Nat} (x : BitVec w) (h1 : (p : Int) < 2 ^ w)
    (hj : (i : Int) + n - 1 < rs_lsb (p : Int)) :
    (x + BitVec.ofInt w (p : Int)).extractLsb' i n = x.extractLsb' i n := by
  rw [BitVec.add_comm]; exact rs_extractLsb'_add_lsb x h1 hj

theorem rs_pow2 {p : Nat} (h : rs_is_pow2 (p : Int) = true) : p = 2 ^ Nat.log2 p := by
  simp only [rs_is_pow2, Bool.and_eq_true, Prim.popcount, Int.toNat_natCast] at h
  have h2 : popcountNat p = 1 := by exact_mod_cast of_decide_eq_true h.2
  obtain ⟨j, hj⟩ := popcountNat_eq_one h2
  rw [hj, Nat.log2_two_pow]

/-- Multiplying by a power of two above the extracted bits. -/
theorem rs_extractLsb'_mul_pow2 {w i n p : Nat} (x : BitVec w) (hp : rs_is_pow2 (p : Int) = true)
    (hk : (i : Int) + n ≤ Nat.log2 p) :
    (BitVec.ofInt w (p : Int) * x).extractLsb' i n = 0#n := by
  have e := rs_pow2 hp
  have : BitVec.ofInt w (p : Int) = BitVec.twoPow w (Nat.log2 p) := by
    rw [← BitVec.toNat_inj, BitVec.toNat_twoPow, BitVec.ofInt_natCast, BitVec.toNat_ofNat, ← e]
  rw [this, BitVec.twoPow_mul_eq_shiftLeft]
  ext t ht
  simp; omega

theorem rs_extractLsb'_mul_pow2' {w i n p : Nat} (x : BitVec w) (hp : rs_is_pow2 (p : Int) = true)
    (hk : (i : Int) + n ≤ Nat.log2 p) :
    (x * BitVec.ofInt w (p : Int)).extractLsb' i n = 0#n := by
  rw [BitVec.mul_comm]; exact rs_extractLsb'_mul_pow2 x hp hk

/-- The remainder by a power of two below the extracted bits. -/
theorem rs_extractLsb'_umod_pow2 {w n p : Nat} (x : BitVec w) (hp : rs_is_pow2 (p : Int) = true)
    (h1 : (p : Int) < 2 ^ w) (hk : Nat.log2 p < n) :
    (x.extractLsb' 0 n).umod (BitVec.ofInt n (p : Int)) =
      (x.umod (BitVec.ofInt w (p : Int))).extractLsb' 0 n := by
  have e := rs_pow2 hp
  have hkn : p < 2 ^ n := by rw [e]; exact Nat.pow_lt_pow_right (by decide) hk
  have hkw : p < 2 ^ w := by exact_mod_cast h1
  show x.extractLsb' 0 n % BitVec.ofInt n (p : Int) = (x % BitVec.ofInt w (p : Int)).extractLsb' 0 n
  rw [← BitVec.toNat_inj]
  simp only [BitVec.toNat_umod, BitVec.extractLsb'_toNat, Nat.shiftRight_zero, BitVec.ofInt_natCast,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt hkw, Nat.mod_eq_of_lt hkn]
  rw [Nat.mod_mod_of_dvd _ (by rw [e]; exact Nat.pow_dvd_pow 2 (by omega))]
  have hp0 : 0 < p := by rw [e]; exact Nat.two_pow_pos _
  exact (Nat.mod_eq_of_lt (Nat.lt_trans (Nat.mod_lt _ hp0) hkn)).symm


/-! ## Shift amounts -/

theorem toNat_ofInt_lt {m : Nat} {z : Int} (h0 : 0 ≤ z) (h1 : z < 2 ^ m) :
    (BitVec.ofInt m z).toNat = z.toNat := by
  have e : ((2 ^ m : Nat) : Int) = (2 : Int) ^ m := by simp
  rw [BitVec.toNat_ofInt, e, Int.emod_eq_of_lt h0 h1]

theorem toNat_ofInt_le {m : Nat} {z : Int} (h0 : 0 ≤ z) (h1 : z ≤ m) :
    (BitVec.ofInt m z).toNat = z.toNat := by
  have : (m : Int) < 2 ^ m := by
    have := Nat.lt_two_pow_self (n := m)
    have e : ((2 ^ m : Nat) : Int) = (2 : Int) ^ m := by simp
    omega
  exact toNat_ofInt_lt h0 (by omega)

theorem ofInt_ones (m : Nat) : BitVec.ofInt m (z_lsl 1 (m : Int) - 1) = BitVec.allOnes m := by
  apply BitVec.eq_of_toNat_eq
  have e : ((2 ^ m : Nat) : Int) = (2 : Int) ^ m := by simp
  have hp : (0 : Int) < 2 ^ m := Int.pow_pos (by decide)
  have hz : z_lsl 1 (m : Int) = 2 ^ m := by simp [Prim.z_lsl]
  rw [hz, toNat_ofInt_lt (by omega) (by omega), BitVec.toNat_allOnes]
  omega

theorem sigma_bv_ext {A B : Nat} {x : BitVec A} {y : BitVec B} (h : A = B)
    (hx : ∀ i, x.getLsbD i = y.getLsbD i) : (⟨A, x⟩ : (n : Nat) × BitVec n) = ⟨B, y⟩ := by
  subst h; congr 1; exact BitVec.eq_of_getLsbD_eq (fun i _ => hx i)

/-! ## Divisions and remainders of values (option B) -/

theorem ovf_comm {n : Nat} (x y : BitVec n) : (x.saddOverflow y = y.saddOverflow x) ∧
    (x.uaddOverflow y = y.uaddOverflow x) ∧ (x.smulOverflow y = y.smulOverflow x) ∧
    (x.umulOverflow y = y.umulOverflow x) := by
  simp [BitVec.saddOverflow, BitVec.uaddOverflow, BitVec.smulOverflow,
    BitVec.umulOverflow, Int.add_comm, Nat.add_comm, Int.mul_comm, Nat.mul_comm]

theorem smtUDiv_toNat {n : Nat} {a b : BitVec n} (hb : b.toNat ≠ 0) :
    (a.smtUDiv b).toNat = a.toNat / b.toNat := by
  simp [BitVec.smtUDiv_eq, ← BitVec.toNat_inj, hb]

section
variable {w : Nat} {x y : BitVec w}


theorem uadd_ok : x.uaddOverflow y = false ↔ x.toNat + y.toNat < 2 ^ w := by
  simp [BitVec.uaddOverflow]

theorem umul_ok : x.umulOverflow y = false ↔ x.toNat * y.toNat < 2 ^ w := by
  simp [BitVec.umulOverflow]

theorem toNat_add_ok (h : x.uaddOverflow y = false) : (x + y).toNat = x.toNat + y.toNat :=
  BitVec.toNat_add_of_not_uaddOverflow (by simp [h])

theorem toNat_mul_ok (h : x.umulOverflow y = false) : (x * y).toNat = x.toNat * y.toNat :=
  BitVec.toNat_mul_of_not_umulOverflow (by simp [h])

end

section
variable {w : Nat}


theorem umod_add_self {d v : BitVec w} (h : d.uaddOverflow v = false) : (d + v) % d = v % d := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_umod, BitVec.toNat_umod, toNat_add_ok h, Nat.add_mod_left]

theorem umod_add_self' {d v : BitVec w} (h : v.uaddOverflow d = false) : (v + d) % d = v % d := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_umod, BitVec.toNat_umod, toNat_add_ok h, Nat.add_mod_right]

theorem umod_umod_of_le {v a b : BitVec w} (ha : 0 < a.toNat) (h : a.toNat ≤ b.toNat) :
    v % a % b = v % a := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_umod]
  exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt _ ha) h)

theorem umod_umod_of_dvd {v a b : BitVec w} (h : b.toNat ∣ a.toNat) : v % a % b = v % b := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_umod, Nat.mod_mod_of_dvd _ h]

theorem umod_umod_of_lt {v a b : BitVec w} (hb : 0 < b.toNat) (h : b.toNat < a.toNat)
    (hd : b.toNat ∣ a.toNat ∨ a.toNat ∣ b.toNat) : v % a % b = v % b := by
  rcases hd with hd | hd
  · exact umod_umod_of_dvd hd
  · have := Nat.le_of_dvd hb hd; omega

theorem mul_div_ok {w : Nat} {n d x : BitVec w} (hd0 : d.toNat ≠ 0) (hd : d.toNat ∣ n.toNat)
    (h : n.umulOverflow x = false) :
    x.umulOverflow (n.smtUDiv d) = false ∧ x * n.smtUDiv d = (n * x).smtUDiv d := by
  obtain ⟨q, hq⟩ := hd
  have hc : (n.smtUDiv d).toNat = q := by
    rw [smtUDiv_toNat hd0, hq, Nat.mul_div_cancel_left _ (by omega)]
  have e := toNat_mul_ok h
  rw [umul_ok] at h
  have l : x.toNat * q ≤ n.toNat * x.toNat := by
    rw [hq, Nat.mul_comm, Nat.mul_assoc]; exact Nat.le_mul_of_pos_left _ (by omega)
  have o : x.umulOverflow (n.smtUDiv d) = false := by rw [umul_ok, hc]; omega
  refine ⟨o, BitVec.eq_of_toNat_eq ?_⟩
  rw [toNat_mul_ok o, hc, smtUDiv_toNat hd0, e, hq, Nat.mul_assoc,
    Nat.mul_div_cancel_left _ (by omega), Nat.mul_comm]

theorem div_mul_ok {w : Nat} {n d x : BitVec w} (hn0 : n.toNat ≠ 0) (hd : n.toNat ∣ d.toNat)
    (h : n.umulOverflow x = false) : x.smtUDiv (d.smtUDiv n) = (n * x).smtUDiv d := by
  obtain ⟨q, hq⟩ := hd
  have hc : (d.smtUDiv n).toNat = q := by
    rw [smtUDiv_toNat hn0, hq, Nat.mul_div_cancel_left _ (by omega)]
  by_cases hq0 : q = 0
  · have h1 : d.smtUDiv n = 0#w := BitVec.eq_of_toNat_eq (by simp [hc, hq0])
    have h2 : d = 0#w := BitVec.eq_of_toNat_eq (by simp [hq, hq0])
    rw [h1, h2]; simp [BitVec.smtUDiv_eq]
  · have e := toNat_mul_ok h
    apply BitVec.eq_of_toNat_eq
    have hd0 : d.toNat ≠ 0 := by rw [hq]; exact Nat.mul_ne_zero hn0 hq0
    rw [smtUDiv_toNat (b := d.smtUDiv n) (by omega), smtUDiv_toNat (a := n * x) hd0, hc, e, hq,
      Nat.mul_div_mul_left _ _ (by omega)]

theorem div_div_ok {w : Nat} {a b x : BitVec w} (ha : a.toNat ≠ 0)
    (h : a.umulOverflow b = false) : (x.smtUDiv a).smtUDiv b = x.smtUDiv (a * b) := by
  have e := toNat_mul_ok h
  by_cases hb : b.toNat = 0
  · have h0 : b = 0#w := BitVec.eq_of_toNat_eq (by simp [hb])
    subst h0; simp [BitVec.smtUDiv_eq]
  · have hab : (a * b).toNat ≠ 0 := by rw [e]; exact Nat.mul_ne_zero ha hb
    apply BitVec.eq_of_toNat_eq
    rw [smtUDiv_toNat hb, smtUDiv_toNat ha, smtUDiv_toNat hab, e, Nat.div_div_eq_div_mul]

theorem mul_div_ok' {w : Nat} {n d x : BitVec w} (hd0 : d.toNat ≠ 0) (hd : d.toNat ∣ n.toNat)
    (h : x.umulOverflow n = false) :
    x.umulOverflow (n.smtUDiv d) = false ∧ x * n.smtUDiv d = (x * n).smtUDiv d := by
  rw [(ovf_comm _ _).2.2.2] at h
  have := mul_div_ok hd0 hd h
  rwa [BitVec.mul_comm n x] at this

theorem div_mul_ok' {w : Nat} {n d x : BitVec w} (hn0 : n.toNat ≠ 0) (hd : n.toNat ∣ d.toNat)
    (h : x.umulOverflow n = false) : x.smtUDiv (d.smtUDiv n) = (x * n).smtUDiv d := by
  rw [(ovf_comm _ _).2.2.2] at h
  rw [BitVec.mul_comm x n]
  exact div_mul_ok hn0 hd h

end


theorem toNat_ofInt_nat {n a : Nat} (ha1 : (a : Int) < 2 ^ n) : (BitVec.ofInt n (a : Int)).toNat = a := by
  rw [toNat_ofInt_lt (by omega) ha1]; simp

theorem umod_umod_le_ofInt {n a b : Nat} {v : BitVec n} (ha : 0 < (a : Int)) (ha1 : (a : Int) < 2 ^ n)
    (hb1 : (b : Int) < 2 ^ n) (h : (a : Int) ≤ b) :
    v.umod (BitVec.ofInt n a) = (v.umod (BitVec.ofInt n a)).umod (BitVec.ofInt n b) :=
  (umod_umod_of_le (by rw [toNat_ofInt_nat ha1]; omega)
    (by rw [toNat_ofInt_nat ha1, toNat_ofInt_nat hb1]; omega)).symm

theorem umod_umod_lt_ofInt {n a b : Nat} {v : BitVec n} (hb : 0 < (b : Int)) (ha1 : (a : Int) < 2 ^ n)
    (hb1 : (b : Int) < 2 ^ n) (h : ¬(a : Int) ≤ b)
    (hd : divisible (a : Int) b = true ∨ divisible (b : Int) a = true) :
    v.umod (BitVec.ofInt n b) = (v.umod (BitVec.ofInt n a)).umod (BitVec.ofInt n b) := by
  simp only [divisible, Prim.divisible, decide_eq_true_eq, Int.natCast_dvd_natCast] at hd
  refine (umod_umod_of_lt (by rw [toNat_ofInt_nat hb1]; omega)
    (by rw [toNat_ofInt_nat ha1, toNat_ofInt_nat hb1]; omega) ?_).symm
  rw [toNat_ofInt_nat ha1, toNat_ofInt_nat hb1]; exact hd

theorem dvd_of_divisible {a b : Nat} (h : divisible (a : Int) b = true) : b ∣ a := by
  simpa [divisible, Prim.divisible, Int.natCast_dvd_natCast] using h

theorem mul_div_ofInt {w n d : Nat} {x : BitVec w} (hd0 : (d : Int) ≠ 0) (hn1 : (n : Int) < 2 ^ w)
    (hd1 : (d : Int) < 2 ^ w) (hdv : divisible (n : Int) d = true)
    (h : (BitVec.ofInt w n).umulOverflow x = false) :
    x.umulOverflow ((BitVec.ofInt w n).smtUDiv (BitVec.ofInt w d)) = false ∧
      x * (BitVec.ofInt w n).smtUDiv (BitVec.ofInt w d) =
        (BitVec.ofInt w n * x).smtUDiv (BitVec.ofInt w d) :=
  mul_div_ok (by rw [toNat_ofInt_nat hd1]; omega)
    (by rw [toNat_ofInt_nat hd1, toNat_ofInt_nat hn1]; exact dvd_of_divisible hdv) h

theorem mul_div_ovf {w n d : Nat} {x : BitVec w} (hd0 : (d : Int) ≠ 0) (hn1 : (n : Int) < 2 ^ w)
    (hd1 : (d : Int) < 2 ^ w) (hdv : divisible (n : Int) d = true)
    (h : (BitVec.ofInt w n).umulOverflow x = false) :
    x.umulOverflow ((BitVec.ofInt w n).smtUDiv (BitVec.ofInt w d)) = false :=
  (mul_div_ofInt hd0 hn1 hd1 hdv h).1

theorem mul_div_eq {w n d : Nat} {x : BitVec w} (hd0 : (d : Int) ≠ 0) (hn1 : (n : Int) < 2 ^ w)
    (hd1 : (d : Int) < 2 ^ w) (hdv : divisible (n : Int) d = true)
    (h : (BitVec.ofInt w n).umulOverflow x = false) :
    x * (BitVec.ofInt w n).smtUDiv (BitVec.ofInt w d) =
      (BitVec.ofInt w n * x).smtUDiv (BitVec.ofInt w d) :=
  (mul_div_ofInt hd0 hn1 hd1 hdv h).2

theorem div_mul_ofInt {w n d : Nat} {x : BitVec w} (hn0 : (n : Int) ≠ 0) (hn1 : (n : Int) < 2 ^ w)
    (hd1 : (d : Int) < 2 ^ w) (hdv : divisible (d : Int) n = true)
    (h : (BitVec.ofInt w n).umulOverflow x = false) :
    x.smtUDiv ((BitVec.ofInt w d).smtUDiv (BitVec.ofInt w n)) =
      (BitVec.ofInt w n * x).smtUDiv (BitVec.ofInt w d) :=
  div_mul_ok (by rw [toNat_ofInt_nat hn1]; omega)
    (by rw [toNat_ofInt_nat hd1, toNat_ofInt_nat hn1]; exact dvd_of_divisible hdv) h

theorem div_div_ofInt {w n d : Nat} {x : BitVec w} (hn0 : (n : Int) ≠ 0) (hn1 : (n : Int) < 2 ^ w)
    (hd1 : (d : Int) < 2 ^ w) (hov : (n : Int) * d ≤ 2 ^ w - 1) :
    x.smtUDiv (BitVec.ofInt w (Prim.lit_mul w n d)) =
      (x.smtUDiv (BitVec.ofInt w n)).smtUDiv (BitVec.ofInt w d) := by
  have hm : BitVec.ofInt w (Prim.lit_mul w n d) = BitVec.ofInt w n * BitVec.ofInt w d :=
    LitOps.ofInt_lit_mul _ _
  rw [hm, div_div_ok (by rw [toNat_ofInt_nat hn1]; omega)]
  rw [umul_ok, toNat_ofInt_nat hn1, toNat_ofInt_nat hd1]
  have e : ((n * d : Nat) : Int) = (n : Int) * d := by simp
  have e2 : ((2 ^ w : Nat) : Int) = (2 : Int) ^ w := by simp
  omega

theorem pow2_of_popcount {r : Int} (h : Prim.popcount r = 1) : ∃ k : Nat, r = 2 ^ k := by
  simp only [Prim.popcount] at h
  have h' : popcountNat r.toNat = 1 := by exact_mod_cast h
  obtain ⟨j, hj⟩ := popcountNat_eq_one h'
  have hr : 0 < r.toNat := by rw [hj]; exact Nat.two_pow_pos _
  refine ⟨j, ?_⟩
  have e : ((2 ^ j : Nat) : Int) = (2 : Int) ^ j := by simp
  omega

theorem log2_two_pow (k : Nat) : Prim.log2 ((2 : Int) ^ k) = k := by
  rw [show (2 : Int) ^ k = ((2 ^ k : Nat) : Int) by simp, Prim.log2, Int.toNat_natCast,
    Nat.log2_two_pow]

theorem ofInt_two_pow_toNat {W k : Nat} (hk : (2 : Int) ^ k < 2 ^ W) :
    (BitVec.ofInt W ((2 : Int) ^ k)).toNat = 2 ^ k := by
  rw [toNat_ofInt_lt (Int.le_of_lt (Int.pow_pos (by decide))) hk]
  rw [show (2 : Int) ^ k = ((2 ^ k : Nat) : Int) by simp, Int.toNat_natCast]

theorem nat_two_pow_lt {k W : Nat} (hk : (2 : Int) ^ k < 2 ^ W) : 2 ^ k < 2 ^ W := by
  have e1 : ((2 ^ k : Nat) : Int) = (2 : Int) ^ k := by simp
  have e2 : ((2 ^ W : Nat) : Int) = (2 : Int) ^ W := by simp
  omega

theorem extract_mul_pow2 {W k i n : Nat} (x : BitVec W) (hk : (2 : Int) ^ k < 2 ^ W)
    (h : i + n ≤ k) : 0#n = (BitVec.ofInt W ((2 : Int) ^ k) * x).extractLsb' i n := by
  have hkW : k < W := (Nat.pow_lt_pow_iff_right (by decide)).1 (nat_two_pow_lt hk)
  have : BitVec.ofInt W ((2 : Int) ^ k) = BitVec.twoPow W k := by
    apply BitVec.eq_of_toNat_eq
    rw [ofInt_two_pow_toNat hk, BitVec.toNat_twoPow, Nat.mod_eq_of_lt (nat_two_pow_lt hk)]
  rw [this, BitVec.twoPow_mul_eq_shiftLeft]
  ext t ht
  simp; omega

theorem extract_umod_pow2 {W k n : Nat} (x : BitVec W) (hk : (2 : Int) ^ k < 2 ^ W) (hkn : k < n) :
    (x.extractLsb' 0 n).umod (BitVec.ofInt n ((2 : Int) ^ k)) =
      (x.umod (BitVec.ofInt W ((2 : Int) ^ k))).extractLsb' 0 n := by
  have hkn' : (2 : Int) ^ k < 2 ^ n := by
    have := Nat.pow_lt_pow_right (a := 2) (by decide) hkn
    have e1 : ((2 ^ k : Nat) : Int) = (2 : Int) ^ k := by simp
    have e2 : ((2 ^ n : Nat) : Int) = (2 : Int) ^ n := by simp
    omega
  show x.extractLsb' 0 n % BitVec.ofInt n ((2 : Int) ^ k) =
    (x % BitVec.ofInt W ((2 : Int) ^ k)).extractLsb' 0 n
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_umod, BitVec.extractLsb'_toNat, Nat.shiftRight_zero,
    ofInt_two_pow_toNat hk, ofInt_two_pow_toNat hkn']
  rw [Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by omega))]
  have hlt : x.toNat % 2 ^ k < 2 ^ n :=
    Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos k)) (Nat.pow_le_pow_right (by omega) (by omega))
  exact (Nat.mod_eq_of_lt hlt).symm

theorem pos_masked_two_pow {m : Int} {k : Nat} (hk : (k : Int) < m) :
    0 < Prim.masked m ((2 : Int) ^ k) % 2 ^ m.toNat := by
  have hlt : (2 : Int) ^ k < 2 ^ m.toNat := by
    have := Nat.pow_lt_pow_right (a := 2) (by decide) (show k < m.toNat by omega)
    have e1 : ((2 ^ k : Nat) : Int) = (2 : Int) ^ k := by simp
    have e2 : ((2 ^ m.toNat : Nat) : Int) = (2 : Int) ^ m.toNat := by simp
    omega
  have hp : (0 : Int) < 2 ^ k := Int.pow_pos (by decide)
  simp only [Prim.masked, Int.emod_emod_of_dvd _ (Int.dvd_refl _)]
  rw [Int.emod_eq_of_lt (by omega) hlt]; exact hp

theorem one_le_of_two_pow_gt {k : Nat} (h : (2 : Int) ^ k > 1) : 1 ≤ k := by
  rcases k with _ | k
  · simp at h
  · omega

theorem rem_pow2_eq {W k n : Nat} (w : BitVec W) (hn : n = k) (hkW : k ≤ W)
    (hk : (2 : Int) ^ k < 2 ^ W) :
    BitVec.setWidth W (BitVec.extractLsb' 0 n w) = w.umod (BitVec.ofInt W ((2 : Int) ^ k)) := by
  subst hn
  show _ = w % BitVec.ofInt W ((2 : Int) ^ n)
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.extractLsb'_toNat, Nat.shiftRight_zero, BitVec.toNat_umod,
    ofInt_two_pow_toNat hk]
  exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos _))
    (Nat.pow_le_pow_right (by decide) hkW))

theorem lt_of_two_pow_lt {k W : Nat} (h : (2 : Int) ^ k < 2 ^ W) : k < W :=
  (Nat.pow_lt_pow_iff_right (by decide)).1 (nat_two_pow_lt h)

theorem lt_two_pow_log2 {z w : Int} (hz : 0 < z) (h : Prim.log2 z < w) : z < 2 ^ w.toNat := by
  have hl := Nat.lt_log2_self (n := z.toNat)
  have hle : 2 ^ (Nat.log2 z.toNat + 1) ≤ 2 ^ w.toNat :=
    Nat.pow_le_pow_right (by omega) (by simp only [Prim.log2] at h; omega)
  have e : ((2 ^ w.toNat : Nat) : Int) = (2 : Int) ^ w.toNat := by simp
  omega

theorem lt_two_pow_log2_nat {z W : Nat} (h : Prim.log2 (z : Int) < (W : Int)) (hz : 0 < (z : Int)) :
    (z : Int) < 2 ^ W := by
  simpa using lt_two_pow_log2 hz h

theorem zext_div_ofInt {W K z : Nat} (x : BitVec W) (hz0 : 0 < z) (hz : (z : Int) < 2 ^ W) :
    BitVec.setWidth (W + K) (x.smtUDiv (BitVec.ofInt W z)) =
      (BitVec.setWidth (W + K) x).smtUDiv (BitVec.ofInt (W + K) z) := by
  have hz' : z < 2 ^ W := by
    have e : ((2 ^ W : Nat) : Int) = (2 : Int) ^ W := by simp
    omega
  have hzK : (z : Int) < 2 ^ (W + K) := by
    have := Nat.pow_le_pow_right (n := 2) (by decide) (show W ≤ W + K by omega)
    have e : ((2 ^ (W + K) : Nat) : Int) = (2 : Int) ^ (W + K) := by simp
    omega
  have hk : (BitVec.ofInt (W + K) (z : Int)).toNat = z := toNat_ofInt_nat hzK
  have hset : (BitVec.ofInt (W + K) (z : Int)).setWidth W = BitVec.ofInt W z := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_setWidth, hk, toNat_ofInt_nat hz, Nat.mod_eq_of_lt hz']
  have := x.isLt
  have hp : 2 ^ W ≤ 2 ^ (W + K) := Nat.pow_le_pow_right (by omega) (by omega)
  have h1 : (BitVec.ofInt (W + K) (z : Int)).toNat ≠ 0 := by rw [hk]; omega
  have h2 : (BitVec.ofInt W (z : Int)).toNat ≠ 0 := by rw [toNat_ofInt_nat hz]; omega
  have hd := Nat.div_le_self x.toNat z
  apply BitVec.eq_of_toNat_eq
  rw [smtUDiv_toNat h1, BitVec.toNat_setWidth, BitVec.toNat_setWidth, smtUDiv_toNat h2, hk,
    toNat_ofInt_nat hz, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]

theorem extract_add_lsb {W i n p j : Nat} (x : BitVec W) (h1 : (p : Int) < 2 ^ W)
    (hj : (j : Int) < rs_lsb p) (hij : i + n ≤ j + 1) :
    x.extractLsb' i n = (BitVec.ofInt W (p : Int) + x).extractLsb' i n :=
  (rs_extractLsb'_add_lsb x h1 (by omega)).symm

theorem int_two_pow_pos (n : Nat) : (0 : Int) < 2 ^ n := Int.pow_pos (by decide)

theorem emod_range (z : Int) (k : Nat) : 0 ≤ z % 2 ^ k ∧ z % 2 ^ k < 2 ^ k :=
  ⟨Int.emod_nonneg _ (Int.ne_of_gt (Int.pow_pos (by decide))), Int.emod_lt_of_pos _ (Int.pow_pos (by decide))⟩

section
variable {w : Int}
theorem lit_shl_range (a b : Int) : 0 ≤ Prim.lit_shl w a b ∧ Prim.lit_shl w a b < 2 ^ w.toNat :=
  ⟨lit_shl_nonneg a b, lit_shl_lt a b⟩
theorem lit_lshr_range (a b : Int) : 0 ≤ Prim.lit_lshr w a b ∧ Prim.lit_lshr w a b < 2 ^ w.toNat :=
  ⟨lit_lshr_nonneg a b, lit_lshr_lt a b⟩
theorem lit_ashr_range (a b : Int) : 0 ≤ Prim.lit_ashr w a b ∧ Prim.lit_ashr w a b < 2 ^ w.toNat :=
  ⟨lit_ashr_nonneg a b, lit_ashr_lt a b⟩
theorem lit_udiv_range (a b : Int) : 0 ≤ Prim.lit_udiv w a b ∧ Prim.lit_udiv w a b < 2 ^ w.toNat :=
  ⟨lit_udiv_nonneg a b, lit_udiv_lt a b⟩
theorem masked_range (z : Int) : 0 ≤ masked w z ∧ masked w z < 2 ^ w.toNat :=
  ⟨masked_nonneg _ _, masked_lt _ _⟩
end

section
variable {S : Kanon.Sem} [KanonBool.Lang S] [CoreMod.Lang S] [Lang S] [Typed S]

/-- A well-typed positive literal is not zero. -/
theorem nonzero_lit_of_wt {z : Int} {t : S.Ty} (hz : 0 < z) (w : S.WT (mk (.BitVec z) t)) :
    Nonzero (mk (.BitVec z) t) := by
  rw [WT_mk] at w
  obtain ⟨⟨⟨n, hn, rfl⟩, hwf⟩, -⟩ := w
  obtain ⟨-, hz1⟩ := hwf n (.inl rfl)
  intro ρ m x e
  rw [ev_mk] at e
  simp only [Node.map, Node.eval, ofBV_some, Option.some.injEq] at e
  simp only [bv, Kanon.Embed.inj_eq_iff, Sigma.mk.injEq] at e
  obtain ⟨rfl, e⟩ := e
  rw [← eq_of_heq e]
  intro h0
  have := congrArg BitVec.toNat h0
  rw [BitVec.toNat_ofInt, width_sort ρ (.inl rfl) hn] at this
  have e2 : ((2 ^ n.toNat : Nat) : Int) = (2 : Int) ^ n.toNat := by simp
  rw [e2, Int.emod_eq_of_lt (by omega) hz1] at this
  simp at this; omega

/-- A literal `mk_bv m z` whose masked value is positive is not zero. -/
theorem nonzero_mk_bv {m z : Int} (hm : 0 < m) (hz : 0 < z % 2 ^ m.toNat) :
    Nonzero (mk_bv (S := S) m z) := by
  have hp : (0 : Int) < 2 ^ m.toNat := Int.pow_pos (by decide)
  refine nonzero_lit_of_wt hz ?_
  rw [WT_mk]
  simp only [Node.wt, bv_wf, Node.All, sort_inj_iff, Srt.TBitVector.injEq, reduceCtorEq, or_false]
  exact ⟨⟨⟨m, hm, rfl⟩, fun n hn => by subst hn; exact ⟨Int.emod_nonneg _ (by omega),
    Int.emod_lt_of_pos _ hp⟩⟩, trivial⟩

/-- The literal of a product of literals that does not overflow, the divisor `d` being not
zero. -/
theorem nonzero_mk_bv_mul {m n d : Int} {t : S.Ty} (hm : 0 < m) (ht : t = sort (.TBitVector m))
    (hn : n ≠ 0) (hn0 : 0 ≤ n) (hd0 : 0 ≤ d) (hdw : d < 2 ^ m.toNat)
    (hov : n * d ≤ 2 ^ m.toNat - 1) (hd : Nonzero (mk (.BitVec d) t)) :
    Nonzero (mk_bv (S := S) m (Prim.lit_mul m n d)) := by
  intro ρ k x e
  have hd' : d ≠ 0 := by
    rintro rfl
    subst ht
    have := hd ρ _ (BitVec.ofInt _ 0) (by rw [ev_mk]; rfl)
    exact this (by apply BitVec.eq_of_toNat_eq; simp)
  have hp : (0 : Int) < n * d := by
    rcases Int.lt_or_gt_of_ne hn with h | h <;> rcases Int.lt_or_gt_of_ne hd' with h' | h'
    all_goals first | omega | exact Int.mul_pos h h'
  refine nonzero_mk_bv hm ?_ ρ k x e
  simp only [Prim.lit_mul, Prim.masked, Int.emod_emod_of_dvd _ (Int.dvd_refl _)]
  rw [Int.emod_eq_of_lt (by omega) (by omega)]; exact hp

/-- The literal of a quotient of literals by a divisor of the dividend, which is not zero. -/
theorem nonzero_mk_bv_udiv {m n d : Int} {t : S.Ty} (hm : 0 < m) (ht : t = sort (.TBitVector m))
    (hn : n ≠ 0) (hn0 : 0 ≤ n) (hn1 : n < 2 ^ m.toNat) (hd0 : 0 ≤ d) (hdw : d < 2 ^ m.toNat)
    (hdv : divisible d n = true) (hd : Nonzero (mk (.BitVec d) t)) :
    Nonzero (mk_bv (S := S) m (Prim.lit_udiv m d n)) := by
  intro ρ k x e
  have hd' : d ≠ 0 := by
    rintro rfl
    subst ht
    have := hd ρ _ (BitVec.ofInt _ 0) (by rw [ev_mk]; rfl)
    exact this (by apply BitVec.eq_of_toNat_eq; simp)
  simp only [divisible, Prim.divisible, decide_eq_true_eq] at hdv
  obtain ⟨q, hq⟩ := hdv
  have hq0 : 0 < q := by
    rcases Int.lt_trichotomy q 0 with h | h | h
    · have := Int.mul_neg_of_pos_of_neg (by omega : 0 < n) h; omega
    · subst h; simp at hq; omega
    · exact h
  have hqd : q ≤ d := by
    rw [hq]; have := Int.mul_le_mul_of_nonneg_right (show 1 ≤ n by omega) (Int.le_of_lt hq0); omega
  have ht : Prim.tdiv d n = q := by
    rw [Prim.tdiv, hq, Int.mul_tdiv_cancel_left _ hn]
  refine nonzero_mk_bv hm ?_ ρ k x e
  have hmn' : n % 2 ^ m.toNat = n := Int.emod_eq_of_lt hn0 hn1
  simp only [Prim.lit_udiv, Prim.masked, hmn', hn, ↓reduceIte, ht,
    Int.emod_emod_of_dvd _ (Int.dvd_refl _)]
  rw [Int.emod_eq_of_lt (by omega) (by omega)]; exact hq0

/-- A literal that is not zero (in an environment) is not `0`. -/
theorem ne_zero_of_nonzero_lit (ρ : S.Env) {z : Int} {t : S.Ty} (h : Nonzero (mk (.BitVec z) t)) :
    z ≠ 0 := by
  rintro rfl
  have := h ρ _ (BitVec.ofInt _ 0) (by rw [ev_mk]; rfl)
  exact this (by apply BitVec.eq_of_toNat_eq; simp)

/-- The most significant bit of a positive literal. -/
theorem msb_of_lit_pos {z : Int} {t : S.Ty} (hz : 0 < z) :
    Bitvec.msb_of (mk (.BitVec z) t) = log2 z := by
  rw [Bitvec.msb_of]
  simp [Kanon.firstSome]
  split
  · rename_i z1 h
    simp only [proj_mk, Option.some.injEq, Node.BitVec.injEq] at h
    subst h
    simp [hz]
  · rename_i h
    simp at h

/-- The literal `z` masked to `m` bits, when its most significant bit is below `m`. -/
theorem nonzero_masked_of {z m : Int} {t : S.Ty} (hm : 0 < m) (h : Nonzero (mk (.BitVec z) t))
    (hz0 : 0 ≤ z) (hmsb : Bitvec.msb_of (mk (.BitVec z) t) < m) :
    Nonzero (mk_masked (S := S) m z) := by
  intro ρ k x e
  have hz : 0 < z := by have := ne_zero_of_nonzero_lit ρ h; omega
  rw [msb_of_lit_pos hz] at hmsb
  have hlt := lt_two_pow_log2 hz hmsb
  exact nonzero_mk_bv hm (by rw [Int.emod_eq_of_lt hz0 hlt]; exact hz) ρ k x e

end

end BitvecMod.ResizeLib

namespace BitvecMod

open Lean Meta Elab Tactic in
/-- Replaces the integer variables that `omega` proves nonnegative (the widths, the bounds of
the extractions, the amounts of the extensions and shifts, and the literals) by natural
numbers (option B's `rsNatVars`). -/
partial def rsNatVars : TacticM Unit := do
  let g ← getMainGoal
  let decls ← g.withContext do return (← getLCtx).decls.toList.filterMap id
  for d in decls do
    if d.isImplementationDetail then continue
    let isInt ← g.withContext do isDefEq d.type (mkConst ``Int)
    unless isInt && d.isLet == false do continue
    let le ← g.withContext do mkAppM ``LE.le #[toExpr (0 : Int), d.toExpr]
    let pf ← g.withContext do mkFreshExprMVar le
    let ok ← try
        pure (← Tactic.run pf.mvarId! (evalTactic (← `(tactic| omega)))).isEmpty
      catch _ => pure false
    unless ok do continue
    let r ← g.withContext do
      let pf ← mkAppM ``Int.eq_ofNat_of_zero_le #[← instantiateMVars pf]
      let (h, g) ← (← g.assert `hw (← inferType pf) pf).intro1P
      let [sg] := (← g.cases h).toList | return none
      let heq := sg.fields[1]!.fvarId!
      let some sg' ← observing? (subst sg.mvarId heq) | return none
      return some sg'
    let some g' := r | continue
    replaceMainGoal [g']
    return ← rsNatVars
  return

open Lean Elab Tactic in
elab "rs_nat" : tactic => rsNatVars

open Lean Meta in
/-- A natural number whose cast is the integer `e`, by its structure: casts of natural numbers,
literals, sums, differences and products (the differences are checked by `omega` with the
equation that uses it). -/
partial def natForm? (e : Expr) : MetaM (Option Expr) := do
  let e := e.cleanupAnnotations
  if e.isAppOfArity ``Nat.cast 3 then return some (e.getArg! 2)
  if let some k := e.int? then
    if 0 ≤ k then return some (mkNatLit k.toNat) else return none
  for (op, nop) in [(``HAdd.hAdd, ``HAdd.hAdd), (``HSub.hSub, ``HSub.hSub), (``HMul.hMul, ``HMul.hMul)] do
    if e.isAppOfArity op 6 then
      let some a ← natForm? (e.getArg! 4) | return none
      let some b ← natForm? (e.getArg! 5) | return none
      return some (← mkAppM nop #[a, b])
  return none

open Lean Meta Elab Tactic in
/-- Generalizes the terms `Int.toNat e` of the goal and the hypotheses (the widths of the
values, in dependent positions) to natural numbers `m`, with `e.toNat = m`, for `omega`. -/
partial def rsGenToNat (fuel : Nat := 32) : TacticM Unit := withMainContext do
  if fuel = 0 then return
  let g ← getMainGoal
  let isDef (e : Expr) : Bool := match e.eq? with
    | some (_, l, _) => l.isAppOfArity ``Int.toNat 1
    | none => false
  let mut exprs := #[← instantiateMVars (← g.getType)]
  for d in (← getLCtx) do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    if isDef ty then continue
    exprs := exprs.push ty
  let mut found := none
  for e in exprs do
    if let some t := e.find? (fun t => t.isAppOfArity ``Int.toNat 1 && !t.hasLooseBVars &&
        !t.hasMVar && !(t.getArg! 0).isRawNatLit) then
      found := some t; break
  let some t := found | return
  let stx ← Term.exprToSyntax t
  evalTactic (← `(tactic| generalize $(mkIdent `rs_h) : $stx = $(mkIdent `rs_m) at *))
  -- the natural number that `e` is, when its structure gives one (`(↑a + ↑b).toNat = a + b`)
  if let some n ← natForm? (t.getArg! 0) then
    withMainContext do
      let sx ← Term.exprToSyntax n
      try
        evalTactic (← `(tactic| have $(mkIdent `rs_e) : $(mkIdent `rs_m) = $sx := by omega))
        evalTactic (← `(tactic| subst $(mkIdent `rs_e)))
      catch _ => pure ()
  rsGenToNat (fuel - 1)

elab "rs_gen_toNat" : tactic => rsGenToNat

open Lean Meta Elab Tactic in
/-- Rewrites the goal with the hypotheses `S.ty x = e` on term variables, by `rw`, which (unlike
`simp`) also rewrites the dependent positions (the widths of the values). -/
elab "rs_rw_tys" : tactic => do
  for h in ← tyHyps (← getMainGoal) do
    withMainContext do
    let some d := (← getLCtx).find? h | return
    let some (_, a, _) := (← instantiateMVars d.type).eq? | return
    let hs ← Term.exprToSyntax d.toExpr
    let stx ← if a.isAppOfArity ``Kanon.Sem.ty 2 then `(tactic| rw [$hs:term] at *)
      else `(tactic| rw [← $hs:term] at *)
    try evalTactic stx catch _ => pure ()

open Lean Meta Elab Tactic in
/-- Rewrites the goal and `e` with the values of the atoms (`S.ev ρ a = some v`). -/
elab "rs_rw_evs" : tactic => withMainContext do
  for d in (← getLCtx) do
    if d.isImplementationDetail then continue
    let some (_, l, _) := (← instantiateMVars d.type).eq? | continue
    unless l.isAppOfArity ``Kanon.Sem.ev 3 do continue
    let hs ← Term.exprToSyntax d.toExpr
    try evalTactic (← `(tactic| rw [$hs:term] at *)) catch _ => pure ()

set_option hygiene false in
/-- The value half, computing the values forward (the values of the atoms first, then those of
the nodes), so that the goal is an equation of values rather than existentials. -/
macro "rs_sem2" : tactic => `(tactic| (
  intro ρ v w w' e
  kanon_lits
  kanon_wt_simp
  (try kanon_split)
  (try subst_vars)
  kanon_wt_simp
  (try simp only [kanon_ev] at e ⊢)
  (try bv_tys)
  kanon_cases
  all_goals (try simp only [Srt.val, KanonBool.Srt.val] at *)
  all_goals (try kanon_split)
  all_goals (try subst_vars)
  all_goals (try rs_rw_evs)
  all_goals (try bv_tys)
  all_goals (try bv_widths)
  all_goals (try simp only [withW_none, asBV_none, Option.map_none, ofBV_none, Option.bind_none,
    asB_none, ofB_none, binOp_none_l, binOp_none_r, ckOp_none_l, ckOp_none_r, reduceCtorEq] at *)
  all_goals (try simp only [ofBV_some, asBV_bv, withW_bv, binOp_some, Option.map_some,
    Option.bind_some, Option.some.injEq, asB_vbool, ckOp_some, negOp_some, binB_some, ofB_some,
    KanonBool.pite, Kanon.Embed.inj_eq_iff, Bool.true_eq_false, Bool.false_eq_true, ↓reduceIte,
    withW_none, asBV_none, Option.map_none, ofBV_none, reduceCtorEq]
    at *)
  all_goals (try subst_vars)))

set_option hygiene false in
/-- `bv_sem`, with the widths of the sorts of the operands (`size_of_ty`) evaluated once their
sorts are known. -/
macro "rs_sem" : tactic => `(tactic| (
  kanon_sem_core
  all_goals (try bv_tys)
  all_goals (try bv_widths)
  all_goals (try rs_rw_tys)
  all_goals (try repeat (rw [size_of_ty_TBitVector] at *))
  all_goals (try bv_tys)
  all_goals (try bv_widths)
  all_goals (try simp only [kanon_val, Option.some.injEq, reduceCtorEq, false_and, and_false,
    ite_true, ite_false, Bool.not_true, Bool.not_false, Option.ite_none_left_eq_some,
    Option.ite_none_right_eq_some, Sigma.mk.injEq] at e ⊢)
  all_goals (try subst e)
  all_goals (try (kanon_split; subst_vars))
  all_goals (try simp only [heq_eq_eq] at *)
  all_goals (try subst_vars)
  all_goals first
    | kanon_close
    | ((repeat' split at e) <;> (repeat' split) <;> kanon_close)
    | skip))

/-- The ranges of the results of the operations on literals (the typing of the arms). -/
macro "rs_ranges" : tactic => `(tactic| (
  (try first
    | exact ResizeLib.emod_range _ _
    | exact ResizeLib.lit_shl_range _ _
    | exact ResizeLib.lit_lshr_range _ _
    | exact ResizeLib.lit_ashr_range _ _
    | exact ResizeLib.lit_udiv_range _ _
    | exact ResizeLib.masked_range _
    | exact ResizeLib.lit_sdiv_range' (by omega) _ _
    | exact ResizeLib.lit_urem_range' (by omega) (by omega) (by omega) _
    | exact ResizeLib.lit_srem_range' (by omega) (by omega) (by omega) _
    | exact ResizeLib.lit_smod_range' (by omega) (by omega) (by omega) _
    | exact ⟨Int.natCast_nonneg _, ResizeLib.rs_concat_lt (by assumption) (by assumption)⟩
    | rfl
    | exact Nat.two_pow_pos _
    | exact Int.pow_pos (by decide)
    | (simp only [ResizeLib.rs_exists_pos_eq, ResizeLib.rs_exists_pos_eq₂, and_self, and_true,
        true_and, Nat.two_pow_pos, ResizeLib.int_two_pow_pos]; (repeat' (apply And.intro)) <;> omega))))

/-- The operations on literals of the arms, at the sorts of bit-vectors of their operands, as
those of their values, and their ranges. -/
macro "rs_lits" : tactic => `(tactic| (
  (try simp only [lit_add, lit_sub, lit_mul, lit_neg, lit_udiv, lit_sdiv, lit_and, lit_or, lit_xor,
    lit_not, lit_shl, lit_lshr, lit_ashr, lit_urem, lit_srem, lit_smod, lit_extract, lit_zext,
    lit_sext, lit_concat, size_of_ty_TBitVector, or_false, forall_eq', Sigma.mk.injEq, heq_eq_eq,
    true_and, Bool.not_eq_true] at *)
  (try subst_vars)
  (try refine ⟨by omega, ?_⟩)
  (try simp (disch := first | assumption | omega) only [ResizeLib.ofInt_emod_two_pow,
    LitOps.ofInt_lit_shl', LitOps.ofInt_lit_ashr', ResizeLib.ofInt_lit_smod',
    ResizeLib.ofInt_lit_srem', ResizeLib.ofInt_lit_sdiv', Bool.false_eq_true, ↓reduceIte])
  (try simp (disch := first | assumption | omega) only [LitOps.ofInt_lit_lshr',
    LitOps.ofInt_lit_udiv', ResizeLib.ofInt_lit_urem'])
  rs_ranges))

open Lean Meta Elab Tactic in
/-- Case splits on the first proposition `p` of a `decide p` or an `if p` of
the goal. -/
elab "bv_rs_split_decide" : tactic => withMainContext do
  let t ← instantiateMVars (← getMainTarget)
  let some e := t.find? (fun e => !e.hasLooseBVars &&
      (e.isAppOfArity ``Decidable.decide 2 || e.isAppOfArity ``ite 5 ||
       e.isAppOfArity ``dite 5))
    | throwError "bv_rs_split_decide: no decide"
  let p ← Term.exprToSyntax
    (if e.isAppOfArity ``Decidable.decide 2 then e.getArg! 0 else e.getArg! 1)
  evalTactic (← `(tactic| by_cases hp : $p <;> simp only [hp, decide_true, decide_false,
    ↓reduceIte, ↓reduceDIte, Bool.not_true, Bool.not_false, Bool.true_and, Bool.false_and,
    Bool.and_true, Bool.and_false, Bool.true_or, Bool.false_or, Bool.or_true, Bool.or_false]
    at ⊢))


/-- `bv_rs_bits` after the introduction of the index. -/
macro "rs_bits_core" : tactic => `(tactic| (
  simp [BitVec.getElem_extractLsb', BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight,
    BitVec.getElem_setWidth, BitVec.getLsbD_append, BitVec.getLsbD_extractLsb',
    BitVec.getLsbD_setWidth, BitVec.getLsbD_signExtend, BitVec.getElem_signExtend,
    BitVec.getElem_append, BitVec.msb_eq_getLsbD_last, BitVec.getLsbD_sshiftRight]
  all_goals (try intros)
  all_goals (repeat' bv_rs_split_decide)
  all_goals first
    | rfl
    | (exfalso; omega)
    | (simp_all; done)
    | (congr 1; omega)
    | (have := BitVec.lt_of_getLsbD ‹_›; omega)
    | (apply BitVec.getLsbD_of_ge; omega)
    | (exact (BitVec.getLsbD_of_ge _ _ (by omega)).symm)
    | (simp_all; omega)))

/-- Proves an equality of bit-vectors bit by bit, the indices being linear. -/
macro "bv_rs_bits" : tactic => `(tactic| (
  ext i hi
  rs_bits_core))

open Lean Meta Elab Tactic in
/-- Fails if the goal has arithmetic on bit-vectors (which the bit-by-bit proofs do not handle,
and on which their `simp` may not terminate). -/
elab "rs_no_arith" : tactic => withMainContext do
  let t ← instantiateMVars (← getMainTarget)
  let bad := [``BitVec.umod, ``BitVec.smtUDiv, ``BitVec.smtSDiv, ``BitVec.srem, ``BitVec.smod,
    ``HMod.hMod, ``HMul.hMul, ``HDiv.hDiv]
  if (t.find? fun e => bad.any (e.isAppOf ·)).isSome then
    throwError "rs_no_arith: arithmetic in the goal"

set_option hygiene false in
/-- An equation of bit-vector values, bit by bit. -/
macro "rs_bv_ext" : tactic => `(tactic| (
  (try simp only [bv, Kanon.Embed.inj_eq_iff])
  rs_no_arith
  refine ResizeLib.sigma_bv_ext (by omega) (fun i => ?_)
  rs_bits_core))

open Lean Meta Elab Tactic in
/-- The width of the bit-vector value `e = Values.vbv.inj ⟨n, x⟩`. -/
def bvWidth? (e : Expr) : MetaM (Option Expr) := do
  let e ← whnfR (← instantiateMVars e)
  if e.isAppOfArity ``Sigma.mk 4 then return some (e.getArg! 2)
  let a := e.getAppArgs
  if a.isEmpty then return none
  let s ← whnfR a.back!
  if s.isAppOfArity ``Sigma.mk 4 then return some (s.getArg! 2) else return none

open Lean Meta Elab Tactic in
/-- Reduces an equation of bit-vector values `bv A x = bv B y` to `x = y`, the widths `A` and
`B` being equal by `omega` (generalized to variables first, then substituted). -/
elab "rs_bv_eq" : tactic => do
  let gen (W : Expr) : TacticM Unit := withMainContext do
    unless W.isFVar do
      let stx ← Term.exprToSyntax W
      evalTactic (← `(tactic| generalize $(mkIdent `rs_hw) : $stx = $(mkIdent `rs_w) at *))
  let widths : TacticM (Expr × Expr) := withMainContext do
    let some (_, l, r) := (← instantiateMVars (← getMainTarget)).cleanupAnnotations.eq?
      | throwError "rs_bv_eq: not an equation"
    let some A ← bvWidth? l | throwError "rs_bv_eq: no width"
    let some B ← bvWidth? r | throwError "rs_bv_eq: no width"
    return (A, B)
  let (A, B) ← widths
  let s ← saveState
  try
    unless A == B do
      gen A
      let (_, B) ← widths
      gen B
      let (A, B) ← widths
      withMainContext do
        let sa ← Term.exprToSyntax A
        let sb ← Term.exprToSyntax B
        evalTactic (← `(tactic| have $(mkIdent `rs_e) : $sa = $sb := by omega))
        evalTactic (← `(tactic| subst $(mkIdent `rs_e)))
    evalTactic (← `(tactic| simp only [bv, Kanon.Embed.inj_eq_iff, Sigma.mk.injEq, heq_eq_eq,
      true_and]))
  catch _ =>
    s.restore
    evalTactic (← `(tactic| rs_bv_ext))
  return
  unless A == B do
    gen A
    let (_, B) ← widths
    gen B
    let (A, B) ← widths
    withMainContext do
      let sa ← Term.exprToSyntax A
      let sb ← Term.exprToSyntax B
      evalTactic (← `(tactic| have $(mkIdent `rs_e) : $sa = $sb := by omega))
      evalTactic (← `(tactic| subst $(mkIdent `rs_e)))
  evalTactic (← `(tactic| simp only [bv, Kanon.Embed.inj_eq_iff, Sigma.mk.injEq, heq_eq_eq,
    true_and]))

open Lean Meta Elab Tactic in
/-- The values of the hypotheses unfolded, and the equations of values split. -/
elab "rs_simp_hyps" : tactic => withMainContext do
  let stx ← `(tactic| simp only [kanon_val, ofBV_some, binOp_some, Option.map_some,
    Option.some.injEq, asBV_bv, withW_bv, Option.bind_some, Option.map_none, Option.bind_none,
    reduceCtorEq, Kanon.Embed.inj_eq_iff, Sigma.mk.injEq, bv, ofBV_none, asBV_none, withW_none,
    Option.map_none, binOp_none_l, binOp_none_r, ckOp_none_l, ckOp_none_r])
  let { ctx, simprocs, dischargeWrapper, .. } ← mkSimpContext stx (eraseLocal := false)
  let hs ← (← getMainGoal).getNondepPropHyps
  dischargeWrapper.with fun dis? => do
    let (r, _) ← simpGoal (← getMainGoal) ctx simprocs dis? false hs
    replaceMainGoal (match r with | none => [] | some (_, g) => [g])

open Lean Meta Elab Tactic in
/-- Fails unless the goal is an equation of bit-vectors. -/
elab "rs_if_bv_eq" : tactic => withMainContext do
  let some (ty, _, _) := (← instantiateMVars (← getMainTarget)).cleanupAnnotations.eq?
    | throwError "rs_if_bv_eq: not an equation"
  unless (← whnfR ty).isAppOfArity ``BitVec 1 do throwError "rs_if_bv_eq: not of bit-vectors"

/-- The values of the hypotheses and the goal, unfolded and identified. -/
macro "rs_norm" : tactic => `(tactic| (
  (try rs_simp_hyps)
  (try simp only [kanon_val, ofBV_some, binOp_some, Option.map_some, Option.some.injEq,
    asBV_bv, withW_bv, Option.bind_some, Option.map_none, Option.bind_none, reduceCtorEq])
  (try kanon_split)
  (try subst_vars)
  (try simp only [heq_eq_eq, true_and, and_true, exists_eq_left', exists_eq_left,
    exists_eq_right, exists_eq_right'] at *)
  (try kanon_split)
  (try subst_vars)))

/-- `rs_res`, after the case splits. -/
macro "rs_res_core" : tactic => `(tactic| (
  (try subst_vars)
  rs_norm
  rs_norm
  (try subst_vars)
  (try rs_nat)
  (try bv_widths)
  rs_norm
  (try rs_gen_toNat)
  (try bv_rw_tys)
  (try rs_rw_tys)
  (try repeat (rw [size_of_ty_TBitVector] at *))
  (try rs_bv_eq)
  (try simp (disch := first | assumption | omega) only [ResizeLib.rs_ofInt_emod,
    ResizeLib.rs_ofInt_emod_nat, ResizeLib.rs_ofInt_lit_sext, ResizeLib.rs_ofInt_lit_zext,
    ResizeLib.rs_lit_concat_nat, ResizeLib.rs_ofInt_append, Prim.lit_extract, ResizeLib.rs_zasr_nat,
    ResizeLib.zasr_zero, LitOps.ofInt_masked, ResizeLib.rs_toNat_ofInt_nat,
    ResizeLib.rs_extractLsb'_ofInt, BitVec.shiftLeft_eq', BitVec.ushiftRight_eq',
    ResizeLib.rs_ofInt_zero, ↓reduceIte, Bool.false_eq_true, Bool.false_and, Bool.or_false,
    Bool.and_false, BitVec.extractLsb'_add, BitVec.extractLsb'_mul, Nat.sub_zero,
    Option.some.injEq] at *)
  (try simp only [ofBV_some, Option.some.injEq] at *)
  (try subst_vars)
  (try rs_bv_eq)
  (try rfl)
  (try (rs_if_bv_eq; rs_no_arith; (repeat' bv_rs_split_decide); all_goals bv_rs_bits; done))
  (try rs_ranges)))

/-- The resizings: the values unfolded, the widths made natural numbers (`rs_nat`,
`rs_gen_toNat`), equations of bit-vector values reduced to their bits (`rs_bv_eq`), and the
operations on literals as those on their values. -/
macro "rs_res" : tactic => `(tactic| (
  (try kanon_split)
  (try subst_vars)
  (try rs_rw_tys)
  (try repeat (rw [size_of_ty_TBitVector] at *))
  rs_norm
  (try kanon_or_cases)
  all_goals (try kanon_split_hyps)
  all_goals rs_res_core))

open Lean Meta Elab Tactic in
/-- `kanon_lift_body`, whatever the tags of the goals (it looks for the goal `hl`). -/
elab "rs_lift_body" : tactic => do
  let g ← getMainGoal
  let s ← saveState
  let lift : TacticM (List MVarId × List MVarId) := do
    evalTactic (← `(tactic| apply Kanon.Sem.Refines.of_lift))
    let gs ← getGoals
    let hl :: rest := gs | throwError "rs_lift_body: no goal"
    setGoals [hl]
    let side ← Kanon.Proof.liftGoal
    let rest ← rest.filterM fun g => return !(← g.isAssigned)
    return (rest, side)
  setGoals [g]
  let (rest, side) ← lift
  if side.isEmpty then setGoals rest
  else
    s.restore
    evalTactic (← `(tactic| refine Kanon.Sem.Refines.of_WT (fun $(mkIdent `kw) => ?_)))
    let (rest, side) ← lift
    setGoals (rest ++ side)

/-- The shift amounts as natural numbers, and the equations of shifts bit by bit. -/
macro "rs_shift" : tactic => `(tactic| (
  (try simp only [decide_eq_true_eq, decide_eq_false_iff_not] at *)
  (try simp (disch := omega) only [ResizeLib.toNat_ofInt_lt, ResizeLib.toNat_ofInt_le,
    BitVec.sshiftRight', Int.toNat_natCast, ResizeLib.ofInt_ones, Prim.lit_sub, Prim.masked,
    ResizeLib.ofInt_emod_two_pow, Int.toNat_natCast, ← Int.natCast_add, Int.toNat_sub',
    ← Int.natCast_sub])
  (try simp only [BitVec.shiftLeft_eq', BitVec.ushiftRight_eq'])
  ext i hi
  simp [BitVec.getElem_sshiftRight, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight,
    BitVec.getElem_shiftLeft, BitVec.getElem_ushiftRight, BitVec.msb_eq_getLsbD_last,
    BitVec.getLsbD_sshiftRight]
  all_goals (try intros)
  all_goals (repeat' bv_rs_split_decide)
  all_goals first
    | rfl
    | (exfalso; omega)
    | (simp_all; done)
    | (congr 1; omega)
    | (rw [Bool.or_comm]; done)
    | (rw [Bool.and_comm]; done)
    | (apply BitVec.getLsbD_of_ge; omega)
    | (simp_all; omega)
    | skip))

/-- `rs_sem2` and the closing steps. -/
macro "rs_sem_fwd" : tactic => `(tactic| (
  rs_sem2
  all_goals rs_lits
  all_goals rs_res
  all_goals (try omega)
  all_goals (try (rs_if_bv_eq; rs_no_arith; rs_shift; done))))

set_option hygiene false in
/-- The sorts that the well-typedness `kw` of the spec gives. -/
macro "rs_kw_tys" : tactic => `(tactic| (
  simp only [WT_mk, Node.wt, Node.All, ty_mk, bv_wf] at kw
  kanon_split
  subst_vars
  simp only [ty_mk, size_of_ty_TBitVector, Bitvec.size] at *))

open Lean Meta Elab Tactic in
/-- The literals that a guard says are powers of two (`popcount r = 1`), as `2 ^ k`. -/
elab "rs_pow2" : tactic => withMainContext do
  for d in (← getLCtx) do
    if d.isImplementationDetail then continue
    let some (_, l, _) := (← instantiateMVars d.type).eq? | continue
    unless (l.isAppOfArity ``Prim.popcount 1 || l.isAppOfArity ``BitvecMod.popcount 1) &&
      (l.getArg! 0).isFVar do continue
    let h ← Term.exprToSyntax d.toExpr
    evalTactic (← `(tactic| obtain ⟨$(mkIdent `rs_k), $(mkIdent `rs_hk)⟩ :=
      ResizeLib.pow2_of_popcount $h))
    evalTactic (← `(tactic| subst $(mkIdent `rs_hk)))
    evalTactic (← `(tactic| try simp only [log2, ResizeLib.log2_two_pow] at *))
    evalTactic (← `(tactic| try have $(mkIdent `rs_k1) : 1 ≤ $(mkIdent `rs_k) :=
      ResizeLib.one_le_of_two_pow_gt (by assumption)))
    return
  throwError "rs_pow2: no power of two"

/-- The guards and sorts of the arms of `div`, made usable by `omega`. -/
macro "rs_div_pre" : tactic => `(tactic| (
  all_goals (try simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not, Prim.z_lsl, Int.not_lt,
    Int.not_le, gt_iff_lt, Int.one_mul, Int.toNat_natCast] at *)
  all_goals (try rs_kw_tys)
  all_goals (try bv_tys)
  all_goals (try simp only [or_false, forall_eq', forall_eq, Kanon.Embed.inj_eq_iff,
    Srt.TBitVector.injEq, reduceCtorEq] at *)))

/-- `bv_auto` with the value half `sem`, leaving the typing goals that `kanon_wt` does not close
(after the value goals). -/
macro "rs_auto_with " sem:tactic : tactic => `(tactic| (
  (try intro _)
  intros
  kanon_rule_lift
  all_goals (try rs_pow2)
  all_goals (try (
    (try simp only [] ) <;> (repeat' bv_rs_split_decide) <;> (try rs_lift_body) <;> (try simp only [kanon_spec, kanon_body]) <;>
      (try first | kanon_refl | (kanon_comm; done) | kanon_close_lemmas)))
  all_goals kanon_on_refines (
    refine Kanon.Sem.Refines.intro ?_ ?_
    focus (kanon_wt; all_goals rs_ranges)
    rotate_left
    focus ($sem:tactic))
  all_goals (try (first | exact Int.pow_pos (by decide) | omega))
  all_goals rs_lits
  all_goals rs_res
  all_goals (try (rs_if_bv_eq; rs_no_arith; rs_shift; done))
  all_goals (try omega)))

/-- `bv_auto`, with the forward value half if it closes the goal, `rs_sem` otherwise. -/
macro "rs_auto" : tactic => `(tactic| rs_auto_with (first | (rs_sem_fwd; done) | rs_sem))

/-- `rs_auto` with the forward value half only (to inspect what it leaves). -/
macro "rs_auto_fwd" : tactic => `(tactic| rs_auto_with rs_sem_fwd)

/-- `rs_auto` with `rs_sem` only, for the hand-written arms that close what it leaves (the
forward value half would fail on them, after doing most of the work). -/
macro "rs_auto_sem" : tactic => `(tactic| rs_auto_with rs_sem)

end BitvecMod
