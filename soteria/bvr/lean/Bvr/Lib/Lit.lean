import Bvr.Lib.Den

/-!
# Bit-vector values (`bv`) in terms

`l.at n` is the value `l` at width `n`. The literals built from values
(`lit l`) are well-typed and have the value `l.at n`, and the operations on
values compute on `at`, when the result is taken at a width that the
operands do not exceed (as when the widths are those of well-typed terms).
-/

namespace Bvr.Lib

open Classical

/-- The value at width `n`. -/
def _root_.Bvr.BvVal.at (n : Nat) (l : BvVal) : BitVec n := l.x.setWidth n

@[simp] theorem lit_w_add (a b : BvVal) : (lit_add a b).w = a.w := rfl
@[simp] theorem lit_w_sub (a b : BvVal) : (lit_sub a b).w = a.w := rfl
@[simp] theorem lit_w_mul (a b : BvVal) : (lit_mul a b).w = a.w := rfl
@[simp] theorem lit_w_neg (a : BvVal) : (lit_neg a).w = a.w := rfl
@[simp] theorem lit_w_udiv (a b : BvVal) : (lit_udiv a b).w = a.w := rfl
@[simp] theorem lit_w_sdiv (a b : BvVal) : (lit_sdiv a b).w = a.w := rfl
@[simp] theorem lit_w_and (a b : BvVal) : (lit_and a b).w = a.w := rfl
@[simp] theorem lit_w_or (a b : BvVal) : (lit_or a b).w = a.w := rfl
@[simp] theorem lit_w_xor (a b : BvVal) : (lit_xor a b).w = a.w := rfl
@[simp] theorem lit_w_shl (a b : BvVal) : (lit_shl a b).w = a.w := rfl
@[simp] theorem lit_w_lshr (a b : BvVal) : (lit_lshr a b).w = a.w := rfl
@[simp] theorem lit_w_ashr (a b : BvVal) : (lit_ashr a b).w = a.w := rfl
@[simp] theorem lit_w_urem (a b : BvVal) : (lit_urem a b).w = a.w := rfl
@[simp] theorem lit_w_srem (a b : BvVal) : (lit_srem a b).w = a.w := rfl
@[simp] theorem lit_w_smod (a b : BvVal) : (lit_smod a b).w = a.w := rfl
@[simp] theorem lit_w_not (a : BvVal) : (lit_not a).w = a.w := rfl
@[simp] theorem lit_w_extract (i j : Int) (a : BvVal) : (lit_extract i j a).w = (j - i + 1).toNat := rfl
@[simp] theorem lit_w_zext (k : Int) (a : BvVal) : (lit_zext k a).w = a.w + k.toNat := rfl
@[simp] theorem lit_w_sext (k : Int) (a : BvVal) : (lit_sext k a).w = a.w + k.toNat := rfl
@[simp] theorem lit_w_concat (a b : BvVal) : (lit_concat a b).w = a.w + b.w := rfl
@[simp] theorem bv_of_lit_w (z : Int) (t : Ty) :
    (bv_of_lit (.mk (.bitVec z) t)).w = (size_of_ty t).toNat := rfl
@[simp] theorem of_z_w (n z : Int) : (of_z n z).w = n.toNat := rfl

@[simp] theorem WT_lit (l : BvVal) : (lit l).WT ↔ 0 < l.w := by
  simp only [lit, WT_bitVec]
  constructor
  · rintro ⟨k, hk, h, -⟩
    rcases h with h | h <;> simp at h <;> omega
  · intro h
    exact ⟨l.w, h, .inl rfl, by omega, by exact_mod_cast l.x.isLt⟩

@[simp] theorem ty_lit (l : BvVal) : (lit l).ty = .bitVector l.w := rfl

@[simp] theorem den_lit {FS ρ n} (l : BvVal) : den FS ρ n (lit l) = some (l.at n) := by
  simp [lit, den, BvVal.at]

theorem setWidth_setWidth_of_le {w v n : Nat} (x : BitVec w) (h : n ≤ v) :
    (x.setWidth v).setWidth n = x.setWidth n := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth]
  rw [Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 h)]

theorem setWidth_add_of_le {w n : Nat} (x y : BitVec w) (h : n ≤ w) :
    (x + y).setWidth n = x.setWidth n + y.setWidth n := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_add]
  rw [Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 h), Nat.add_mod]

theorem setWidth_mul_of_le {w n : Nat} (x y : BitVec w) (h : n ≤ w) :
    (x * y).setWidth n = x.setWidth n * y.setWidth n := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_mul]
  rw [Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 h), Nat.mul_mod]

theorem setWidth_neg_of_le {w n : Nat} (x : BitVec w) (h : n ≤ w) :
    (-x).setWidth n = -(x.setWidth n) := by
  have := setWidth_add_of_le x (-x) h
  have h0 : x + -x = 0 := by grind
  rw [h0] at this
  have h1 : BitVec.setWidth n (0 : BitVec w) = 0 := by
    apply BitVec.eq_of_toNat_eq; simp
  rw [h1] at this
  grind

theorem setWidth_sub_of_le {w n : Nat} (x y : BitVec w) (h : n ≤ w) :
    (x - y).setWidth n = x.setWidth n - y.setWidth n := by
  rw [BitVec.sub_eq_add_neg, setWidth_add_of_le _ _ h, setWidth_neg_of_le _ h,
    BitVec.sub_eq_add_neg]

@[simp] theorem at_add {n} {a b : BvVal} (h : n ≤ a.w) :
    (lit_add a b).at n = a.at n + b.at n := by
  simp [BvVal.at, lit_add, setWidth_add_of_le _ _ h, setWidth_setWidth_of_le _ h]

@[simp] theorem at_sub {n} {a b : BvVal} (h : n ≤ a.w) :
    (lit_sub a b).at n = a.at n - b.at n := by
  simp [BvVal.at, lit_sub, setWidth_sub_of_le _ _ h, setWidth_setWidth_of_le _ h]

@[simp] theorem at_mul {n} {a b : BvVal} (h : n ≤ a.w) :
    (lit_mul a b).at n = a.at n * b.at n := by
  simp [BvVal.at, lit_mul, setWidth_mul_of_le _ _ h, setWidth_setWidth_of_le _ h]

@[simp] theorem at_neg {n} {a : BvVal} (h : n ≤ a.w) : (lit_neg a).at n = -(a.at n) := by
  simp [BvVal.at, lit_neg, setWidth_neg_of_le _ h]

@[simp] theorem at_udiv {n} {a b : BvVal} (h : a.w = n) :
    (lit_udiv a b).at n = (a.at n).smtUDiv (b.at n) := by
  obtain ⟨w, x⟩ := a; simp only at h; subst h
  simp [BvVal.at, lit_udiv]

@[simp] theorem at_sdiv {n} {a b : BvVal} (h : a.w = n) :
    (lit_sdiv a b).at n = (a.at n).smtSDiv (b.at n) := by
  obtain ⟨w, x⟩ := a; simp only at h; subst h
  simp [BvVal.at, lit_sdiv]

theorem setWidth_ofInt_of_le {n w : Nat} (z : Int) (h : n ≤ w) : (BitVec.ofInt w z).setWidth n = BitVec.ofInt n z := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofInt]
  have hd : ((2 ^ n : Nat) : Int) ∣ ((2 ^ w : Nat) : Int) := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
    exact ⟨((2 ^ k : Nat) : Int), by push_cast; rw [Int.pow_add]⟩
  have hw : (0 : Int) < ((2 ^ w : Nat) : Int) := by exact_mod_cast Nat.two_pow_pos w
  have hn : (0 : Int) < ((2 ^ n : Nat) : Int) := by exact_mod_cast Nat.two_pow_pos n
  have h1 : (0 : Int) ≤ z % ((2 ^ w : Nat) : Int) := Int.emod_nonneg _ (by omega)
  have e : (z % ((2 ^ w : Nat) : Int)) % ((2 ^ n : Nat) : Int) = z % ((2 ^ n : Nat) : Int) :=
    Int.emod_emod_of_dvd z hd
  rw [← e, Int.toNat_emod h1 (by omega), Int.toNat_natCast]

@[simp] theorem at_bv_of_lit {n z t} (h : n ≤ (size_of_ty t).toNat) :
    (bv_of_lit (.mk (.bitVec z) t)).at n = BitVec.ofInt n z :=
  setWidth_ofInt_of_le z h

@[simp] theorem at_of_z {n m z} (h : n ≤ m.toNat) : (of_z m z).at n = BitVec.ofInt n z :=
  setWidth_ofInt_of_le z h

/-! ## Values of known widths

Once the widths are those of well-typed terms, the values are normalized to
`⟨n, x⟩`, on which the operations compute without side conditions. -/

@[simp] theorem bv_of_lit_bv (n : Nat) (z : Int) :
    bv_of_lit (.mk (.bitVec z) (.bitVector (n : Int))) = ⟨n, BitVec.ofInt n z⟩ := rfl

/-- `bv_of_lit_bv`, at any width (e.g. a numeral). -/
@[simp] theorem bv_of_lit_bv' (m z : Int) :
    bv_of_lit (.mk (.bitVec z) (.bitVector m)) = ⟨m.toNat, BitVec.ofInt m.toNat z⟩ := rfl

@[simp] theorem of_z_nat (n : Nat) (z : Int) : of_z (n : Int) z = ⟨n, BitVec.ofInt n z⟩ := rfl

@[simp] theorem lit_add_mk {n} (x y : BitVec n) : lit_add ⟨n, x⟩ ⟨n, y⟩ = ⟨n, x + y⟩ := by
  simp [lit_add]
@[simp] theorem lit_sub_mk {n} (x y : BitVec n) : lit_sub ⟨n, x⟩ ⟨n, y⟩ = ⟨n, x - y⟩ := by
  simp [lit_sub]
@[simp] theorem lit_mul_mk {n} (x y : BitVec n) : lit_mul ⟨n, x⟩ ⟨n, y⟩ = ⟨n, x * y⟩ := by
  simp [lit_mul]
@[simp] theorem lit_neg_mk {n} (x : BitVec n) : lit_neg ⟨n, x⟩ = ⟨n, -x⟩ := rfl
@[simp] theorem lit_udiv_mk {n} (x y : BitVec n) :
    lit_udiv ⟨n, x⟩ ⟨n, y⟩ = ⟨n, x.smtUDiv y⟩ := by simp [lit_udiv]
@[simp] theorem lit_sdiv_mk {n} (x y : BitVec n) :
    lit_sdiv ⟨n, x⟩ ⟨n, y⟩ = ⟨n, x.smtSDiv y⟩ := by simp [lit_sdiv]
@[simp] theorem lit_and_mk {n} (x y : BitVec n) : lit_and ⟨n, x⟩ ⟨n, y⟩ = ⟨n, x &&& y⟩ := by
  simp [lit_and]
@[simp] theorem lit_or_mk {n} (x y : BitVec n) : lit_or ⟨n, x⟩ ⟨n, y⟩ = ⟨n, x ||| y⟩ := by
  simp [lit_or]
@[simp] theorem lit_xor_mk {n} (x y : BitVec n) : lit_xor ⟨n, x⟩ ⟨n, y⟩ = ⟨n, x ^^^ y⟩ := by
  simp [lit_xor]
@[simp] theorem lit_not_mk {n} (x : BitVec n) : lit_not ⟨n, x⟩ = ⟨n, ~~~x⟩ := rfl
@[simp] theorem lit_shl_mk {n} (x y : BitVec n) : lit_shl ⟨n, x⟩ ⟨n, y⟩ = ⟨n, x <<< y⟩ := by
  simp [lit_shl]
@[simp] theorem lit_lshr_mk {n} (x y : BitVec n) : lit_lshr ⟨n, x⟩ ⟨n, y⟩ = ⟨n, x >>> y⟩ := by
  simp [lit_lshr]
@[simp] theorem lit_ashr_mk {n} (x y : BitVec n) :
    lit_ashr ⟨n, x⟩ ⟨n, y⟩ = ⟨n, x.sshiftRight' y⟩ := by simp [lit_ashr]
@[simp] theorem lit_urem_mk {n} (x y : BitVec n) : lit_urem ⟨n, x⟩ ⟨n, y⟩ = ⟨n, x.umod y⟩ := by
  simp [lit_urem]
@[simp] theorem lit_srem_mk {n} (x y : BitVec n) : lit_srem ⟨n, x⟩ ⟨n, y⟩ = ⟨n, x.srem y⟩ := by
  simp [lit_srem]
@[simp] theorem lit_smod_mk {n} (x y : BitVec n) : lit_smod ⟨n, x⟩ ⟨n, y⟩ = ⟨n, x.smod y⟩ := by
  simp [lit_smod]
@[simp] theorem lit_extract_mk {n} (i j : Int) (x : BitVec n) :
    lit_extract i j ⟨n, x⟩ = ⟨(j - i + 1).toNat, x.extractLsb' i.toNat _⟩ := rfl
@[simp] theorem lit_zext_mk {n} (k : Int) (x : BitVec n) :
    lit_zext k ⟨n, x⟩ = ⟨n + k.toNat, x.setWidth _⟩ := rfl
@[simp] theorem lit_sext_mk {n} (k : Int) (x : BitVec n) :
    lit_sext k ⟨n, x⟩ = ⟨n + k.toNat, x.signExtend _⟩ := rfl
@[simp] theorem lit_concat_mk {n m} (x : BitVec n) (y : BitVec m) :
    lit_concat ⟨n, x⟩ ⟨m, y⟩ = ⟨n + m, x ++ y⟩ := rfl
/-- A value at another width than its own. -/
theorem at_mk' {n m} (x : BitVec n) : BvVal.at m ⟨n, x⟩ = x.setWidth m := rfl
@[simp] theorem bv_equal_mk {n} (x y : BitVec n) : (⟨n, x⟩ : BvVal) = ⟨n, y⟩ ↔ x = y := by
  constructor
  · intro h; cases h; rfl
  · intro h; rw [h]

@[simp] theorem at_of_z_self (m z : Int) : (of_z m z).at m.toNat = BitVec.ofInt m.toNat z := by
  simp [BvVal.at, of_z]
@[simp] theorem at_mk {n} (x : BitVec n) : BvVal.at n ⟨n, x⟩ = x := by simp [BvVal.at]
@[simp] theorem width_mk {n} (x : BitVec n) : width ⟨n, x⟩ = n := rfl
@[simp] theorem to_z_mk {n} (s : Bool) (x : BitVec n) :
    to_z s ⟨n, x⟩ = if s then x.toInt else (x.toNat : Int) := rfl

/-! ## Constants in range -/

theorem toNat_ofInt_of_lt {n : Nat} {k : Int} (h0 : 0 ≤ k) (h1 : k < 2 ^ n) :
    (BitVec.ofInt n k).toNat = k.toNat := by
  rw [BitVec.toNat_ofInt, Int.emod_eq_of_lt h0 (by push_cast; exact h1)]
theorem emod_two_pow_of_lt {n : Nat} {k : Int} (h0 : 0 ≤ k) (h1 : k < 2 ^ n) :
    k % 2 ^ n = k := Int.emod_eq_of_lt h0 h1

theorem smtUDiv_toNat {n : Nat} {a b : BitVec n} (hb : b.toNat ≠ 0) :
    (a.smtUDiv b).toNat = a.toNat / b.toNat := by
  rw [BitVec.smtUDiv_eq, ite_eq_right_iff.mpr (fun h => absurd h (by intro h; apply hb; simp [h])),
    BitVec.toNat_udiv]

theorem msb_of_lit (z : Int) (T : Ty) :
    msb_of (.mk (.bitVec z) T) = if 0 < z then log2 z else size_of_ty T - 1 := by
  rw [msb_of]
  by_cases h : 0 < z
  · simp [firstSome, h, HOrElse.hOrElse, OrElse.orElse, Option.orElse]
  · by_cases h' : z = 0
    · subst h'; simp [firstSome, HOrElse.hOrElse, OrElse.orElse, Option.orElse]
    · simp [firstSome, h, h', HOrElse.hOrElse, OrElse.orElse, Option.orElse]

/-! ## Integer helpers -/

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

theorem is_pow2_eq {z : Int} (h : is_pow2 z = true) : z = 2 ^ (log2 z).toNat ∧ 0 ≤ log2 z := by
  unfold is_pow2 at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨h0, h1⟩ := h
  simp only [popcount] at h1
  have h1' : popcountNat z.toNat = 1 := by exact_mod_cast h1
  obtain ⟨j, hj⟩ := popcountNat_eq_one h1'
  have e1 : ((2 ^ j : Nat) : Int) = (2 : Int) ^ j := by push_cast; rfl
  simp only [log2, hj, Nat.log2_two_pow, Int.toNat_natCast]
  omega

theorem is_pow2_exists {z : Int} (h : is_pow2 z = true) : ∃ k : Nat, z = 2 ^ k :=
  ⟨_, (is_pow2_eq h).1⟩

theorem lt_two_pow_log2 {z w : Int} (hz : 0 < z) (h : log2 z < w) : z < 2 ^ w.toNat := by
  have hl := Nat.lt_log2_self (n := z.toNat)
  have hle : 2 ^ (Nat.log2 z.toNat + 1) ≤ 2 ^ w.toNat :=
    Nat.pow_le_pow_right (by omega) (by simp only [log2] at h; omega)
  have : ((z.toNat : Nat) : Int) < ((2 ^ w.toNat : Nat) : Int) := by exact_mod_cast (by omega)
  push_cast at this; omega

theorem is_bv_iff {t : Ty} : is_bv t = true ↔ ∃ n, t = .bitVector n := by
  cases t <;> simp [is_bv, firstSome]

theorem WT_mk_masked {n z : Int} : (mk_masked n z).WT ↔ 0 < n := by
  refine ⟨fun w => ?_, mk_masked_WT⟩
  obtain ⟨k, hk, h, -⟩ := WT_bitVec.1 w
  rcases h with h | h <;> simp at h; omega

/-! ## Boolean literals -/

@[simp] theorem of_bool_WT (b : Bool) : (of_bool b).WT := by cases b <;> simp [of_bool]
@[simp] theorem of_bool_ty (b : Bool) : (of_bool b).ty = .bool := by cases b <;> rfl
@[simp] theorem denB_of_bool {FS ρ} (b : Bool) : denB FS ρ (of_bool b) = some b := by
  cases b <;> rfl
@[simp] theorem eval_of_bool {FS ρ} (b : Bool) : eval FS ρ (of_bool b) = some (.bool b) := by
  cases b <;> simp [of_bool]

end Bvr.Lib
