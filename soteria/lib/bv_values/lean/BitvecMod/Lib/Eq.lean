import BitvecMod.Lib.Tactic

/-!
# Equality, the boolean rules, the overflow checks and the divisions

The lemmas and tactics of the arms of `Bool.eq`, `and_`, `or_`, `not_` of the module,
`Bitvec.add_overflows`, `sub_overflows`, `mul_overflows`, `div`, `rem`, `mod_`, over the
interface: the counterparts of the language's `Kanon/Lib/{Eq,Ovf,Bool}.lean` (and of the parts
of `Lit`, `LitOps` and `Arith` that they use).

- the helpers of the rules on literals in range (`to_z`, `overflows_*`, `lit_*_overflows`,
  `lit_udiv`, ...) as the operations of `BitVec` (`to_z_ofInt`, `ofInt_lit_udiv`, ...);
- facts on overflows and divisions, through integers (`sadd_pos`, `mul_div_ok`, ...);
- `bveq_rule` proves an arm of these functions: `bveq_rule_lift` (Kanon's `kanon_rule_lift`,
  with `bveq_lift_body` and the side conditions `L.Nonzero v` by `bveq_nonzero`), the
  reduction to the structural values of the terms (`bv_apply_den`), then the typing half
  (`bveq_wt`) and the value half (`bveq_sem`: `bveq_sem_core` reduces it to the values of the
  atoms, with natural widths and opaque values for the literals, which the closing lemmas
  are stated on). It is the tactic of the bitvec functions above; the arms that the module
  adds to the functions of the bool module are proved with it in `Proofs/Bool/`.
-/

namespace BitvecMod.Lib.BvEq

open Classical Kanon Prim

set_option linter.unusedSectionVars false

/-- The integer that a bit-vector stands for, in a signedness. -/
abbrev iv (s : Bool) {w : Nat} (x : BitVec w) : Int := if s then x.toInt else x.toNat

@[simp] theorem zasr_zero (z : Int) : zasr z 0 = z := by simp [zasr]

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

theorem lit_add_overflows_ofInt (s : Bool) {s2 : S.Ty} {l r : Int} (hl0 : 0 ≤ l)
    (hl1 : l < 2 ^ n) (hr0 : 0 ≤ r) (hr1 : r < 2 ^ n) :
    L.bitvec_lit_add_overflows s (L.TBitVector (n : Int)) s2 l r =
      if s then (BitVec.ofInt n l).saddOverflow (BitVec.ofInt n r)
      else (BitVec.ofInt n l).uaddOverflow (BitVec.ofInt n r) := by
  rw [L.bitvec_lit_add_overflows_eq, Sem.size_of_ty_TBitVector, ← L.bitvec_overflows_add_eq]
  exact overflows_add_ofInt hn s hl0 hl1 hr0 hr1

theorem lit_sub_overflows_ofInt (s : Bool) {s2 : S.Ty} {l r : Int} (hl0 : 0 ≤ l)
    (hl1 : l < 2 ^ n) (hr0 : 0 ≤ r) (hr1 : r < 2 ^ n) :
    L.bitvec_lit_sub_overflows s (L.TBitVector (n : Int)) s2 l r =
      if s then (BitVec.ofInt n l).ssubOverflow (BitVec.ofInt n r)
      else (BitVec.ofInt n l).usubOverflow (BitVec.ofInt n r) := by
  rw [L.bitvec_lit_sub_overflows_eq, Sem.size_of_ty_TBitVector, ← L.bitvec_overflows_sub_eq]
  exact overflows_sub_ofInt hn s hl0 hl1 hr0 hr1

theorem lit_mul_overflows_ofInt (s : Bool) {s2 : S.Ty} {l r : Int} (hl0 : 0 ≤ l)
    (hl1 : l < 2 ^ n) (hr0 : 0 ≤ r) (hr1 : r < 2 ^ n) :
    L.bitvec_lit_mul_overflows s (L.TBitVector (n : Int)) s2 l r =
      if s then (BitVec.ofInt n l).smulOverflow (BitVec.ofInt n r)
      else (BitVec.ofInt n l).umulOverflow (BitVec.ofInt n r) := by
  rw [L.bitvec_lit_mul_overflows_eq, Sem.size_of_ty_TBitVector, ← L.bitvec_overflows_mul_eq]
  exact overflows_mul_ofInt hn s hl0 hl1 hr0 hr1

end


/-! ## Literals in range -/

@[simp] theorem ofInt_emod_two_pow (n : Nat) (z : Int) :
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

@[simp] theorem log2_two_pow (k : Nat) : log2 ((2 : Int) ^ k) = k := by
  rw [show (2 : Int) ^ k = ((2 ^ k : Nat) : Int) by push_cast; rfl, log2, Int.toNat_natCast,
    Nat.log2_two_pow]

theorem lt_two_pow_log2 {z w : Int} (hz : 0 < z) (h : log2 z < w) : z < 2 ^ w.toNat := by
  have hl := Nat.lt_log2_self (n := z.toNat)
  have hle : 2 ^ (Nat.log2 z.toNat + 1) ≤ 2 ^ w.toNat :=
    Nat.pow_le_pow_right (by omega) (by simp only [log2] at h; omega)
  have : ((z.toNat : Nat) : Int) < ((2 ^ w.toNat : Nat) : Int) := by exact_mod_cast (by omega)
  push_cast at this; omega

theorem is_pow2_exists {z : Int} (h : L.bitvec_is_pow2 z = true) : ∃ k : Nat, z = 2 ^ k := by
  rw [L.bitvec_is_pow2_eq, Sem.popcount_eq] at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, popcount] at h
  obtain ⟨h0, h1⟩ := h
  have h1' : popcountNat z.toNat = 1 := by exact_mod_cast of_decide_eq_true h1
  obtain ⟨j, hj⟩ := popcountNat_eq_one h1'
  have : ((2 ^ j : Nat) : Int) = (2 : Int) ^ j := by push_cast; rfl
  exact ⟨j, by omega⟩

theorem ovf_comm {n : Nat} (x y : BitVec n) : (x.saddOverflow y = y.saddOverflow x) ∧
    (x.uaddOverflow y = y.uaddOverflow x) ∧ (x.smulOverflow y = y.smulOverflow x) ∧
    (x.umulOverflow y = y.umulOverflow x) := by
  simp [BitVec.saddOverflow, BitVec.uaddOverflow, BitVec.smulOverflow,
    BitVec.umulOverflow, Int.add_comm, Nat.add_comm, Int.mul_comm, Nat.mul_comm]


/-! ## Division and remainders of literals -/

section
variable {n : Nat}

theorem masked_eq_toNat (z : Int) : masked (n : Int) z = ((BitVec.ofInt n z).toNat : Int) := by
  have e : ((2 ^ n : Nat) : Int) = (2 : Int) ^ n := by push_cast; rfl
  have h2 : (0 : Int) < 2 ^ n := Int.pow_pos (by decide)
  rw [BitVec.toNat_ofInt, e, masked, Int.toNat_natCast]
  exact (Int.toNat_of_nonneg (Int.emod_nonneg _ (by omega))).symm

theorem ofInt_masked' (z : Int) : BitVec.ofInt n (masked (n : Int) z) = BitVec.ofInt n z := by
  simp only [masked, Int.toNat_natCast, ofInt_emod_two_pow]

theorem ofInt_masked_toNat (z : Int) :
    BitVec.ofInt n ((BitVec.ofInt n z).toNat : Int) = BitVec.ofInt n z := by
  rw [BitVec.ofInt_natCast, BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem sext_of_eq (hn : 0 < n) (z : Int) : sext_of (n : Int) z = (BitVec.ofInt n z).toInt :=
  signed_extract_zero hn z

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

theorem ofInt_lit_udiv {a : Int} (ha0 : 0 ≤ a) (ha1 : a < 2 ^ n) (b : Int) :
    BitVec.ofInt n (lit_udiv (n : Int) a b) = (BitVec.ofInt n a).smtUDiv (BitVec.ofInt n b) := by
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

theorem ofInt_lit_urem {a : Int} (ha0 : 0 ≤ a) (ha1 : a < 2 ^ n) (b : Int) :
    BitVec.ofInt n (lit_urem (n : Int) a b) = BitVec.ofInt n a % BitVec.ofInt n b := by
  obtain ⟨p, rfl⟩ := Int.eq_ofNat_of_zero_le ha0
  have hp : p < 2 ^ n := by exact_mod_cast ha1
  unfold lit_urem
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
    have e : trem (p : Int) (y.toNat : Int) = ((p % y.toNat : Nat) : Int) := rfl
    rw [e, ← Int.natCast_emod, Int.toNat_natCast,
      Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.mod_le _ _) hp)]

theorem ofInt_lit_srem (hn : 0 < n) (a b : Int) :
    BitVec.ofInt n (lit_srem (n : Int) a b) = (BitVec.ofInt n a).srem (BitVec.ofInt n b) := by
  unfold lit_srem
  simp only [sext_of_eq hn]
  by_cases hd : (BitVec.ofInt n b).toInt = 0
  · have hy : BitVec.ofInt n b = 0#n := by
      apply BitVec.eq_of_toInt_eq; simpa using hd
    simp only [hd, ite_true]
    rw [hy, BitVec.srem_zero]
  · simp only [hd, ite_false, ofInt_masked']
    rw [trem, ← BitVec.toInt_srem, BitVec.ofInt_toInt]

theorem ofInt_lit_sdiv (hn : 0 < n) (a b : Int) :
    BitVec.ofInt n (lit_sdiv (n : Int) a b) = (BitVec.ofInt n a).smtSDiv (BitVec.ofInt n b) := by
  unfold lit_sdiv
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
    BitVec.ofInt n (lit_smod (n : Int) a b) = (BitVec.ofInt n a).smod (BitVec.ofInt n b) := by
  unfold lit_smod
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
    rw [key, ← smod_formula _ _ hd, trem]
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

theorem masked_nonneg' (w z : Int) : 0 ≤ masked w z := emod_two_pow_nonneg z w.toNat
theorem masked_lt' (z : Int) : masked (n : Int) z < 2 ^ n := by
  simpa [masked] using emod_two_pow_lt z n

theorem lit_udiv_nonneg (a b : Int) : 0 ≤ lit_udiv (n : Int) a b := by
  unfold lit_udiv; dsimp only; split <;> exact masked_nonneg' _ _
theorem lit_udiv_lt (a b : Int) : lit_udiv (n : Int) a b < 2 ^ n := by
  unfold lit_udiv; dsimp only; split <;> exact masked_lt' _
theorem lit_sdiv_nonneg (a b : Int) : 0 ≤ lit_sdiv (n : Int) a b := by
  unfold lit_sdiv; dsimp only; split <;> exact masked_nonneg' _ _
theorem lit_sdiv_lt (a b : Int) : lit_sdiv (n : Int) a b < 2 ^ n := by
  unfold lit_sdiv; dsimp only; split <;> exact masked_lt' _
theorem lit_urem_nonneg {a : Int} (ha : 0 ≤ a) (b : Int) : 0 ≤ lit_urem (n : Int) a b := by
  unfold lit_urem; dsimp only; split <;> first | exact ha | exact masked_nonneg' _ _
theorem lit_urem_lt {a : Int} (ha : a < 2 ^ n) (b : Int) : lit_urem (n : Int) a b < 2 ^ n := by
  unfold lit_urem; dsimp only; split <;> first | exact ha | exact masked_lt' _
theorem lit_srem_nonneg {a : Int} (ha : 0 ≤ a) (b : Int) : 0 ≤ lit_srem (n : Int) a b := by
  unfold lit_srem; dsimp only; split <;> first | exact ha | exact masked_nonneg' _ _
theorem lit_srem_lt {a : Int} (ha : a < 2 ^ n) (b : Int) : lit_srem (n : Int) a b < 2 ^ n := by
  unfold lit_srem; dsimp only; split <;> first | exact ha | exact masked_lt' _
theorem lit_smod_nonneg {a : Int} (ha : 0 ≤ a) (b : Int) : 0 ≤ lit_smod (n : Int) a b := by
  unfold lit_smod; dsimp only; split
  · exact ha
  · split <;> exact masked_nonneg' _ _
theorem lit_smod_lt {a : Int} (ha : a < 2 ^ n) (b : Int) : lit_smod (n : Int) a b < 2 ^ n := by
  unfold lit_smod; dsimp only; split
  · exact ha
  · split <;> exact masked_lt' _

end

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
elab "bveq_ovf_eqs" : tactic => liftMetaTactic fun g => return [← ovfEqs g]

open Lean Meta Elab Tactic in
elab "bveq_bounds" : tactic => liftMetaTactic fun g => return [← ovfBounds g]

open Lean Meta Elab Tactic in
/-- Case splits the booleans, and the checked flags. -/
partial def splitBools (g : MVarId) : MetaM (List MVarId) := g.withContext do
  for d in (← getLCtx) do
    if d.isImplementationDetail then continue
    let ty ← whnfR (← instantiateMVars d.type)
    if ty.isConstOf ``Bool || ty.isConstOf ``CoreMod.Checked then
      let subgoals ← g.cases d.fvarId
      return ← subgoals.toList.foldlM (init := []) fun acc sg =>
        return acc ++ (← splitBools sg.mvarId)
  return [g]

open Lean Meta Elab Tactic in
elab "bveq_bools" : tactic => liftMetaTactic splitBools

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
elab "bveq_bool_vars" : tactic => liftMetaTactic splitBoolVars


theorem toNat_emod_eq {w : Nat} (z : Int) : (z % 2 ^ w).toNat = (BitVec.ofInt w z).toNat := by
  rw [BitVec.toNat_ofInt]; push_cast; rfl

theorem natCast_toNat_ofInt {w : Nat} (z : Int) :
    max (z % 2 ^ w) 0 = ((BitVec.ofInt w z).toNat : Int) := by
  rw [BitVec.toNat_ofInt]; push_cast; omega

theorem ofInt_toNat_cast {n : Nat} {z : Int} (h0 : 0 ≤ z) (h1 : z < 2 ^ n) :
    ((BitVec.ofInt n z).toNat : Int) = z := by
  rw [toNat_ofInt_of_lt h0 h1]; omega

open Lean Meta Elab Tactic in
/-- Generalizes the values `BitVec.ofInt n z` of the literals (`z` a variable) to opaque
bit-vectors `k`. When `z` is in range, `k.toNat = z` replaces `z`. -/
partial def genLits : TacticM Unit := withMainContext do
  let isLitVal (e : Expr) : Bool :=
    e.isAppOfArity ``BitVec.ofInt 2 && e.appArg!.isFVar && !e.hasLooseBVars
  let g ← getMainGoal
  let ctxExprs := (← getLCtx).foldl (init := #[]) fun acc d =>
    if d.isImplementationDetail then acc else acc.push d.type
  let mut cands : Array Expr := #[]
  for e in #[← instantiateMVars (← g.getType)] ++ (← ctxExprs.mapM instantiateMVars) do
    let some a := e.find? isLitVal | continue
    unless cands.contains a do cands := cands.push a
  let tryRel (a : Expr) : TacticM Bool := do
    let c ← mkConstWithFreshMVarLevels ``ofInt_toNat_cast
    let (mvs, _, _) ← forallMetaTelescopeReducing (← inferType c)
    unless (← isDefEq mvs[0]! a.appFn!.appArg!) && (← isDefEq mvs[1]! a.appArg!) do return false
    for mv in mvs[2:] do
      let some h ← Kanon.Proof.findHyp (← instantiateMVars (← inferType mv)) | return false
      unless ← isDefEq mv h do return false
    let pf ← instantiateMVars (mkAppN c mvs)
    let (_, g) ← (← (← getMainGoal).assert `hlit (← inferType pf) pf).intro1P
    replaceMainGoal [g]
    return true
  let mut chosen : Option Expr := none
  for a in cands do
    if ← tryRel a then chosen := some a; break
  let hasRel := chosen.isSome
  let some a := chosen <|> cands[0]? | return
  let g ← getMainGoal
  let hyps := (← g.withContext getLCtx).foldl (init := #[]) fun acc d =>
    if d.isImplementationDetail then acc else acc.push d
  let (_, _, g) ← g.withContext <| g.generalizeHyp #[{ expr := a, xName? := `k }] (hyps.map (·.fvarId))
  replaceMainGoal [g]
  if hasRel then evalTactic (← `(tactic| subst $(mkIdent `hlit)))
  genLits


open Lean Meta Elab Tactic in
/-- Replaces `(↑n : Int).toNat` by `n` everywhere, instances included. -/
def fixWidths (g : MVarId) : MetaM MVarId := g.withContext do
  let fix (e : Expr) : Expr := e.replace fun t =>
    if t.isAppOfArity ``Int.toNat 1 then
      let a := t.appArg!
      if a.isAppOfArity ``Nat.cast 3 then some a.appArg!
      else if let some k := a.int? then (if 0 ≤ k then some (mkNatLit k.toNat) else none)
      else if a.isAppOfArity ``HAdd.hAdd 6 && (a.getArg! 4).isAppOfArity ``Nat.cast 3 &&
          (a.getArg! 5).isAppOfArity ``Nat.cast 3 then
        some (mkNatAdd (a.getArg! 4).appArg! (a.getArg! 5).appArg!)
      else none
    else none
  let mut g := g
  for d in (← getLCtx) do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    let ty' := fix ty
    if ty' != ty then g ← g.replaceLocalDeclDefEq d.fvarId ty'
  let t ← instantiateMVars (← g.getType)
  let t' := fix t
  if t' != t then g ← g.replaceTargetDefEq t'
  return g

open Lean Meta Elab Tactic in
elab "bveq_fix_widths" : tactic => liftMetaTactic fun g => return [← fixWidths g]

open Lean Meta Elab Tactic in
/-- Proves a goal on bit-vectors of small literal widths by enumerating them. -/
elab "bveq_decide_small" : tactic => do
  let g ← getMainGoal
  let fvs ← g.withContext do
    let mut small : Array FVarId := #[]
    for d in (← getLCtx) do
      if d.isImplementationDetail then continue
      let ty ← whnfR (← instantiateMVars d.type)
      if ty.isAppOfArity ``BitVec 1 then
        if let some n := (← instantiateMVars ty.appArg!).nat? then
          if n ≤ 4 then small := small.push d.fvarId
    let mut fvs := small
    for d in (← getLCtx) do
      if d.isImplementationDetail || small.contains d.fvarId then continue
      let ty ← instantiateMVars d.type
      unless ← isProp ty do continue
      let used := (collectFVars {} ty).fvarIds
      if used.all small.contains then fvs := fvs.push d.fvarId
    return fvs
  let (_, g') ← g.revert fvs
  replaceMainGoal [g']
  evalTactic (← `(tactic| decide))

open Lean Meta Elab Tactic in
elab "bveq_gen_lits" : tactic => genLits



section
variable {w : Nat} {k x : BitVec w}

theorem sadd_pos (hw : 0 < w) (h : 0 < k.toInt) :
    (BitVec.ofInt w (2 ^ (w - 1) - 1 - k.toInt)).slt x = k.saddOverflow x := by
  have := toInt_bounds k; have := toInt_bounds x
  rw [BitVec.slt, BitVec.toInt_ofInt_eq_self hw]
  · rw [Bool.eq_iff_iff]; simp [BitVec.saddOverflow]; omega
  all_goals omega

theorem sadd_nonpos (hw : 0 < w) (h : k.toInt ≤ 0) :
    x.slt (BitVec.ofInt w (-2 ^ (w - 1) - k.toInt)) = k.saddOverflow x := by
  have := toInt_bounds k; have := toInt_bounds x
  rw [BitVec.slt, BitVec.toInt_ofInt_eq_self hw]
  · rw [Bool.eq_iff_iff]; simp [BitVec.saddOverflow]; omega
  all_goals omega

theorem uadd_not : (~~~k).ult x = k.uaddOverflow x := by
  have := k.isLt; have := x.isLt
  simp only [BitVec.uaddOverflow, BitVec.ult, BitVec.toNat_not]
  rw [Bool.eq_iff_iff]; simp; omega

theorem usub_self : x.usubOverflow x = false := by simp [BitVec.usubOverflow]

theorem ssub_self : x.ssubOverflow x = false := by
  have := toInt_bounds x
  simp [BitVec.ssubOverflow]; omega

theorem uadd_zero : (0#w).uaddOverflow x = false := by
  have := x.isLt; simp [BitVec.uaddOverflow]; omega

theorem sadd_zero : (0#w).saddOverflow x = false := by
  have := toInt_bounds x; simp [BitVec.saddOverflow]; omega

theorem sadd_pos' (hw : 0 < w) (h : 0 < k.toInt) :
    (BitVec.ofInt w (2 ^ (w - 1) - 1 - k.toInt)).slt x = x.saddOverflow k := by
  rw [sadd_pos hw h, (ovf_comm _ _).1]

theorem sadd_nonpos' (hw : 0 < w) (h : k.toInt ≤ 0) :
    x.slt (BitVec.ofInt w (-2 ^ (w - 1) - k.toInt)) = x.saddOverflow k := by
  rw [sadd_nonpos hw h, (ovf_comm _ _).1]

theorem uadd_not' : (~~~k).ult x = x.uaddOverflow k := by
  rw [uadd_not, (ovf_comm _ _).2.1]

theorem uadd_zero' : x.uaddOverflow 0#w = false := by rw [(ovf_comm _ _).2.1, uadd_zero]

theorem sadd_zero' : x.saddOverflow 0#w = false := by rw [(ovf_comm _ _).1, sadd_zero]

theorem one_uadd (hw : 0 < w) : (1#w).uaddOverflow x = decide (x = BitVec.ofInt w (2 ^ w - 1)) := by
  have := x.isLt
  have h1 : 1 % 2 ^ w = 1 := Nat.mod_eq_of_lt (Nat.one_lt_two_pow (by omega))
  have hp : ((2 ^ w : Nat) : Int) = (2 : Int) ^ w := by push_cast; rfl
  have := Nat.one_lt_two_pow (n := w) (by omega)
  have e : x = BitVec.ofInt w (2 ^ w - 1) ↔ x.toNat = 2 ^ w - 1 := by
    rw [← BitVec.toNat_inj, BitVec.toNat_ofInt, hp, Int.emod_eq_of_lt (by omega) (by omega)]
    omega
  rw [Bool.eq_iff_iff]; simp [BitVec.uaddOverflow, e, h1]; omega

theorem one_sadd (hw : (1 : Int) < w) :
    (1#w).saddOverflow x = decide (x = BitVec.ofInt w (2 ^ (w - 1) - 1)) := by
  have := toInt_bounds x
  have e : x = BitVec.ofInt w (2 ^ (w - 1) - 1) ↔ x.toInt = 2 ^ (w - 1) - 1 := by
    rw [← BitVec.toInt_inj, BitVec.toInt_ofInt_eq_self (by omega)] <;>
      omega
  rw [Bool.eq_iff_iff]; simp [BitVec.saddOverflow, e, BitVec.toInt_one (show 1 < w by omega)]; omega

theorem one_uadd' (hw : 0 < w) : x.uaddOverflow 1#w = decide (x = BitVec.ofInt w (2 ^ w - 1)) := by
  rw [(ovf_comm _ _).2.1, one_uadd hw]

theorem one_sadd' (hw : (1 : Int) < w) :
    x.saddOverflow 1#w = decide (x = BitVec.ofInt w (2 ^ (w - 1) - 1)) := by
  rw [(ovf_comm _ _).1, one_sadd hw]

theorem one_uadd_one (hw : (1 : Int) < w) : (1#w).uaddOverflow 1#w = false := by
  have h4 : 4 ≤ 2 ^ w := by
    have := Nat.pow_le_pow_right (n := 2) (by omega) (show 2 ≤ w by omega); simpa using this
  have h1 : 1 % 2 ^ w = 1 := Nat.mod_eq_of_lt (by omega)
  simp [BitVec.uaddOverflow, h1]; omega

theorem one_sadd_one (hw : (1 : Int) < w) (h2 : ¬(w : Int) = 2) : (1#w).saddOverflow 1#w = false := by
  have h4 : 4 ≤ 2 ^ (w - 1) := by
    have := Nat.pow_le_pow_right (n := 2) (by omega) (show 2 ≤ w - 1 by omega); simpa using this
  have : (4 : Int) ≤ 2 ^ (w - 1) := by exact_mod_cast h4
  simp [BitVec.saddOverflow, BitVec.toInt_one (show 1 < w by omega)]; omega


theorem umul_udiv : x.umulOverflow (k.smtUDiv x) = false := by
  rw [umul_ok]
  by_cases hx : x.toNat = 0
  · simp [hx, Nat.two_pow_pos]
  · rw [smtUDiv_toNat hx]
    exact Nat.lt_of_le_of_lt (Nat.mul_div_le _ _) k.isLt


theorem umul_udiv' : (k.smtUDiv x).umulOverflow x = false := by
  rw [(ovf_comm _ _).2.2.2, umul_udiv]


theorem int_mul_pos_ovf {M z y : Int} (hz : 0 < z) :
    (M ≤ z * y ∨ z * y < -M) ↔ (y < -(M / z) ∨ (M - 1) / z < y) := by
  have e1 := Int.ediv_lt_iff_lt_mul (a := M) (b := -y) hz
  have e2 := Int.ediv_lt_iff_lt_mul (a := M - 1) (b := y) hz
  rw [Int.neg_mul, Int.mul_comm y] at e1
  rw [Int.mul_comm y] at e2
  constructor
  · rintro (h | h)
    · exact Or.inr (e2.2 (by omega))
    · exact Or.inl (by have := e1.2 (by omega); omega)
  · rintro (h | h)
    · exact Or.inr (by have := e1.1 (by omega); omega)
    · exact Or.inl (by have := e2.1 h; omega)

theorem int_mul_neg_ovf {M z y : Int} (hz : z < 0) :
    (M ≤ z * y ∨ z * y < -M) ↔ (y < -((M - 1) / -z) ∨ M / -z < y) := by
  have := int_mul_pos_ovf (M := M) (z := -z) (y := -y) (by omega)
  rw [Int.neg_mul_neg] at this
  constructor
  · intro h; rcases this.1 (by omega) with h' | h' <;> omega
  · intro h; rcases this.2 (by omega) with h' | h' <;> omega


theorem smul_pos (hw : 0 < w) (hk : 1 < k.toInt) :
    k.smulOverflow x = (x.slt (BitVec.ofInt w ((-2 ^ (w - 1) : Int).tdiv k.toInt)) ||
      (BitVec.ofInt w ((2 ^ (w - 1) - 1 : Int).tdiv k.toInt)).slt x) := by
  have hx := toInt_bounds x; have hkb := toInt_bounds k
  have hM : (0 : Int) < 2 ^ (w - 1) := Int.pow_pos (by decide)
  rw [Int.neg_tdiv, Int.tdiv_eq_ediv_of_nonneg (by omega), Int.tdiv_eq_ediv_of_nonneg (by omega)]
  have q1 := Int.ediv_le_self k.toInt (by omega : (0 : Int) ≤ 2 ^ (w - 1))
  have q1' := Int.ediv_nonneg (by omega : (0 : Int) ≤ 2 ^ (w - 1)) (by omega : (0 : Int) ≤ k.toInt)
  have q2 := Int.ediv_le_self k.toInt (by omega : (0 : Int) ≤ 2 ^ (w - 1) - 1)
  have q2' := Int.ediv_nonneg (by omega : (0 : Int) ≤ 2 ^ (w - 1) - 1)
    (by omega : (0 : Int) ≤ k.toInt)
  simp only [BitVec.smulOverflow, BitVec.slt,
    BitVec.toInt_ofInt_eq_self hw (by omega : -2 ^ (w - 1) ≤ -(2 ^ (w - 1) / k.toInt)) (by omega),
    BitVec.toInt_ofInt_eq_self hw (by omega : -2 ^ (w - 1) ≤ (2 ^ (w - 1) - 1) / k.toInt) (by omega)]
  rw [Bool.eq_iff_iff]; simp only [Bool.or_eq_true, decide_eq_true_eq, ge_iff_le]
  exact int_mul_pos_ovf (by omega)

theorem smul_neg (hw : 0 < w) (hk : k.toInt < -1) :
    k.smulOverflow x = (x.slt (BitVec.ofInt w ((2 ^ (w - 1) - 1 : Int).tdiv k.toInt)) ||
      (BitVec.ofInt w ((-2 ^ (w - 1) : Int).tdiv k.toInt)).slt x) := by
  have hx := toInt_bounds x; have hkb := toInt_bounds k
  have hM : (0 : Int) < 2 ^ (w - 1) := Int.pow_pos (by decide)
  have ek : k.toInt = -(-k.toInt) := by omega
  rw [ek, Int.neg_tdiv_neg, Int.tdiv_neg, Int.tdiv_eq_ediv_of_nonneg (by omega),
    Int.tdiv_eq_ediv_of_nonneg (by omega)]
  have q1 := Int.ediv_lt_of_lt_mul (a := 2 ^ (w - 1)) (b := 2 ^ (w - 1)) (c := -k.toInt)
    (by omega) (by
      have := Int.mul_le_mul_of_nonneg_left (show (2 : Int) ≤ -k.toInt by omega) (Int.le_of_lt hM)
      omega)
  have q1' := Int.ediv_nonneg (by omega : (0 : Int) ≤ 2 ^ (w - 1)) (by omega : (0 : Int) ≤ -k.toInt)
  have q2 := Int.ediv_le_self (-k.toInt) (by omega : (0 : Int) ≤ 2 ^ (w - 1) - 1)
  have q2' := Int.ediv_nonneg (by omega : (0 : Int) ≤ 2 ^ (w - 1) - 1)
    (by omega : (0 : Int) ≤ -k.toInt)
  simp only [BitVec.smulOverflow, BitVec.slt,
    BitVec.toInt_ofInt_eq_self hw
      (by omega : -2 ^ (w - 1) ≤ -((2 ^ (w - 1) - 1) / -k.toInt)) (by omega),
    BitVec.toInt_ofInt_eq_self hw (by omega : -2 ^ (w - 1) ≤ 2 ^ (w - 1) / -k.toInt) (by omega)]
  rw [Bool.eq_iff_iff]; simp only [Bool.or_eq_true, decide_eq_true_eq, ge_iff_le]
  exact int_mul_neg_ovf (by omega)

theorem smul_neg_one (hw : 0 < w) (hk : k.toInt = -1) :
    k.smulOverflow x = decide (x = BitVec.ofInt w (-2 ^ (w - 1))) := by
  have hx := toInt_bounds x
  have e : x = BitVec.ofInt w (-2 ^ (w - 1)) ↔ x.toInt = -2 ^ (w - 1) := by
    rw [← BitVec.toInt_inj, BitVec.toInt_ofInt_eq_self hw] <;> omega
  rw [Bool.eq_iff_iff]; simp [BitVec.smulOverflow, e, hk]; omega

theorem umul_const (hk : 0 < k.toNat) :
    k.umulOverflow x = (BitVec.ofInt w ((2 ^ w - 1 : Int).tdiv k.toNat)).ult x := by
  have := x.isLt; have := k.isLt
  have hp : ((2 ^ w : Nat) : Int) = (2 : Int) ^ w := by push_cast; rfl
  have q := Int.ediv_le_self (k.toNat : Int) (by omega : (0 : Int) ≤ 2 ^ w - 1)
  have q' := Int.ediv_nonneg (by omega : (0 : Int) ≤ 2 ^ w - 1) (by omega : (0 : Int) ≤ k.toNat)
  rw [Int.tdiv_eq_ediv_of_nonneg (by omega)]
  simp only [BitVec.umulOverflow, BitVec.ult, BitVec.toNat_ofInt, hp,
    Int.emod_eq_of_lt q' (show (2 ^ w - 1) / (k.toNat : Int) < (2 : Int) ^ w by omega)]
  have e := Int.ediv_lt_iff_lt_mul (a := 2 ^ w - 1) (b := (x.toNat : Int))
    (by omega : (0 : Int) < k.toNat)
  rw [Bool.eq_iff_iff]; simp only [decide_eq_true_eq, ge_iff_le]
  have : ((k.toNat * x.toNat : Nat) : Int) = (x.toNat : Int) * k.toNat := by push_cast; rw [Int.mul_comm]
  omega


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

theorem ne_and_of_mask {k m x : BitVec w} (h : ¬(k &&& ~~~m) = 0#w) : ¬k = m &&& x := by
  rintro rfl; apply h; ext i; simp; intro h1 _; exact h1

theorem mul_cancel_nat {M a b d : Nat} (hM : Nat.Coprime M a) (hb : b < M) (hd : d < M)
    (h : a * b % M = a * d % M) : b = d := by
  rcases Nat.le_total b d with hbd | hbd
  · have h1 := Nat.sub_mod_eq_zero_of_mod_eq h.symm
    rw [← Nat.mul_sub] at h1
    have h2 := hM.dvd_of_dvd_mul_left (Nat.dvd_of_mod_eq_zero h1)
    have := Nat.eq_zero_of_dvd_of_lt h2 (by omega)
    omega
  · have h1 := Nat.sub_mod_eq_zero_of_mod_eq h
    rw [← Nat.mul_sub] at h1
    have h2 := hM.dvd_of_dvd_mul_left (Nat.dvd_of_mod_eq_zero h1)
    have := Nat.eq_zero_of_dvd_of_lt h2 (by omega)
    omega

theorem mul_cancel_odd {k a b : BitVec w} (h : k.toNat % 2 = 1) : k * a = k * b ↔ a = b := by
  refine ⟨fun e => BitVec.eq_of_toNat_eq ?_, fun e => by rw [e]⟩
  have := congrArg BitVec.toNat e
  simp only [BitVec.toNat_mul] at this
  refine mul_cancel_nat ?_ a.isLt b.isLt this
  apply Nat.Coprime.pow_left
  show Nat.gcd 2 k.toNat = 1
  rw [Nat.gcd_rec, h]; rfl

theorem mul_cancel_umul {k a b : BitVec w} (hk : k ≠ 0#w) (ha : k.umulOverflow a = false)
    (hb : k.umulOverflow b = false) : k * a = k * b ↔ a = b := by
  refine ⟨fun e => BitVec.eq_of_toNat_eq ?_, fun e => by rw [e]⟩
  have := congrArg BitVec.toNat e
  rw [toNat_mul_ok ha, toNat_mul_ok hb] at this
  exact Nat.eq_of_mul_eq_mul_left (BitVec.toNat_pos_of_ne_zero hk) this

theorem mul_cancel_smul {k a b : BitVec w} (hk : k ≠ 0#w) (ha : k.smulOverflow a = false)
    (hb : k.smulOverflow b = false) : k * a = k * b ↔ a = b := by
  refine ⟨fun e => BitVec.eq_of_toInt_eq ?_, fun e => by rw [e]⟩
  have := congrArg BitVec.toInt e
  rw [toInt_mul_ok ha, toInt_mul_ok hb] at this
  have : k.toInt ≠ 0 := by
    intro h0; apply hk; exact BitVec.eq_of_toInt_eq (by simp [h0])
  exact Int.eq_of_mul_eq_mul_left this ‹_›

theorem zshiftl_one_pred (hw : 0 < w) : z_lsl 1 ((w : Int) - 1) = 2 ^ (w - 1) := by
  simp only [z_lsl, Int.one_mul]; congr 1; omega

theorem zshiftl_one_nat : z_lsl 1 (w : Int) = 2 ^ w := by simp [z_lsl]

theorem toInt_pos_ne_one (h0 : 0 < k.toInt) (h1 : ¬(k.toNat : Int) = 1) :
    1 < k.toInt := by
  have h := BitVec.toInt_eq_toNat_cond k
  have := k.isLt
  have : ((2 ^ w : Nat) : Int) > k.toNat := by exact_mod_cast this
  split at h <;> omega

theorem umul_small (h : k.toNat = 0 ∨ (k.toNat : Int) = 1) : k.umulOverflow x = false := by
  have := x.isLt
  rw [umul_ok]; rcases h with h | h
  · simp [h, Nat.two_pow_pos]
  · have : k.toNat = 1 := by omega
    simp [this, x.isLt]

theorem smul_small (hw : (1 : Int) < w) (h : k.toNat = 0 ∨ (k.toNat : Int) = 1) :
    k.smulOverflow x = false := by
  have := toInt_bounds x
  have e : k.toInt = 0 ∨ k.toInt = 1 := by
    rw [BitVec.toInt_eq_toNat_cond]
    have : 4 ≤ 2 ^ w := by
      have := Nat.pow_le_pow_right (n := 2) (by omega) (show 2 ≤ w by omega); simpa using this
    split <;> omega
  have : (0 : Int) < 2 ^ (w - 1) := Int.pow_pos (by decide)
  rw [smul_ok]; rcases e with e | e <;> rw [e] <;> omega

theorem smul_const_pos (hw : (1 : Int) < w) (h0 : 0 < k.toInt) (h1 : ¬(k.toNat : Int) = 1) :
    k.smulOverflow x = (x.slt (BitVec.ofInt w (tdiv (-z_lsl 1 ((w : Int) - 1)) k.toInt)) ||
      (BitVec.ofInt w (tdiv (z_lsl 1 ((w : Int) - 1) - 1) k.toInt)).slt x) := by
  rw [zshiftl_one_pred (by omega), smul_pos (by omega) (toInt_pos_ne_one h0 h1)]; rfl

theorem smul_const_neg (hw : (1 : Int) < w) (h0 : ¬k.toNat = 0) (h1 : k.toInt ≤ 0)
    (h2 : ¬k.toInt = -1) :
    k.smulOverflow x = (x.slt (BitVec.ofInt w (tdiv (z_lsl 1 ((w : Int) - 1) - 1) k.toInt)) ||
      (BitVec.ofInt w (tdiv (-z_lsl 1 ((w : Int) - 1)) k.toInt)).slt x) := by
  have : k.toInt ≠ 0 := by
    intro e; apply h0; have := BitVec.eq_of_toInt_eq (x := k) (y := 0#w) (by simp [e]); simp [this]
  rw [zshiftl_one_pred (by omega), smul_neg (by omega) (by omega)]; rfl

theorem smul_const_neg_one (hw : (1 : Int) < w) (h : k.toInt = -1) :
    k.smulOverflow x = decide (x = BitVec.ofInt w (-z_lsl 1 ((w : Int) - 1))) := by
  rw [zshiftl_one_pred (by omega), smul_neg_one (by omega) h]

theorem umul_const_rule (h0 : ¬k.toNat = 0) :
    k.umulOverflow x = (BitVec.ofInt w (tdiv (z_lsl 1 (w : Int) - 1) k.toNat)).ult x := by
  rw [zshiftl_one_nat, umul_const (by omega)]; rfl

theorem umul_small' (h : k.toNat = 0 ∨ (k.toNat : Int) = 1) : x.umulOverflow k = false := by
  rw [(ovf_comm _ _).2.2.2, umul_small h]
theorem smul_small' (hw : (1 : Int) < w) (h : k.toNat = 0 ∨ (k.toNat : Int) = 1) :
    x.smulOverflow k = false := by
  rw [(ovf_comm _ _).2.2.1, smul_small hw h]
theorem smul_const_pos' (hw : (1 : Int) < w) (h0 : 0 < k.toInt) (h1 : ¬(k.toNat : Int) = 1) :
    x.smulOverflow k = (x.slt (BitVec.ofInt w (tdiv (-z_lsl 1 ((w : Int) - 1)) k.toInt)) ||
      (BitVec.ofInt w (tdiv (z_lsl 1 ((w : Int) - 1) - 1) k.toInt)).slt x) := by
  rw [(ovf_comm _ _).2.2.1, smul_const_pos hw h0 h1]
theorem smul_const_neg' (hw : (1 : Int) < w) (h0 : ¬k.toNat = 0) (h1 : k.toInt ≤ 0)
    (h2 : ¬k.toInt = -1) :
    x.smulOverflow k = (x.slt (BitVec.ofInt w (tdiv (z_lsl 1 ((w : Int) - 1) - 1) k.toInt)) ||
      (BitVec.ofInt w (tdiv (-z_lsl 1 ((w : Int) - 1)) k.toInt)).slt x) := by
  rw [(ovf_comm _ _).2.2.1, smul_const_neg hw h0 h1 h2]
theorem smul_const_neg_one' (hw : (1 : Int) < w) (h : k.toInt = -1) :
    x.smulOverflow k = decide (x = BitVec.ofInt w (-z_lsl 1 ((w : Int) - 1))) := by
  rw [(ovf_comm _ _).2.2.1, smul_const_neg_one hw h]
theorem umul_const_rule' (h0 : ¬k.toNat = 0) :
    x.umulOverflow k = (BitVec.ofInt w (tdiv (z_lsl 1 (w : Int) - 1) k.toNat)).ult x := by
  rw [(ovf_comm _ _).2.2.2, umul_const_rule h0]

theorem smul_neg_ok {a b : BitVec w} (ha : a ≠ BitVec.intMin w) (hb : b ≠ BitVec.intMin w)
    (h : (-a).smulOverflow b = false) : (-b).smulOverflow a = false := by
  rw [smul_ok] at h ⊢
  rw [BitVec.toInt_neg_of_ne_intMin ha] at h
  rw [BitVec.toInt_neg_of_ne_intMin hb]
  rw [Int.neg_mul] at h ⊢
  rwa [Int.mul_comm b.toInt a.toInt]

theorem umul_swap_ok {w a b : BitVec n} (h1 : w.umulOverflow a = false)
    (h2 : b.umulOverflow (w * a) = false) : w.umulOverflow (a * b) = false := by
  rw [umul_ok] at h1 h2 ⊢
  rw [BitVec.toNat_mul, Nat.mod_eq_of_lt h1] at h2
  rw [BitVec.toNat_mul]
  calc w.toNat * (a.toNat * b.toNat % 2 ^ n) ≤ w.toNat * (a.toNat * b.toNat) :=
        Nat.mul_le_mul_left _ (Nat.mod_le _ _)
    _ = b.toNat * (w.toNat * a.toNat) := by rw [Nat.mul_comm b.toNat, Nat.mul_assoc]
    _ < 2 ^ n := h2

theorem smul_swap_ok {w a b : BitVec n} (h0 : a.smulOverflow b = false) (h1 : w.smulOverflow a = false)
    (h2 : b.smulOverflow (w * a) = false) : w.smulOverflow (a * b) = false := by
  rw [smul_ok] at h2 ⊢
  rw [toInt_mul_ok h1] at h2
  rw [toInt_mul_ok h0]
  have e : w.toInt * (a.toInt * b.toInt) = b.toInt * (w.toInt * a.toInt) := by
    rw [Int.mul_comm b.toInt, Int.mul_assoc]
  rwa [e]

theorem umul_swap_ok' {w a b : BitVec n} (h1 : a.umulOverflow w = false)
    (h2 : b.umulOverflow (a * w) = false) : w.umulOverflow (a * b) = false := by
  rw [BitVec.mul_comm] at h2
  exact umul_swap_ok (by rwa [umul_ok, Nat.mul_comm, ← umul_ok]) h2

theorem smul_swap_ok' {w a b : BitVec n} (h0 : a.smulOverflow b = false) (h1 : a.smulOverflow w = false)
    (h2 : b.smulOverflow (a * w) = false) : w.smulOverflow (a * b) = false := by
  rw [BitVec.mul_comm] at h2
  exact smul_swap_ok h0 (by rwa [smul_ok, Int.mul_comm, ← smul_ok]) h2

theorem umod_umod_of_lt {v a b : BitVec w} (hb : 0 < b.toNat) (h : b.toNat < a.toNat)
    (hd : b.toNat ∣ a.toNat ∨ a.toNat ∣ b.toNat) : v % a % b = v % b := by
  rcases hd with hd | hd
  · exact umod_umod_of_dvd hd
  · have := Nat.le_of_dvd hb hd; omega

theorem extract_umod_pow2_ofInt {w n : Nat} {to_ z : Int} (a : BitVec w) (hp : L.bitvec_is_pow2 z = true)
    (hl : log2 z < to_) (ht : to_ + 1 = n) (hw : to_ < w) :
    a.extractLsb' 0 n % (BitVec.ofInt w z).extractLsb' 0 n =
      (a % BitVec.ofInt w z).extractLsb' 0 n := by
  obtain ⟨k, rfl⟩ := is_pow2_exists hp
  simp only [log2_two_pow] at hl
  have hb : (BitVec.ofInt w ((2 : Int) ^ k)).toNat = 2 ^ k := by
    have e : ((2 ^ k : Nat) : Int) = 2 ^ k := by push_cast; rfl
    rw [← e, BitVec.ofInt_natCast, BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by omega) (by omega))
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_umod, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow,
    Nat.pow_zero, Nat.div_one, hb]
  rw [Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by omega) (by omega) : 2 ^ k < 2 ^ n),
    Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by omega))]
  have hlt : a.toNat % 2 ^ k < 2 ^ n :=
    Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos k)) (Nat.pow_le_pow_right (by omega) (by omega))
  exact (Nat.mod_eq_of_lt hlt).symm

theorem extract_umod_pow2' {w n : Nat} {to_ : Int} (a k : BitVec w) (hp : L.bitvec_is_pow2 (k.toNat : Int) = true)
    (hl : log2 (k.toNat : Int) < to_) (ht : to_ + 1 = n) (hw : to_ < w) :
    a.extractLsb' 0 n % k.extractLsb' 0 n = (a % k).extractLsb' 0 n := by
  have := extract_umod_pow2_ofInt a hp hl ht hw
  rwa [BitVec.ofInt_natCast, BitVec.ofNat_toNat, BitVec.setWidth_eq] at this

theorem umod_umod_of_le_ofNat {n a b : Nat} {v : BitVec n} (ha : 0 < a) (ha1 : (a : Int) < 2 ^ n)
    (hb1 : (b : Int) < 2 ^ n) (h : a ≤ b) :
    v % BitVec.ofNat n a % BitVec.ofNat n b = v % BitVec.ofNat n a := by
  have ha1' : a < 2 ^ n := by exact_mod_cast ha1
  have hb1' : b < 2 ^ n := by exact_mod_cast hb1
  apply umod_umod_of_le <;> simp [Nat.mod_eq_of_lt ha1', Nat.mod_eq_of_lt hb1', ha, h]

theorem umod_umod_of_lt_ofNat {n a b : Nat} {v : BitVec n} (hb : 0 < b) (ha1 : (a : Int) < 2 ^ n)
    (hb1 : (b : Int) < 2 ^ n) (h : b < a) (hd : b % 2 ^ n ∣ a % 2 ^ n ∨ a % 2 ^ n ∣ b % 2 ^ n) :
    v % BitVec.ofNat n a % BitVec.ofNat n b = v % BitVec.ofNat n b := by
  have ha1' : a < 2 ^ n := by exact_mod_cast ha1
  have hb1' : b < 2 ^ n := by exact_mod_cast hb1
  rw [Nat.mod_eq_of_lt ha1', Nat.mod_eq_of_lt hb1'] at hd
  apply umod_umod_of_lt <;> simp [Nat.mod_eq_of_lt ha1', Nat.mod_eq_of_lt hb1', hb, h, hd]

theorem ne_and_of_mask' {k m x : BitVec w} (h : ¬(k.toNat &&& (2 ^ w - 1 - m.toNat)) = 0) :
    ¬k = m &&& x := by
  apply ne_and_of_mask; intro e; apply h
  have := congrArg BitVec.toNat e
  simpa [BitVec.toNat_and, BitVec.toNat_not] using this

theorem append_inj {w' : Nat} {a c : BitVec w} {b d : BitVec w'} :
    a ++ b = c ++ d ↔ a = c ∧ b = d := by
  constructor
  · intro h
    have h1 := congrArg (fun x => x.extractLsb' w' w) h
    have h2 := congrArg (fun x => x.extractLsb' 0 w') h
    simp only [BitVec.extractLsb'_append_eq_left, BitVec.extractLsb'_append_eq_right] at h1 h2
    exact ⟨h1, h2⟩
  · rintro ⟨rfl, rfl⟩; rfl

theorem and_not_self_toNat {k v : BitVec w} : k.toNat &&& v.toNat &&& (2 ^ w - 1 - k.toNat) = 0 := by
  have : k &&& v &&& ~~~k = 0#w := by ext i; simp; intro h _; exact h
  simpa [BitVec.toNat_and, BitVec.toNat_not] using congrArg BitVec.toNat this

theorem toNat_eq_zero_iff {k : BitVec w} : k.toNat = 0 ↔ k = 0#w := by
  rw [← BitVec.toNat_inj]; simp

theorem natCast_toNat_eq_one (hw : 0 < w) {k : BitVec w} : ((k.toNat : Int) = 1) ↔ k = 1#w := by
  rw [← BitVec.toNat_inj]; simp [Nat.one_mod_two_pow hw]; omega

theorem zland_one (n : Nat) : z_land (n : Int) 1 = ((n % 2 : Nat) : Int) := by
  show Int.ofNat (n &&& 1) = _
  rw [Nat.and_one_is_mod]; rfl

theorem mul_cancel_flags {k a b : BitVec w} {s1 u1 s2 u2 : Bool}
    (h : z_land (k.toNat : Int) 1 = 1 ∨
      ¬k.toNat = 0 ∧ (s1 = true ∧ s2 = true ∨ u1 = true ∧ u2 = true))
    (h1 : (s1 = true → k.smulOverflow a = false) ∧ (u1 = true → k.umulOverflow a = false))
    (h2 : (s2 = true → k.smulOverflow b = false) ∧ (u2 = true → k.umulOverflow b = false)) :
    k * a = k * b ↔ a = b := by
  rw [zland_one] at h
  rcases h with h | ⟨h0, (⟨hs1, hs2⟩ | ⟨hu1, hu2⟩)⟩
  · exact mul_cancel_odd (by omega)
  · exact mul_cancel_smul (by rwa [ne_eq, ← toNat_eq_zero_iff]) (h1.1 hs1) (h2.1 hs2)
  · exact mul_cancel_umul (by rwa [ne_eq, ← toNat_eq_zero_iff]) (h1.2 hu1) (h2.2 hu2)

end


/-! ## Division of products -/

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


/-! ## Nonzero literals -/

theorem ofInt_ne_zero {n : Nat} {z : Int} (h0 : 0 < z) (h1 : z < 2 ^ n) : BitVec.ofInt n z ≠ 0 := by
  intro e
  have := congrArg BitVec.toNat e
  rw [toNat_ofInt_of_lt (by omega) h1] at this
  simp at this; omega

theorem nonzero_lit {z : Int} {t : S.Ty} (h0 : 0 < z)
    (h1 : z < 2 ^ (L.bitvec_size_of_ty t).toNat) : L.Nonzero (B.node (L.BitVecK z) t) :=
  Sem.nonzero_BitVec z t fun n hn => ofInt_ne_zero h0 (by rw [hn] at h1; simpa using h1)

/-- The product of two literals, of which the second is nonzero, is nonzero when it does not
overflow (if the second is zero, the product is the same literal). -/
theorem nonzero_lit_mul {n d : Int} {w : Nat} (hw : 0 < w) (hn : n ≠ 0) (h0n : 0 ≤ n)
    (h1n : n < 2 ^ w) (h0d : 0 ≤ d) (h1d : d < 2 ^ w)
    (ho : L.bitvec_overflows_mul false w n d = false)
    (hd : L.Nonzero (B.node (L.BitVecK d) (L.TBitVector w))) :
    L.Nonzero (B.node (L.BitVecK (Prim.lit_mul w n d % 2 ^ w)) (L.TBitVector w)) := by
  by_cases hd0 : d = 0
  · subst hd0
    simpa [Prim.lit_mul, Prim.masked] using hd
  · rw [overflows_mul_ofInt hw false h0n h1n h0d h1d] at ho
    simp only [Bool.false_eq_true, ite_false, umul_ok, toNat_ofInt_of_lt h0n h1n,
      toNat_ofInt_of_lt h0d h1d] at ho
    have hp : n * d < 2 ^ w := by
      have : ((n.toNat * d.toNat : Nat) : Int) < ((2 ^ w : Nat) : Int) := by exact_mod_cast ho
      push_cast at this; rwa [Int.toNat_of_nonneg h0n, Int.toNat_of_nonneg h0d] at this
    have hpos : 0 < n * d := Int.mul_pos (by omega) (by omega)
    have e : Prim.lit_mul (w : Int) n d % 2 ^ w = n * d := by
      simp only [Prim.lit_mul, Prim.masked, Int.toNat_natCast]
      rw [Int.emod_emod, Int.emod_eq_of_lt (by omega) hp]
    rw [e]
    exact nonzero_lit hpos (by simpa [Sem.size_of_ty_TBitVector] using hp)

/-- The quotient of two literals, the second dividing the first, is nonzero (if the first is
zero, the quotient is the same literal). -/
theorem nonzero_lit_udiv {n d : Int} {w : Nat} (hw : 0 < w) (hn : n ≠ 0) (h0n : 0 ≤ n)
    (h1n : n < 2 ^ w) (h0d : 0 ≤ d) (h1d : d < 2 ^ w) (hdv : L.bitvec_udivides n d = true)
    (hd : L.Nonzero (B.node (L.BitVecK d) (L.TBitVector w))) :
    L.Nonzero (B.node (L.BitVecK (Prim.lit_udiv w d n % 2 ^ w)) (L.TBitVector w)) := by
  rw [L.bitvec_udivides_eq, Sem.divisible_eq] at hdv
  simp only [Prim.divisible, decide_eq_true_eq] at hdv
  have hm : n % 2 ^ w = n := Int.emod_eq_of_lt h0n h1n
  have e : Prim.lit_udiv (w : Int) d n % 2 ^ w = d / n := by
    simp only [Prim.lit_udiv, Prim.masked, Int.toNat_natCast, hm, hn, ite_false, Int.emod_emod,
      Prim.tdiv]
    rw [Int.tdiv_eq_ediv_of_nonneg h0d]
    exact Int.emod_eq_of_lt (Int.ediv_nonneg h0d h0n)
      (Int.lt_of_le_of_lt (Int.ediv_le_self _ h0d) h1d)
  rw [e]
  by_cases hd0 : d = 0
  · subst hd0; simpa using hd
  · obtain ⟨q, rfl⟩ := hdv
    have hq : 0 < q := by
      rcases Int.lt_trichotomy q 0 with h | h | h
      · have := Int.mul_neg_of_pos_of_neg (show 0 < n by omega) h; omega
      · subst h; simp at hd0
      · exact h
    rw [Int.mul_ediv_cancel_left _ hn]
    refine nonzero_lit hq ?_
    have : 1 * q ≤ n * q := Int.mul_le_mul_of_nonneg_right (by omega) (by omega)
    simp only [Sem.size_of_ty_TBitVector, Int.toNat_natCast]; omega


/-! ## Extensions and powers of two -/

/-- The most significant bit of a literal. -/
theorem msb_of_lit {z : Int} {t : S.Ty} (h0 : 0 ≤ z) :
    L.bitvec_msb_of (B.node (L.BitVecK z) t) =
      if 0 < z then log2 z else L.bitvec_size_of_ty t - 1 := by
  rw [L.bitvec_msb_of_eq, Syntax.asBitVec_node]
  by_cases h : 0 < z
  · simp [Kanon.firstSome, h, Sem.log2_eq, HOrElse.hOrElse, OrElse.orElse, Option.orElse]
  · obtain rfl : z = 0 := by omega
    simp [Kanon.firstSome, HOrElse.hOrElse, OrElse.orElse, Option.orElse, Syntax.bitvec_size_eq,
      Kanon.Base.ty_node]

/-- The literal `z`, of a sort of `W = w + b` bits, whose most significant bit is below `w`,
at `w` bits: it is nonzero (if `z` is zero, `b` is zero and it is the same literal). -/
theorem nonzero_masked_zext {z b : Int} {w W : Nat} (hW : (W : Int) = w + b) (hb : 0 ≤ b)
    (h0 : 0 ≤ z) (hmsb : L.bitvec_msb_of (B.node (L.BitVecK z) (L.TBitVector W)) < w)
    (hz : L.Nonzero (B.node (L.BitVecK z) (L.TBitVector W))) :
    L.Nonzero (B.node (L.BitVecK (z % 2 ^ w)) (L.TBitVector w)) := by
  rw [msb_of_lit h0, Sem.size_of_ty_TBitVector] at hmsb
  by_cases hp : 0 < z
  · simp only [hp, ite_true] at hmsb
    have hlt := lt_two_pow_log2 hp hmsb
    simp only [Int.toNat_natCast] at hlt
    rw [Int.emod_eq_of_lt h0 hlt]
    exact nonzero_lit hp (by simpa [Sem.size_of_ty_TBitVector] using hlt)
  · obtain rfl : z = 0 := by omega
    simp only [Int.lt_irrefl, ite_false] at hmsb
    obtain rfl : W = w := by omega
    simpa using hz

theorem zext_div_ok {m n : Nat} (hmn : m ≤ n) (x : BitVec m) (k : BitVec n)
    (hk : 0 < k.toNat ∧ k.toNat < 2 ^ m ∨ m = n) :
    (x.setWidth n).smtUDiv k = (x.smtUDiv (k.setWidth m)).setWidth n := by
  rcases hk with ⟨hk0, hk⟩ | rfl
  · have := x.isLt
    have hp : 2 ^ m ≤ 2 ^ n := Nat.pow_le_pow_right (by omega) hmn
    have hkm : (k.setWidth m).toNat = k.toNat := by
      rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt hk]
    apply BitVec.eq_of_toNat_eq
    rw [smtUDiv_toNat (by omega), BitVec.toNat_setWidth, BitVec.toNat_setWidth,
      smtUDiv_toNat (by omega), hkm, Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by have := Nat.div_le_self x.toNat k.toNat; omega)]
  · simp

/-- A power of two above one, below `2 ^ w`. -/
theorem pow2_facts {r : Int} {w : Nat} (hp : L.bitvec_is_pow2 r = true) (h1 : 1 < r)
    (h2 : r < 2 ^ w) : ∃ j : Nat, r = 2 ^ j ∧ log2 r = j ∧ 1 ≤ j ∧ j < w := by
  obtain ⟨j, rfl⟩ := is_pow2_exists hp
  refine ⟨j, rfl, log2_two_pow j, ?_, ?_⟩
  · rcases j with _ | j
    · simp at h1
    · omega
  · have : 2 ^ j < 2 ^ w := by exact_mod_cast h2
    exact (Nat.pow_lt_pow_iff_right (by omega)).1 this

/-- The remainder by a power of two keeps the low bits. -/
theorem rem_pow2_bv {n m : Nat} (w k : BitVec n) (hp : L.bitvec_is_pow2 (k.toNat : Int) = true)
    (h1 : 1 < (k.toNat : Int)) (hm : m = (log2 (k.toNat : Int) - 1 - 0 + 1).toNat) :
    BitVec.setWidth n (BitVec.extractLsb' 0 m w) = w % k := by
  have hk := k.isLt
  obtain ⟨j, hj, hl, hj1, hjn⟩ := pow2_facts (L := L) (w := n) hp h1 (by exact_mod_cast hk)
  rw [hl] at hm
  have hmj : m = j := by omega
  subst hmj
  have hkj : k.toNat = 2 ^ m := by exact_mod_cast hj
  have hp' : 2 ^ m ≤ 2 ^ n := Nat.pow_le_pow_right (by omega) (by omega)
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.extractLsb'_toNat, BitVec.toNat_umod, hkj,
    Nat.shiftRight_zero, Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos _)) hp')]


/-! ## Significant bits -/

/-- A multiplication of values of few significant bits does not overflow. -/
theorem Refines.mulOvf_msb {s : Bool} {v1 v2 : S.Term} {t : S.Ty}
    (h : s = true ∧ L.bitvec_msb_of v1 + L.bitvec_msb_of v2 < L.bitvec_size v1 - 2 ∨
      s = false ∧ L.bitvec_msb_of v1 + L.bitvec_msb_of v2 < L.bitvec_size v1 - 1) :
    S.Refines (B.node (L.MulOvfK s v1 v2) t) LBool.bool_v_false := by
  replace h : if s then L.bitvec_msb_of v1 + L.bitvec_msb_of v2 < L.bitvec_size v1 - 2
      else L.bitvec_msb_of v1 + L.bitvec_msb_of v2 < L.bitvec_size v1 - 1 := by
    cases s <;> simpa using h
  refine Refines.denB (L := L) (fun w => ?_) (fun w => ?_) (fun w ρ b e => ?_)
  · rw [Kanon.Base.ty_node]; exact ((L.WT_MulOvf _ _ _ _).1 w).1.2.2
  · rw [KanonBool.Sem.v_false_eq, KanonBool.Syntax.WT_Bool, Kanon.Base.ty_node, Kanon.Base.ty_node,
      ((L.WT_MulOvf _ _ _ _).1 w).1.2.2]
    simp
  obtain ⟨⟨⟨m, hm, h1⟩, h2, -⟩, w1, w2⟩ := (L.WT_MulOvf _ _ _ _).1 w
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le (Int.le_of_lt hm)
  have hn : 0 < n := by omega
  rw [h1] at h2
  rw [Sem.denB_MulOvf, h1, Syntax.asTBitVector_sort] at e
  simp only [Int.toNat_natCast, if_pos hm] at e
  cases e1 : Sem.den L ρ n v1 <;> cases e2 : Sem.den L ρ n v2 <;> rw [e1, e2] at e <;>
    simp only [binB_some, binB_none_l, binB_none_r, reduceCtorEq, Option.some.injEq] at e
  rename_i x y
  have bx := Sem.den_msb ρ v1 n x w1 h1 e1
  have by' := Sem.den_msb ρ v2 n y w2 h2 e2
  simp only [Syntax.bitvec_size_eq, h1, Sem.size_of_ty_TBitVector] at h
  subst e
  rw [KanonBool.Sem.v_false_eq, Sem.denB_Bool, Option.some.injEq]
  by_cases hx : x.toNat = 0
  · have : x = 0#n := BitVec.eq_of_toNat_eq (by simp [hx])
    subst this
    have : (0 : Int) < 2 ^ (n - 1) := Int.pow_pos (by decide)
    cases s <;> simp [BitVec.umulOverflow, BitVec.smulOverflow] <;> omega
  by_cases hy : y.toNat = 0
  · have : y = 0#n := BitVec.eq_of_toNat_eq (by simp [hy])
    subst this
    have : (0 : Int) < 2 ^ (n - 1) := Int.pow_pos (by decide)
    cases s <;> simp [BitVec.umulOverflow, BitVec.smulOverflow] <;> omega
  have ha : 0 ≤ L.bitvec_msb_of v1 := by
    apply Int.not_lt.1; intro hc
    have : (L.bitvec_msb_of v1 + 1).toNat = 0 := by omega
    rw [this] at bx; omega
  have hb : 0 ≤ L.bitvec_msb_of v2 := by
    apply Int.not_lt.1; intro hc
    have : (L.bitvec_msb_of v2 + 1).toNat = 0 := by omega
    rw [this] at by'; omega
  have hp : x.toNat * y.toNat <
      2 ^ ((L.bitvec_msb_of v1 + 1).toNat + (L.bitvec_msb_of v2 + 1).toNat) := by
    rw [Nat.pow_add]; exact Nat.mul_lt_mul'' bx by'
  cases s
  · simp only [Bool.false_eq_true, ite_false] at h ⊢
    rw [eq_comm, umul_ok]
    exact Nat.lt_of_lt_of_le hp (Nat.pow_le_pow_right (by omega) (by omega))
  · simp only [ite_true] at h ⊢
    have lx : 2 * x.toNat < 2 ^ n := by
      have := Nat.pow_le_pow_right (n := 2) (by omega)
        (show (L.bitvec_msb_of v1 + 1).toNat + 1 ≤ n by omega)
      rw [Nat.pow_succ] at this; omega
    have ly : 2 * y.toNat < 2 ^ n := by
      have := Nat.pow_le_pow_right (n := 2) (by omega)
        (show (L.bitvec_msb_of v2 + 1).toNat + 1 ≤ n by omega)
      rw [Nat.pow_succ] at this; omega
    have hq := Nat.lt_of_lt_of_le hp (Nat.pow_le_pow_right (n := 2) (by omega)
      (show (L.bitvec_msb_of v1 + 1).toNat + (L.bitvec_msb_of v2 + 1).toNat ≤ n - 1 by omega))
    rw [eq_comm, smul_ok, BitVec.toInt_eq_toNat_of_lt lx, BitVec.toInt_eq_toNat_of_lt ly]
    have : ((2 ^ (n - 1) : Nat) : Int) = (2 : Int) ^ (n - 1) := by push_cast; rfl
    have : ((x.toNat * y.toNat : Nat) : Int) < 2 ^ (n - 1) := by omega
    push_cast at this
    constructor
    · have := Int.mul_nonneg (Int.natCast_nonneg x.toNat) (Int.natCast_nonneg y.toNat)
      have : (0 : Int) < 2 ^ (n - 1) := Int.pow_pos (by decide); omega
    · exact this

end


/-! ## Tactics -/



theorem ssubOverflow_zero_left {n : Nat} (hn : 0 < n) (x : BitVec n) :
    (0#n).ssubOverflow x = decide (x = BitVec.intMin n) := by
  have := BitVec.le_toInt x; have := BitVec.toInt_lt (x := x)
  rw [Bool.eq_iff_iff]
  simp [BitVec.ssubOverflow, ← BitVec.toInt_inj, BitVec.toInt_intMin_of_pos hn]; omega



/-! ## Lifting with subsort side conditions

`kanon_lift_body` (Kanon's) computes the head of the side conditions (`L.Nonzero v`) of the
lifting lemmas outside of their goal's context, which fails (`unknown free variable`) when
the predicate is a field of the interface; `bveq_lift_body` is the same, in the goal's
context. -/

open Lean Meta Elab Tactic in
/-- `Kanon.Proof.liftGoal`, in the context of the goal. -/
partial def liftGoal : TacticM (List MVarId) := do
  let g ← getMainGoal
  let ty ← g.withContext do whnfR (← instantiateMVars (← g.getType))
  unless ty.isAppOfArity ``Kanon.Sem.Refines 3 do return [g]
  let ls ← g.withContext do Kanon.Proof.liftLemmas (ty.getArg! 2)
  for l in ls do
    let s ← saveState
    try
      evalTactic (← `(tactic| apply $(mkCIdent l) (by assumption)))
    catch _ =>
      s.restore
      continue
    let mut out := []
    for g' in ← getGoals do
      unless ← g'.isAssigned do
        setGoals [g']
        out := out ++ (← liftGoal)
    return out
  unless ls.isEmpty do
    throwError "bveq_lift: none of the lifting lemmas {ls} applies to{indentExpr ty}"
  evalTactic (← `(tactic| exact Kanon.Sem.Refines.refl))
  return []

open Lean Meta Elab Tactic in
/-- `kanon_lift_body`, with `liftGoal` in the context of the goal. -/
elab "bveq_lift_body" : tactic => do
  let lift : TacticM (List MVarId × List MVarId) := do
    evalTactic (← `(tactic| apply Kanon.Sem.Refines.of_lift))
    let gs ← getGoals
    let some hl ← gs.findM? fun g => return match (← g.getTag) with
        | .str _ "hl" => true
        | _ => false
      | throwError "bveq_lift_body: no goal"
    setGoals [hl]
    let side ← liftGoal
    let rest ← gs.filterM fun g => return g != hl && !(← g.isAssigned)
    return (rest, side)
  let s ← saveState
  let (rest, side) ← lift
  if side.isEmpty then setGoals rest
  else
    s.restore
    evalTactic (← `(tactic| refine Kanon.Sem.Refines.of_WT (fun $(mkIdent `kw) => ?_)))
    let (rest, side) ← lift
    setGoals (rest ++ side)

open Lean Meta Elab Tactic in
/-- `kanon_on_refines`, in the context of the goal. -/
elab "bveq_on_refines " tac:tactic : tactic => withMainContext do
  let ty ← whnfR (← instantiateMVars (← getMainTarget))
  if ty.isAppOfArity ``Kanon.Sem.Refines 3 then evalTactic tac

set_option hygiene false in
/-- The facts that the typing of the spec (`kw`) gives, with natural widths. -/
macro "bveq_side_facts" : tactic => `(tactic| (
  have w1 := kw
  simp only [bv_wt, bv_lits, true_and, and_true] at w1
  kanon_split
  subst_vars
  (try simp only [bv_wt, bv_lits, true_and, and_true] at *)
  (try bv_nat_widths)
  (try bv_rw_tys)
  (try simp only [BitvecMod.Lib.TBitVector_inj_iff, Int.natCast_inj, Sem.size_of_ty_TBitVector,
    Int.toNat_natCast] at *)
  (try subst_vars)))

set_option hygiene false in
/-- Closes the side conditions `L.Nonzero v` of the lifting (`kw`: the spec is well-typed). -/
macro "bveq_nonzero" : tactic => `(tactic| first
  | assumption
  | (bveq_side_facts
     first
       | exact BitvecMod.Lib.BvEq.nonzero_lit_mul (by omega) ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›
       | exact BitvecMod.Lib.BvEq.nonzero_lit_udiv (by omega) ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›)
  | (refine BitvecMod.Lib.BvEq.nonzero_lit (by omega) ?_
     have w1 := kw
     simp only [bv_wt, bv_lits, true_and, and_true] at w1
     kanon_split
     subst_vars
     (try simp only [bv_wt, bv_lits, true_and, and_true] at *)
     first | assumption | omega))

/-- `kanon_rule_lift`, with `bveq_lift_body`, and `bveq_nonzero` on the side conditions. -/
macro "bveq_rule_lift" : tactic => `(tactic| (
  intro _
  intros
  (try kanon_guards)
  (try kanon_split)
  (try subst_vars)
  (try simp only [kanon_spec, kanon_body])
  (repeat' split)
  all_goals (try bveq_lift_body)
  all_goals (try simp only [kanon_spec, kanon_body])
  all_goals (try first
    | kanon_refl
    | (kanon_comm; done)
    | kanon_rule_close
    | kanon_close_lemmas)
  all_goals (try bveq_nonzero)))

/-- `bv_facts`, keeping the sort hypotheses. -/
macro "bveq_facts" : tactic => `(tactic| (
  (try simp only [bv_wt, bv_lits, KanonBool.Sem.v_true_eq, KanonBool.Sem.v_false_eq,
    KanonBool.Syntax.bool_of_bool_eq, KanonBool.Syntax.WT_Bool, true_and, and_true] at *)
  (try kanon_split)
  (try subst_vars)
  (try bv_rw_tys)
  (try simp only [bv_wt, bv_lits, true_and, and_true] at *)
  (try kanon_split)
  (try subst_vars)))

macro "bveq_wt" : tactic => `(tactic| (
  intro w
  bveq_facts
  (try bv_nat_widths)
  (try simp_all [bv_range, BitvecMod.Lib.BvEq.emod_two_pow_nonneg,
    BitvecMod.Lib.BvEq.emod_two_pow_lt, BitvecMod.Lib.BvEq.lit_udiv_nonneg,
    BitvecMod.Lib.BvEq.lit_udiv_lt, BitvecMod.Lib.BvEq.lit_sdiv_nonneg,
    BitvecMod.Lib.BvEq.lit_sdiv_lt, BitvecMod.Lib.BvEq.lit_urem_nonneg,
    BitvecMod.Lib.BvEq.lit_urem_lt, BitvecMod.Lib.BvEq.lit_srem_nonneg,
    BitvecMod.Lib.BvEq.lit_srem_lt, BitvecMod.Lib.BvEq.lit_smod_nonneg,
    BitvecMod.Lib.BvEq.lit_smod_lt])
  all_goals first | done | grind))

set_option hygiene false in
/-- The value half of `Refines.den` or `Refines.denB`, reduced to the values of the atoms, with
natural widths and the values of the literals opaque (the closing lemmas are stated on them). -/
macro "bveq_sem_core" : tactic => `(tactic| (
  first
    | refine fun n w ht ρ (x : BitVec n) e => ?_
    | refine fun w ρ (x : Bool) e => ?_
  bveq_facts
  (try bv_nat_widths)
  (try simp only [Int.toNat_natCast, Int.natCast_pos] at *)
  (try simp only [bv_den, bv_lits, KanonBool.Sem.v_true_eq, KanonBool.Sem.v_false_eq,
    KanonBool.Syntax.bool_of_bool_eq] at e ⊢)
  (try bv_rw_tys)
  (try simp only [Syntax.asTBitVector_sort, Int.toNat_natCast,
    BitvecMod.Lib.BvEq.ofInt_emod_two_pow] at e ⊢)
  (try simp (disch := first | assumption | omega) only [if_pos, Int.natCast_pos,
    BitvecMod.Lib.BvEq.lit_add_overflows_ofInt, BitvecMod.Lib.BvEq.lit_sub_overflows_ofInt,
    BitvecMod.Lib.BvEq.lit_mul_overflows_ofInt, BitvecMod.Lib.BvEq.to_z_ofInt,
    BitvecMod.Lib.BvEq.max_for_false, BitvecMod.Lib.BvEq.min_for_false,
    BitvecMod.Lib.BvEq.ofInt_lit_udiv, BitvecMod.Lib.BvEq.ofInt_lit_urem,
    BitvecMod.Lib.BvEq.ofInt_lit_sdiv, BitvecMod.Lib.BvEq.ofInt_lit_srem,
    BitvecMod.Lib.BvEq.ofInt_lit_smod, BitvecMod.Lib.BvEq.overflows_add_ofInt,
    BitvecMod.Lib.BvEq.overflows_sub_ofInt, BitvecMod.Lib.BvEq.overflows_mul_ofInt,
    BitvecMod.Lib.BvEq.is_int_min_ofInt] at *)
  bv_lit_ops
  (try simp only [← BitVec.toInt_ofInt, BitvecMod.Lib.BvEq.natCast_toNat_ofInt,
    BitvecMod.Lib.BvEq.toNat_emod_eq, BitVec.ofInt_emod_two_pow] at *)
  bveq_gen_lits
  (try simp only [BitVec.ofInt_natCast, BitVec.ofNat_toNat] at *)
  bveq_fix_widths
  (try simp only [Int.natCast_inj, Int.natCast_pos, BitVec.toNat_inj] at *)
  (try subst_vars)
  run_tac Kanon.Proof.caseAllAtoms (some #[``BitvecMod.Lib.den_cases, ``BitvecMod.Lib.denB_cases])
  all_goals bveq_bool_vars
  all_goals (try simp_all [Syntax.bitvec_unchecked_eq, Syntax.bitvec_checked_signed_eq,
    Syntax.bitvec_checked_unsigned_eq, Syntax.bitvec_checked_meet_eq,
    BitvecMod.Lib.BvEq.max_for_false, BitvecMod.Lib.BvEq.min_for_false,
    BitvecMod.Lib.BvEq.smtUDiv_one, BitvecMod.Lib.BvEq.smtSDiv_one, Syntax.bitvec_udivides_eq,
    Sem.divisible_eq, Prim.divisible, decide_eq_true_eq, Int.natCast_dvd_natCast])
  all_goals (try simp (disch := omega) only [BitvecMod.Lib.BvEq.max_for_true,
    BitvecMod.Lib.BvEq.min_for_true] at *)
  all_goals (try (repeat' split at e))
  all_goals (try simp_all [BitvecMod.Lib.BvEq.ssubOverflow_zero_left])
  all_goals (try (repeat' apply And.intro))))

open BitvecMod.Lib.BvEq in
/-- Proves overflow facts: splits the flags, and reasons on integers. -/
macro "bveq_ovf" : tactic => `(tactic| (
  bveq_bools
  all_goals (try simp_all)
  all_goals (repeat' (first | apply And.intro | intro))
  all_goals kanon_split
  all_goals bveq_ovf_eqs
  all_goals (try simp only [BitvecMod.Lib.BvEq.sadd_ok, BitvecMod.Lib.BvEq.ssub_ok,
    BitvecMod.Lib.BvEq.smul_ok, BitvecMod.Lib.BvEq.uadd_ok, BitvecMod.Lib.BvEq.usub_ok,
    BitvecMod.Lib.BvEq.umul_ok] at *)
  all_goals kanon_split
  all_goals bveq_bounds
  all_goals (try push_cast at *)
  all_goals (try simp only [Int.natCast_pow, Int.natCast_ofNat] at *)
  all_goals omega))

/-- The value half: `bveq_sem_core`, then the closing lemmas of the rules. -/
macro "bveq_sem" : tactic => `(tactic| (
  bveq_sem_core
  all_goals (first
    | (bveq_decide_small; done)
    | (simp_all [one_uadd_one, one_sadd_one]; done)
    | (simp_all [iv, sadd_pos, sadd_nonpos, uadd_not, usub_self, ssub_self, uadd_zero, sadd_zero,
        umul_udiv, one_uadd, one_sadd]; done)
    | (simp_all [iv, sadd_pos', sadd_nonpos', uadd_not', uadd_zero', sadd_zero', umul_udiv', one_uadd',
        one_sadd']; done)
    | (simp_all [iv, umul_small, smul_small, smul_const_pos, smul_const_neg, smul_const_neg_one,
        umul_const_rule]; done)
    | (simp_all [iv, umul_small', smul_small', smul_const_pos', smul_const_neg', smul_const_neg_one',
        umul_const_rule']; done)
    | (simp_all [umod_add_self, umod_add_self']; done)
    | (simp_all [umod_umod_of_le, umod_umod_of_lt, umod_umod_of_le_ofNat, umod_umod_of_lt_ofNat]; done)
    | (simp_all [ne_and_of_mask', and_not_self_toNat]; done)
    | (simp_all [BitVec.mul_comm, smul_neg_ok]; done)
    | (kanon_split; subst_vars; ac_rfl)
    | (first
         | (rw [(ovf_comm _ _).1]; assumption)
         | (rw [(ovf_comm _ _).2.1]; assumption)
         | (rw [(ovf_comm _ _).2.2.1]; assumption)
         | (rw [(ovf_comm _ _).2.2.2]; assumption))
    | (intro _
       kanon_split
       first
         | (rw [(ovf_comm _ _).1]; simp_all; done)
         | (rw [(ovf_comm _ _).2.1]; simp_all; done)
         | (rw [(ovf_comm _ _).2.2.1]; simp_all; done)
         | (rw [(ovf_comm _ _).2.2.2]; simp_all; done))
    | (intro _ _
       (try simp_all)
       kanon_split
       first
         | exact umul_swap_ok ‹_› ‹_›
         | exact smul_swap_ok ‹_› ‹_› ‹_›
         | exact umul_swap_ok' ‹_› ‹_›
         | exact smul_swap_ok' ‹_› ‹_› ‹_›)
    | (simp_all [append_inj]; done)
    | ((try subst_vars)
       (try kanon_split)
       first
         | exact (mul_div_ok ‹_› ‹_› ‹_›).1
         | exact (mul_div_ok ‹_› ‹_› ‹_›).2
         | exact (mul_div_ok' ‹_› ‹_› ‹_›).1
         | exact (mul_div_ok' ‹_› ‹_› ‹_›).2
         | exact div_mul_ok ‹_› ‹_› ‹_›
         | exact div_mul_ok' ‹_› ‹_› ‹_›
         | exact div_div_ok ‹_› ‹_›
         | exact (div_div_ok ‹_› ‹_›).symm)
    | (simp_all [BitVec.usubOverflow, BitVec.ult]; done)
    | (simp_all [toNat_eq_zero_iff, natCast_toNat_eq_one]; done)
    | (simp only [BitVec.ult, BitVec.ule, BitVec.slt, BitVec.sle, decide_eq_true_eq,
        decide_eq_false_iff_not, Bool.not_eq_true, Bool.not_eq_false] at *; omega)
    | (grind [BitVec.neg_eq_not_add]; done)
    | (bveq_ovf; done)
    | skip)))

/-- Proves an arm of a boolean function of the module (or of `Bool.eq`), as far as it can. -/
macro "bveq_rule" : tactic => `(tactic| (
  bveq_rule_lift
  all_goals bveq_on_refines bv_apply_den
  all_goals first
    | (bveq_wt; done)
    | bveq_sem
    | skip))

end BitvecMod.Lib.BvEq

namespace BitvecMod

attribute [kanon_tactic "bveq_rule"] Bitvec.add_overflows.spec Bitvec.sub_overflows.spec
  Bitvec.mul_overflows.spec Bitvec.div.spec Bitvec.rem.spec Bitvec.mod_.spec

end BitvecMod
