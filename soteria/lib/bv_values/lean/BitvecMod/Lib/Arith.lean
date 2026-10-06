import BitvecMod.Lib.Tactic

/-!
# Arithmetic, bitwise operations and shifts

The lemmas and tactics of the arms of `Bitvec.add`, `sub`, `mul`, `neg`, `and_`, `or_`, `xor`, `shl`, `lshr`,
`ashr`, `not_bool`, `of_bool`, `to_bool`, over the interface: the
counterparts of the language's `Kanon/Lib/LitOps.lean`, `Bitwise.lean` and `Arith.lean`.

- the typing of the booleans that the rules build (`bool_of_bool_node`) and the
  bounds of the powers of two;
- the helpers of the rules on literals in range (`fold_checked`, `is_ones`,
  `bits_in`, …) as operations on their values;
- facts on overflows, through integers (`bv_arith_ovf`), on masks and shifts;
- `bv_arith`, the tactic of the arms of these functions: `bv_rule`'s steps, with
  the value goals closed by the lemmas above (`bv_arith_close`).
-/

namespace BitvecMod

open Classical Kanon Kanon.Sem

set_option linter.unusedSectionVars false

namespace Lib

variable {S : Kanon.Sem} [DecidableEq S.Term] [DecidableEq S.Ty] {B : Kanon.Base S}
  {LBool : KanonBool.Syntax B} {LCore : CoreMod.Syntax B} {L : Syntax B LBool LCore}
  [KanonBool.Sem LBool] [CoreMod.Sem LCore] [Sem L]

/-! ## Typing -/

theorem arith_bool_of_bool_node (b : Bool) :
    LBool.bool_of_bool b = B.node (LBool.BoolK b) LBool.TBool := by
  rw [LBool.bool_of_bool_eq]
  cases b
  · exact KanonBool.Sem.v_false_eq
  · exact KanonBool.Sem.v_true_eq

@[simp] theorem arith_two_pow_pos (n : Nat) : (0 : Int) < 2 ^ n := Int.pow_pos (by decide)

@[simp] theorem arith_one_lt_two_pow {k : Nat} : (1 : Int) < 2 ^ k ↔ 0 < k := by
  norm_cast; exact Nat.one_lt_two_pow_iff.trans Nat.pos_iff_ne_zero.symm

@[simp] theorem arith_exists_concat_width {a b : Int} {P : Int → Int → Prop} :
    (∃ n, 0 < n ∧ ∃ m, 0 < m ∧ a = n ∧ b = m ∧ P n m) ↔ 0 < a ∧ 0 < b ∧ P a b :=
  ⟨fun ⟨_, h0, _, h1, e1, e2, h⟩ => by subst e1 e2; exact ⟨h0, h1, h⟩,
    fun ⟨h0, h1, h⟩ => ⟨_, h0, _, h1, rfl, rfl, h⟩⟩

@[simp] theorem arith_exists_extend_width {a : Int} {P : Int → Prop} :
    (∃ n, 0 < n ∧ a = n ∧ P n) ↔ 0 < a ∧ P a :=
  ⟨fun ⟨_, h0, e, h⟩ => by subst e; exact ⟨h0, h⟩, fun ⟨h0, h⟩ => ⟨_, h0, rfl, h⟩⟩

attribute [bv_range] arith_exists_concat_width arith_exists_extend_width

attribute [bv_lits] arith_bool_of_bool_node
attribute [bv_range] arith_two_pow_pos arith_one_lt_two_pow

/-! ## Overflows -/

section
variable {n : Nat} (x y : BitVec n)

theorem arith_saddOverflow_comm : x.saddOverflow y = y.saddOverflow x := by
  simp [BitVec.saddOverflow, Int.add_comm]
theorem arith_uaddOverflow_comm : x.uaddOverflow y = y.uaddOverflow x := by
  simp [BitVec.uaddOverflow, Nat.add_comm]
theorem arith_smulOverflow_comm : x.smulOverflow y = y.smulOverflow x := by
  simp [BitVec.smulOverflow, Int.mul_comm]
theorem arith_umulOverflow_comm : x.umulOverflow y = y.umulOverflow x := by
  simp [BitVec.umulOverflow, Nat.mul_comm]

theorem arith_ssubOverflow_zero_left (hn : 0 < n) :
    (0#n).ssubOverflow x = decide (x = BitVec.intMin n) := by
  have := BitVec.le_toInt x; have := BitVec.toInt_lt (x := x)
  rw [Bool.eq_iff_iff]
  simp [BitVec.ssubOverflow, ← BitVec.toInt_inj, BitVec.toInt_intMin_of_pos hn]; omega

end

/-! ## The helpers of the rules on literals in range -/

theorem arith_emod_two_pow_nonneg (z : Int) (w : Nat) : 0 ≤ z % 2 ^ w :=
  Int.emod_nonneg _ (Int.ne_of_gt (Int.pow_pos (by decide)))

theorem arith_emod_two_pow_lt (z : Int) (w : Nat) : z % 2 ^ w < 2 ^ w :=
  Int.emod_lt_of_pos _ (Int.pow_pos (by decide))

theorem arith_ofInt_emod_two_pow {n : Nat} (z : Int) : BitVec.ofInt n (z % 2 ^ n) = BitVec.ofInt n z := by
  simpa [Prim.masked] using ofInt_masked (w := (n : Int)) rfl z

theorem arith_emod_two_pow_of_lt {z : Int} {n : Nat} (h0 : 0 ≤ z) (h1 : z < 2 ^ n) : z % 2 ^ n = z :=
  Int.emod_eq_of_lt h0 h1

attribute [bv_range] arith_emod_two_pow_nonneg arith_emod_two_pow_lt
attribute [bv_ofInt] arith_ofInt_emod_two_pow

theorem arith_z_lsl_one (k : Int) : Prim.z_lsl 1 k = 2 ^ k.toNat := by
  simp [Prim.z_lsl]

theorem arith_to_z_true {n : Nat} (hn : 0 < n) (z : Int) :
    L.bitvec_to_z true n z = (BitVec.ofInt n z).toInt := by
  rw [L.bitvec_to_z_eq]; simp only [↓reduceIte, Sem.signed_extract_eq]
  exact sext_of_eq hn z

theorem arith_to_z_false (n z : Int) : L.bitvec_to_z false n z = z := by
  rw [L.bitvec_to_z_eq]; rfl

theorem arith_min_for_true {n : Nat} (hn : 0 < n) : L.bitvec_min_for true n = -2 ^ (n - 1) := by
  rw [L.bitvec_min_for_eq]; simp only [↓reduceIte, Sem.z_lsl_eq, arith_z_lsl_one]
  congr 2; omega

theorem arith_max_for_true {n : Nat} (hn : 0 < n) : L.bitvec_max_for true n = 2 ^ (n - 1) - 1 := by
  rw [L.bitvec_max_for_eq]; simp only [↓reduceIte, Sem.z_lsl_eq, arith_z_lsl_one]
  congr 2; omega

theorem arith_min_for_false (n : Int) : L.bitvec_min_for false n = 0 := by
  rw [L.bitvec_min_for_eq]; rfl

theorem arith_max_for_false (n : Nat) : L.bitvec_max_for false n = 2 ^ n - 1 := by
  rw [L.bitvec_max_for_eq]; simp only [Bool.false_eq_true, ↓reduceIte, Sem.z_lsl_eq, arith_z_lsl_one]
  simp

section
variable {n : Nat} (hn : 0 < n)
include hn

theorem arith_overflows_add_ofInt (s : Bool) {l r : Int} (hl0 : 0 ≤ l) (hl1 : l < 2 ^ n)
    (hr0 : 0 ≤ r) (hr1 : r < 2 ^ n) :
    L.bitvec_overflows_add s n l r =
      if s then (BitVec.ofInt n l).saddOverflow (BitVec.ofInt n r)
      else (BitVec.ofInt n l).uaddOverflow (BitVec.ofInt n r) := by
  rw [L.bitvec_overflows_add_eq]
  cases s
  · simp only [arith_to_z_false, arith_min_for_false, arith_max_for_false, BitVec.uaddOverflow,
      BitVec.toNat_ofInt, Bool.false_eq_true, ↓reduceIte]
    have e : ((2 ^ n : Nat) : Int) = (2 : Int) ^ n := by push_cast; rfl
    rw [Bool.eq_iff_iff]; simp [e, Int.emod_eq_of_lt hl0 hl1, Int.emod_eq_of_lt hr0 hr1]
    omega
  · have := BitVec.le_toInt (BitVec.ofInt n l); have := BitVec.toInt_lt (x := BitVec.ofInt n l)
    simp only [arith_to_z_true hn, arith_min_for_true hn, arith_max_for_true hn,
      BitVec.saddOverflow, ↓reduceIte]
    rw [Bool.eq_iff_iff]; simp; omega

theorem arith_overflows_sub_ofInt (s : Bool) {l r : Int} (hl0 : 0 ≤ l) (hl1 : l < 2 ^ n)
    (hr0 : 0 ≤ r) (hr1 : r < 2 ^ n) :
    L.bitvec_overflows_sub s n l r =
      if s then (BitVec.ofInt n l).ssubOverflow (BitVec.ofInt n r)
      else (BitVec.ofInt n l).usubOverflow (BitVec.ofInt n r) := by
  rw [L.bitvec_overflows_sub_eq]
  cases s
  · simp only [arith_to_z_false, arith_min_for_false, arith_max_for_false, BitVec.usubOverflow,
      BitVec.toNat_ofInt, Bool.false_eq_true, ↓reduceIte]
    have e : ((2 ^ n : Nat) : Int) = (2 : Int) ^ n := by push_cast; rfl
    rw [Bool.eq_iff_iff]; simp [e, Int.emod_eq_of_lt hl0 hl1, Int.emod_eq_of_lt hr0 hr1]
    omega
  · have := BitVec.le_toInt (BitVec.ofInt n l); have := BitVec.toInt_lt (x := BitVec.ofInt n l)
    simp only [arith_to_z_true hn, arith_min_for_true hn, arith_max_for_true hn,
      BitVec.ssubOverflow, ↓reduceIte]
    rw [Bool.eq_iff_iff]; simp; omega

theorem arith_overflows_mul_ofInt (s : Bool) {l r : Int} (hl0 : 0 ≤ l) (hl1 : l < 2 ^ n)
    (hr0 : 0 ≤ r) (hr1 : r < 2 ^ n) :
    L.bitvec_overflows_mul s n l r =
      if s then (BitVec.ofInt n l).smulOverflow (BitVec.ofInt n r)
      else (BitVec.ofInt n l).umulOverflow (BitVec.ofInt n r) := by
  rw [L.bitvec_overflows_mul_eq]
  cases s
  · obtain ⟨l, rfl⟩ := Int.eq_ofNat_of_zero_le hl0
    obtain ⟨r, rfl⟩ := Int.eq_ofNat_of_zero_le hr0
    have e : ((2 ^ n : Nat) : Int) = (2 : Int) ^ n := by push_cast; rfl
    simp only [arith_to_z_false, arith_min_for_false, arith_max_for_false, BitVec.umulOverflow,
      BitVec.toNat_ofInt, Bool.false_eq_true, ↓reduceIte, e,
      Int.emod_eq_of_lt (Int.natCast_nonneg l) hl1, Int.emod_eq_of_lt (Int.natCast_nonneg r) hr1,
      Int.toNat_natCast]
    rw [Bool.eq_iff_iff]
    simp only [Bool.or_eq_true, decide_eq_true_eq]
    have : (0 : Int) ≤ l * r := Int.mul_nonneg (Int.natCast_nonneg l) (Int.natCast_nonneg r)
    have e2 : ((l * r : Nat) : Int) = (l : Int) * r := by push_cast; rfl
    rw [← e2] at *
    omega
  · simp only [arith_to_z_true hn, arith_min_for_true hn, arith_max_for_true hn,
      BitVec.smulOverflow, ↓reduceIte]
    rw [Bool.eq_iff_iff]; simp; omega

theorem arith_is_int_min_ofInt (z : Int) :
    L.bitvec_is_int_min n z = decide (BitVec.ofInt n z = BitVec.intMin n) := by
  rw [L.bitvec_is_int_min_eq, arith_to_z_true hn, arith_min_for_true hn,
    ← BitVec.toInt_intMin_of_pos hn]
  simp only [BitVec.toInt_inj]

theorem arith_fold_checked_ofInt {a b : Int} (ha0 : 0 ≤ a) (ha1 : a < 2 ^ n) (hb0 : 0 ≤ b)
    (hb1 : b < 2 ^ n) (c : CoreMod.Checked) (add : Bool) :
    L.bitvec_fold_checked c n a b add =
      { signed := c.signed && !(if add then (BitVec.ofInt n a).saddOverflow (BitVec.ofInt n b)
          else (BitVec.ofInt n a).ssubOverflow (BitVec.ofInt n b)),
        unsigned := c.unsigned && !(if add then (BitVec.ofInt n a).uaddOverflow (BitVec.ofInt n b)
          else (BitVec.ofInt n a).usubOverflow (BitVec.ofInt n b)) } := by
  rw [L.bitvec_fold_checked_eq]
  cases add <;> simp [L.bitvec_checked_has_eq, arith_overflows_add_ofInt hn _ ha0 ha1 hb0 hb1,
    arith_overflows_sub_ofInt hn _ ha0 ha1 hb0 hb1]

end

attribute [bv_ofInt] arith_overflows_add_ofInt arith_overflows_sub_ofInt arith_overflows_mul_ofInt
  arith_is_int_min_ofInt arith_fold_checked_ofInt

/-! ## Bitwise helpers -/

theorem arith_ofInt_eq_ofInt_iff {n : Nat} {a b : Int} (ha0 : 0 ≤ a) (ha1 : a < 2 ^ n)
    (hb0 : 0 ≤ b) (hb1 : b < 2 ^ n) : BitVec.ofInt n a = BitVec.ofInt n b ↔ a = b := by
  constructor
  · intro h
    have := congrArg BitVec.toInt h
    have e : ((2 ^ n : Nat) : Int) = (2 : Int) ^ n := by push_cast; rfl
    have h2 := congrArg BitVec.toNat h
    simp only [BitVec.toNat_ofInt, e, Int.emod_eq_of_lt ha0 ha1, Int.emod_eq_of_lt hb0 hb1] at h2
    omega
  · rintro rfl; rfl

theorem arith_ofInt_eq_zero_iff {n : Nat} {a : Int} (ha0 : 0 ≤ a) (ha1 : a < 2 ^ n) :
    BitVec.ofInt n a = 0#n ↔ a = 0 := by
  have h := arith_ofInt_eq_ofInt_iff (n := n) ha0 ha1 (Int.le_refl 0) (Int.pow_pos (by decide))
  rw [← h]; rfl

theorem arith_zero_eq_ofInt_iff {n : Nat} {a : Int} (ha0 : 0 ≤ a) (ha1 : a < 2 ^ n) :
    0#n = BitVec.ofInt n a ↔ a = 0 := by
  rw [eq_comm, arith_ofInt_eq_zero_iff ha0 ha1]

theorem arith_ones_nat (n : Nat) : L.bitvec_ones (n : Int) = 2 ^ n - 1 := by
  rw [L.bitvec_ones_eq, Sem.z_lsl_eq, arith_z_lsl_one, Int.toNat_natCast]

theorem arith_ofInt_ones (n : Nat) : BitVec.ofInt n (L.bitvec_ones (n : Int)) = BitVec.allOnes n := by
  have e : ((2 ^ n - 1 : Nat) : Int) = 2 ^ n - 1 := by
    rw [Int.natCast_sub (Nat.one_le_two_pow)]; push_cast; rfl
  rw [arith_ones_nat (L := L), ← e, BitVec.ofInt_natCast]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, BitVec.toNat_allOnes, Nat.mod_eq_of_lt (Nat.sub_lt (Nat.two_pow_pos n) Nat.one_pos)]

theorem arith_is_ones_ofInt {n : Nat} {z : Int} (h0 : 0 ≤ z) (h1 : z < 2 ^ n) :
    L.bitvec_is_ones n z = decide (BitVec.ofInt n z = BitVec.allOnes n) := by
  have := arith_two_pow_pos n
  rw [L.bitvec_is_ones_eq, ← arith_ofInt_ones (L := L), decide_eq_decide,
    arith_ofInt_eq_ofInt_iff h0 h1 (by rw [arith_ones_nat]; omega)
      (by rw [arith_ones_nat]; omega)]

theorem arith_bits_in_ofInt {n : Nat} {a b : Int} (ha0 : 0 ≤ a) (ha1 : a < 2 ^ n) (hb0 : 0 ≤ b)
    (hb1 : b < 2 ^ n) :
    L.bitvec_bits_in a b = decide (BitVec.ofInt n a &&& BitVec.ofInt n b = BitVec.ofInt n a) := by
  obtain ⟨p, rfl⟩ := Int.eq_ofNat_of_zero_le ha0
  obtain ⟨q, rfl⟩ := Int.eq_ofNat_of_zero_le hb0
  have hp : p < 2 ^ n := by exact_mod_cast ha1
  have hq : q < 2 ^ n := by exact_mod_cast hb1
  rw [L.bitvec_bits_in_eq, Sem.z_land_eq, decide_eq_decide, ← BitVec.toNat_inj, BitVec.toNat_and,
    BitVec.ofInt_natCast, BitVec.ofInt_natCast, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hp, Nat.mod_eq_of_lt hq]
  show ((p &&& q : Nat) : Int) = p ↔ _
  omega

theorem arith_disjoint_ofInt {n : Nat} {a b : Int} (ha0 : 0 ≤ a) (ha1 : a < 2 ^ n) (hb0 : 0 ≤ b)
    (hb1 : b < 2 ^ n) :
    L.bitvec_disjoint a b = decide (BitVec.ofInt n a &&& BitVec.ofInt n b = 0) := by
  obtain ⟨p, rfl⟩ := Int.eq_ofNat_of_zero_le ha0
  obtain ⟨q, rfl⟩ := Int.eq_ofNat_of_zero_le hb0
  have hp : p < 2 ^ n := by exact_mod_cast ha1
  have hq : q < 2 ^ n := by exact_mod_cast hb1
  rw [L.bitvec_disjoint_eq, Sem.z_land_eq, decide_eq_decide, ← BitVec.toNat_inj, BitVec.toNat_and,
    BitVec.ofInt_natCast, BitVec.ofInt_natCast, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hp, Nat.mod_eq_of_lt hq]
  show ((p &&& q : Nat) : Int) = 0 ↔ _
  simp

theorem arith_toNat_ofInt {n : Nat} {z : Int} (h0 : 0 ≤ z) (h1 : z < 2 ^ n) :
    (BitVec.ofInt n z).toNat = z.toNat := by
  have e : ((2 ^ n : Nat) : Int) = (2 : Int) ^ n := by push_cast; rfl
  rw [BitVec.toNat_ofInt, e, Int.emod_eq_of_lt h0 h1]

theorem arith_toNat_ofInt_sub {n : Nat} {a b : Int} (hb0 : 0 ≤ b) (hba : b ≤ a) (ha1 : a < 2 ^ n) :
    (BitVec.ofInt n a - BitVec.ofInt n b).toNat = (a - b).toNat := by
  rw [BitVec.toNat_sub_of_le (by
      rw [BitVec.le_def, arith_toNat_ofInt hb0 (by omega), arith_toNat_ofInt (by omega) ha1]
      omega),
    arith_toNat_ofInt hb0 (by omega), arith_toNat_ofInt (by omega) ha1]
  omega

theorem arith_natCast_lt_two_pow (n : Nat) : (n : Int) < 2 ^ n := by
  have := Nat.lt_two_pow_self (n := n)
  have e : ((2 ^ n : Nat) : Int) = (2 : Int) ^ n := by push_cast; rfl
  omega

theorem arith_ite_lt {c : Prop} [Decidable c] {a b B : Int} (ha : c → a < B) (hb : ¬c → b < B) :
    (if c then a else b) < B := by
  split <;> simp_all

theorem arith_ite_nonneg {c : Prop} [Decidable c] {a b : Int} (ha : c → 0 ≤ a) (hb : ¬c → 0 ≤ b) :
    0 ≤ if c then a else b := by
  split <;> simp_all

theorem arith_ones_nonneg (n : Nat) : 0 ≤ L.bitvec_ones (n : Int) := by
  have := arith_two_pow_pos n
  rw [arith_ones_nat]; omega

theorem arith_ones_lt (n : Nat) : L.bitvec_ones (n : Int) < 2 ^ n := by
  rw [arith_ones_nat]; omega

attribute [bv_range] arith_ones_nonneg arith_ones_lt

attribute [bv_ofInt] arith_emod_two_pow_of_lt arith_toNat_ofInt arith_toNat_ofInt_sub arith_ofInt_eq_ofInt_iff arith_ofInt_eq_zero_iff arith_zero_eq_ofInt_iff arith_ofInt_ones arith_is_ones_ofInt
  arith_bits_in_ofInt arith_disjoint_ofInt

theorem arith_asTBitVector_TBool : L.asTBitVector LBool.TBool = none := by
  cases h : L.asTBitVector LBool.TBool with
  | none => rfl
  | some m => exact absurd (L.asTBitVector_sound _ _ h).symm (L.TBitVector_ne_TBool m)

attribute [bv_lits] arith_asTBitVector_TBool

/-! ## Overflow facts, through integers -/

section
variable {w : Nat} {x y : BitVec w}

theorem arith_sadd_ok : x.saddOverflow y = false ↔
    -2 ^ (w - 1) ≤ x.toInt + y.toInt ∧ x.toInt + y.toInt < 2 ^ (w - 1) := by
  simp [BitVec.saddOverflow]; omega
theorem arith_ssub_ok : x.ssubOverflow y = false ↔
    -2 ^ (w - 1) ≤ x.toInt - y.toInt ∧ x.toInt - y.toInt < 2 ^ (w - 1) := by
  simp [BitVec.ssubOverflow]; omega
theorem arith_smul_ok : x.smulOverflow y = false ↔
    -2 ^ (w - 1) ≤ x.toInt * y.toInt ∧ x.toInt * y.toInt < 2 ^ (w - 1) := by
  simp [BitVec.smulOverflow]; omega
theorem arith_uadd_ok : x.uaddOverflow y = false ↔ x.toNat + y.toNat < 2 ^ w := by
  simp [BitVec.uaddOverflow]
theorem arith_usub_ok : x.usubOverflow y = false ↔ y.toNat ≤ x.toNat := by
  simp [BitVec.usubOverflow]
theorem arith_umul_ok : x.umulOverflow y = false ↔ x.toNat * y.toNat < 2 ^ w := by
  simp [BitVec.umulOverflow]

theorem arith_sadd_ovf : x.saddOverflow y = true ↔
    x.toInt + y.toInt < -2 ^ (w - 1) ∨ 2 ^ (w - 1) ≤ x.toInt + y.toInt := by
  simp [BitVec.saddOverflow]; omega
theorem arith_ssub_ovf : x.ssubOverflow y = true ↔
    x.toInt - y.toInt < -2 ^ (w - 1) ∨ 2 ^ (w - 1) ≤ x.toInt - y.toInt := by
  simp [BitVec.ssubOverflow]; omega
theorem arith_smul_ovf : x.smulOverflow y = true ↔
    x.toInt * y.toInt < -2 ^ (w - 1) ∨ 2 ^ (w - 1) ≤ x.toInt * y.toInt := by
  simp [BitVec.smulOverflow]; omega
theorem arith_uadd_ovf : x.uaddOverflow y = true ↔ 2 ^ w ≤ x.toNat + y.toNat := by
  simp [BitVec.uaddOverflow]
theorem arith_usub_ovf : x.usubOverflow y = true ↔ x.toNat < y.toNat := by
  simp [BitVec.usubOverflow]
theorem arith_umul_ovf : x.umulOverflow y = true ↔ 2 ^ w ≤ x.toNat * y.toNat := by
  simp [BitVec.umulOverflow]

theorem arith_toInt_add_ok (h : x.saddOverflow y = false) : (x + y).toInt = x.toInt + y.toInt :=
  BitVec.toInt_add_of_not_saddOverflow (by simp [h])
theorem arith_toInt_sub_ok (h : x.ssubOverflow y = false) : (x - y).toInt = x.toInt - y.toInt :=
  BitVec.toInt_sub_of_not_ssubOverflow (by simp [h])
theorem arith_toInt_mul_ok (h : x.smulOverflow y = false) : (x * y).toInt = x.toInt * y.toInt :=
  BitVec.toInt_mul_of_not_smulOverflow (by simp [h])
theorem arith_toNat_add_ok (h : x.uaddOverflow y = false) : (x + y).toNat = x.toNat + y.toNat :=
  BitVec.toNat_add_of_not_uaddOverflow (by simp [h])
theorem arith_toNat_sub_ok (h : x.usubOverflow y = false) : (x - y).toNat = x.toNat - y.toNat :=
  BitVec.toNat_sub_of_not_usubOverflow (by simp [h])
theorem arith_toNat_mul_ok (h : x.umulOverflow y = false) : (x * y).toNat = x.toNat * y.toNat :=
  BitVec.toNat_mul_of_not_umulOverflow (by simp [h])

theorem arith_toInt_bounds (x : BitVec w) : -2 ^ (w - 1) ≤ x.toInt ∧ x.toInt < 2 ^ (w - 1) :=
  ⟨BitVec.le_toInt x, BitVec.toInt_lt⟩

end

open Lean Meta Elab Tactic in
/-- Adds the integer meaning of the non-overflow hypotheses. -/
def arithOvfEqs (g : MVarId) : MetaM MVarId := g.withContext do
  let mut g := g
  for d in (← getLCtx) do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    let some (_, lhs, rhs) := ty.eq? | continue
    unless rhs.isConstOf ``Bool.false do continue
    let lems := [(``BitVec.saddOverflow, ``arith_toInt_add_ok),
      (``BitVec.ssubOverflow, ``arith_toInt_sub_ok), (``BitVec.smulOverflow, ``arith_toInt_mul_ok),
      (``BitVec.uaddOverflow, ``arith_toNat_add_ok), (``BitVec.usubOverflow, ``arith_toNat_sub_ok),
      (``BitVec.umulOverflow, ``arith_toNat_mul_ok)]
    for (f, lem) in lems do
      if lhs.isAppOfArity f 3 then
        let pf ← mkAppM lem #[d.toExpr]
        let (_, g') ← (← g.assert `hovf (← inferType pf) pf).intro1P
        g := g'
  return g

theorem arith_smulOverflow_neg_swap {n : Nat} {c v : BitVec n} (hc : c ≠ BitVec.intMin n)
    (hv : v ≠ BitVec.intMin n) : (-c).smulOverflow v = c.smulOverflow (-v) := by
  simp only [BitVec.smulOverflow, BitVec.toInt_neg_of_ne_intMin hc,
    BitVec.toInt_neg_of_ne_intMin hv, Int.neg_mul, Int.mul_neg]

theorem arith_umul_assoc_ok {n : Nat} {x y z : BitVec n} (h1 : x.umulOverflow y = false)
    (h2 : (x * y).umulOverflow z = false) : x.umulOverflow (y * z) = false := by
  have e := arith_toNat_mul_ok h1
  rw [arith_umul_ok] at *
  rw [e] at h2
  have : (y * z).toNat ≤ y.toNat * z.toNat := by rw [BitVec.toNat_mul]; exact Nat.mod_le _ _
  calc x.toNat * (y * z).toNat ≤ x.toNat * (y.toNat * z.toNat) := Nat.mul_le_mul_left _ this
    _ = x.toNat * y.toNat * z.toNat := (Nat.mul_assoc ..).symm
    _ < 2 ^ n := h2

theorem arith_smul_assoc_ok {n : Nat} {x y z : BitVec n} (h1 : x.smulOverflow y = false)
    (h2 : (x * y).smulOverflow z = false) (h3 : y.smulOverflow z = false) :
    x.smulOverflow (y * z) = false := by
  rwa [← BitVec.smulOverflow_assoc (by simp [h1]) (by simp [h3])]

theorem arith_smulOverflow_neg_swap' {n : Nat} {c v : BitVec n} (hc : c ≠ BitVec.intMin n)
    (hv : v ≠ BitVec.intMin n) : (-c).smulOverflow v = (-v).smulOverflow c := by
  rw [arith_smulOverflow_neg_swap hc hv, arith_smulOverflow_comm]

theorem arith_umul_assoc_ok₂ {n : Nat} {x y z : BitVec n} (h1 : y.umulOverflow x = false)
    (h2 : (y * x).umulOverflow z = false) : x.umulOverflow (y * z) = false :=
  arith_umul_assoc_ok (by rwa [arith_umulOverflow_comm]) (by rwa [BitVec.mul_comm])

theorem arith_umul_assoc_ok₃ {n : Nat} {x y z : BitVec n} (h1 : x.umulOverflow y = false)
    (h2 : z.umulOverflow (x * y) = false) : x.umulOverflow (y * z) = false :=
  arith_umul_assoc_ok h1 (by rwa [arith_umulOverflow_comm])

theorem arith_umul_assoc_ok₄ {n : Nat} {x y z : BitVec n} (h1 : y.umulOverflow x = false)
    (h2 : z.umulOverflow (y * x) = false) : x.umulOverflow (y * z) = false :=
  arith_umul_assoc_ok₂ h1 (by rwa [arith_umulOverflow_comm])

theorem arith_smul_assoc_ok₂ {n : Nat} {x y z : BitVec n} (h1 : y.smulOverflow x = false)
    (h2 : (y * x).smulOverflow z = false) (h3 : y.smulOverflow z = false) :
    x.smulOverflow (y * z) = false :=
  arith_smul_assoc_ok (by rwa [arith_smulOverflow_comm]) (by rwa [BitVec.mul_comm]) h3

theorem arith_smul_assoc_ok₃ {n : Nat} {x y z : BitVec n} (h1 : x.smulOverflow y = false)
    (h2 : z.smulOverflow (x * y) = false) (h3 : y.smulOverflow z = false) :
    x.smulOverflow (y * z) = false :=
  arith_smul_assoc_ok h1 (by rwa [arith_smulOverflow_comm]) h3

theorem arith_smul_assoc_ok₄ {n : Nat} {x y z : BitVec n} (h1 : y.smulOverflow x = false)
    (h2 : z.smulOverflow (y * x) = false) (h3 : y.smulOverflow z = false) :
    x.smulOverflow (y * z) = false :=
  arith_smul_assoc_ok₂ h1 (by rwa [arith_smulOverflow_comm]) h3

theorem arith_umul_add_ok {n : Nat} {a x y : BitVec n} (h1 : a.umulOverflow x = false)
    (h2 : a.umulOverflow y = false) (h3 : (a * x).uaddOverflow (a * y) = false) :
    a.umulOverflow (x + y) = false := by
  rw [arith_uadd_ok, arith_toNat_mul_ok h1, arith_toNat_mul_ok h2, ← Nat.mul_add] at h3
  rw [arith_umul_ok, BitVec.toNat_add]
  exact Nat.lt_of_le_of_lt (Nat.mul_le_mul_left _ (Nat.mod_le _ _)) h3

theorem arith_udivides_eq {d z : Int} (hd0 : 0 ≤ d) (hz0 : 0 ≤ z) :
    L.bitvec_udivides d z = decide (d.toNat ∣ z.toNat) := by
  obtain ⟨p, rfl⟩ := Int.eq_ofNat_of_zero_le hd0
  obtain ⟨q, rfl⟩ := Int.eq_ofNat_of_zero_le hz0
  rw [L.bitvec_udivides_eq, Sem.divisible_eq]
  simp only [Prim.divisible, Int.toNat_natCast, Int.natCast_dvd_natCast]

attribute [bv_ofInt] arith_udivides_eq

theorem arith_smtUDiv_toNat {n : Nat} {a b : BitVec n} (hb : b.toNat ≠ 0) :
    (a.smtUDiv b).toNat = a.toNat / b.toNat := by
  simp [BitVec.smtUDiv_eq, ← BitVec.toNat_inj, hb]

theorem arith_factor_ok {n : Nat} {a b x y : BitVec n} (hab : a.toNat ≠ 0 ∨ b.toNat ≠ 0)
    (hd : a.toNat ∣ b.toNat) (h1 : a.umulOverflow x = false) (h2 : b.umulOverflow y = false)
    (h3 : (a * x).uaddOverflow (b * y) = false) :
    ckOp ⟨false, true⟩ BitVec.smulOverflow BitVec.umulOverflow (· * ·) (some a)
      (ckOp ⟨false, true⟩ BitVec.saddOverflow BitVec.uaddOverflow (· + ·) (some x)
        (if (b.smtUDiv a).umulOverflow y = true then none else some (b.smtUDiv a * y))) =
      some (a * x + b * y) := by
  have ha : a.toNat ≠ 0 := fun h => by
    rw [h] at hd; have := Nat.eq_zero_of_zero_dvd hd; omega
  obtain ⟨q, hq⟩ := hd
  have hc : (b.smtUDiv a).toNat = q := by
    rw [arith_smtUDiv_toNat ha, hq, Nat.mul_div_cancel_left _ (by omega)]
  have e1 := arith_toNat_mul_ok h1
  have e2 := arith_toNat_mul_ok h2
  rw [arith_uadd_ok, e1, e2] at h3
  rw [arith_umul_ok] at h1 h2
  have hA : 1 ≤ a.toNat := by omega
  have l1 : q * y.toNat ≤ b.toNat * y.toNat := by
    rw [hq, Nat.mul_assoc]; exact Nat.le_mul_of_pos_left _ hA
  have l2 : x.toNat ≤ a.toNat * x.toNat := Nat.le_mul_of_pos_left _ hA
  have o1 : (b.smtUDiv a).umulOverflow y = false := by rw [arith_umul_ok, hc]; omega
  have e3 := arith_toNat_mul_ok o1
  have o2 : x.uaddOverflow (b.smtUDiv a * y) = false := by rw [arith_uadd_ok, e3, hc]; omega
  have e4 := arith_toNat_add_ok o2
  have hs : a.toNat * (x.toNat + q * y.toNat) = a.toNat * x.toNat + b.toNat * y.toNat := by
    rw [hq, Nat.mul_add, Nat.mul_assoc]
  have o3 : a.umulOverflow (x + b.smtUDiv a * y) = false := by
    rw [arith_umul_ok, e4, e3, hc, hs]; omega
  simp only [o1, o2, o3, ckOp, Bool.false_eq_true, ite_false, Bool.false_and, Bool.true_and,
    Bool.false_or, Option.some.injEq]
  apply BitVec.eq_of_toNat_eq
  rw [arith_toNat_mul_ok o3, e4, e3, hc, hs,
    arith_toNat_add_ok (by rw [arith_uadd_ok, e1, e2]; omega), e1, e2]

theorem arith_factor_ok' {n : Nat} {a b x y : BitVec n} (ha : a.toNat ≠ 0 ∨ b.toNat ≠ 0)
    (hd : a.toNat ∣ b.toNat)
    (h1 : a.umulOverflow x = false) (h2 : b.umulOverflow y = false)
    (h3 : (b * y).uaddOverflow (a * x) = false) :
    ckOp ⟨false, true⟩ BitVec.smulOverflow BitVec.umulOverflow (· * ·) (some a)
      (ckOp ⟨false, true⟩ BitVec.saddOverflow BitVec.uaddOverflow (· + ·) (some x)
        (if (b.smtUDiv a).umulOverflow y = true then none else some (b.smtUDiv a * y))) =
      some (b * y + a * x) := by
  rw [BitVec.add_comm]
  exact arith_factor_ok ha hd h1 h2 (by rw [arith_uadd_ok] at *; omega)

/-- An addition that cannot wrap around, by the bounds of its operands
(`unsigned_ub`, from `msb_of`), may be checked unsigned. -/
theorem arith_refines_add_no_wrap {c : CoreMod.Checked} {a b : S.Term} {t : S.Ty} :
    S.Refines (B.node (L.AddK c a b) t) (B.node (L.AddK (L.bitvec_no_wrap c a b) a b) t) := by
  rw [L.bitvec_no_wrap_eq]
  split
  · rename_i h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨_, h⟩ := h
    refine Refines.den (L := L) (fun w => ?_) (fun w => ?_) (fun n w ht ρ x e => ?_)
    · obtain ⟨⟨⟨m, _, hm⟩, _, ht⟩, _, _⟩ := (L.WT_Add _ _ _ _).1 w
      exact ⟨m, by rw [B.ty_node, ht, hm]⟩
    · obtain ⟨w1, wa, wb⟩ := (L.WT_Add _ _ _ _).1 w
      exact ⟨(L.WT_Add _ _ _ _).2 ⟨w1, wa, wb⟩, by rw [B.ty_node, B.ty_node]⟩
    · obtain ⟨⟨⟨m, _, hm⟩, hb, htt⟩, wa, wb⟩ := (L.WT_Add _ _ _ _).1 w
      rw [B.ty_node] at ht
      have han : S.ty a = L.TBitVector n := htt ▸ ht
      have hbn : S.ty b = L.TBitVector n := hb.trans han
      rw [Sem.den_Add] at e ⊢
      cases ea : Sem.den L ρ n a <;> cases eb : Sem.den L ρ n b <;> rw [ea, eb] at e <;>
        (try simp only [BitvecMod.ckOp_none_l, BitvecMod.ckOp_none_r, reduceCtorEq] at e ⊢)
      rename_i xa xb
      have la := Sem.den_msb ρ a n xa wa han ea
      have lb := Sem.den_msb ρ b n xb wb hbn eb
      simp only [L.bitvec_unsigned_ub_eq, L.bitvec_size_eq, han, Sem.size_of_ty_TBitVector,
        Sem.z_lsl_eq, arith_z_lsl_one, Int.toNat_natCast] at h
      have e1 : (((2 : Nat) ^ (L.bitvec_msb_of a + 1).toNat : Nat) : Int) =
          (2 : Int) ^ (L.bitvec_msb_of a + 1).toNat := by push_cast; rfl
      have e2 : (((2 : Nat) ^ (L.bitvec_msb_of b + 1).toNat : Nat) : Int) =
          (2 : Int) ^ (L.bitvec_msb_of b + 1).toNat := by push_cast; rfl
      have e3 : (((2 : Nat) ^ n : Nat) : Int) = (2 : Int) ^ n := by push_cast; rfl
      have hov : xa.uaddOverflow xb = false := by
        rw [arith_uadd_ok]; omega
      rw [BitvecMod.ckOp_some] at e ⊢
      simp only [hov, Bool.and_false, Bool.or_false, Bool.and_true] at e ⊢
      exact e
  · exact Kanon.Sem.Refines.refl

open Lean in
/-- The subterms of `e` (without loose bound variables) that satisfy `p`. -/
partial def arithSubterms (p : Expr → Bool) (e : Expr) (acc : Array Expr := #[]) : Array Expr :=
  let acc := if p e && !e.hasLooseBVars && !acc.contains e then acc.push e else acc
  match e with
  | .app f a => arithSubterms p a (arithSubterms p f acc)
  | .lam _ t b _ | .forallE _ t b _ => arithSubterms p b (arithSubterms p t acc)
  | .letE _ t v b _ => arithSubterms p b (arithSubterms p v (arithSubterms p t acc))
  | .mdata _ b => arithSubterms p b acc
  | .proj _ _ b => arithSubterms p b acc
  | _ => acc

open Lean Meta Elab Tactic in
/-- Adds the bounds of the `toInt`s and `toNat`s of the goal and hypotheses. -/
def arithOvfBounds (g : MVarId) : MetaM MVarId := g.withContext do
  let mut g := g
  let mut exprs : Array Expr := #[← instantiateMVars (← g.getType)]
  for d in (← getLCtx) do
    if !d.isImplementationDetail then exprs := exprs.push (← instantiateMVars d.type)
  let mut atoms : Array Expr := #[]
  for e in exprs do
    let subs := arithSubterms
      (fun sub => sub.isAppOfArity ``BitVec.toInt 2 || sub.isAppOfArity ``BitVec.toNat 2) e
    atoms := atoms ++ (subs.map (·.appArg!)).filter (!atoms.contains ·)
  for x in atoms do
    for lem in [``arith_toInt_bounds, ``BitVec.isLt] do
      let pf ← mkAppM lem #[x]
      let (_, g') ← (← g.assert `hbd (← inferType pf) pf).intro1P
      g := g'
  return g

open Lean Meta Elab Tactic in
/-- Case splits the booleans and the checked flags of the context. -/
partial def arithSplitBools (g : MVarId) : MetaM (List MVarId) := g.withContext do
  for d in (← getLCtx) do
    if d.isImplementationDetail then continue
    let ty ← whnfR (← instantiateMVars d.type)
    if ty.isConstOf ``Bool || ty.isConstOf ``CoreMod.Checked then
      let subgoals ← g.cases d.fvarId
      return ← subgoals.toList.foldlM (init := []) fun acc sg =>
        return acc ++ (← arithSplitBools sg.mvarId)
  return [g]

theorem arith_add_left_comm {w : Nat} (x y z : BitVec w) : x + (y + z) = y + (x + z) := by
  rw [← BitVec.add_assoc, BitVec.add_comm x y, BitVec.add_assoc]

theorem arith_mul_left_comm {w : Nat} (x y z : BitVec w) : x * (y * z) = y * (x * z) := by
  rw [← BitVec.mul_assoc, BitVec.mul_comm x y, BitVec.mul_assoc]

open Lean Meta Elab Tactic in
/-- Generalizes the bit-vectors of the literals (`BitVec.ofInt n z`) of the goal
and the hypotheses. -/
elab "bv_arith_gen_lits" : tactic => withMainContext do
  let mut exprs : Array Expr := #[← instantiateMVars (← getMainTarget)]
  for d in (← getLCtx) do
    if !d.isImplementationDetail then exprs := exprs.push (← instantiateMVars d.type)
  let mut lits : Array Expr := #[]
  for e in exprs do
    lits := arithSubterms (·.isAppOfArity ``BitVec.ofInt 2) e lits
  for l in lits do
    let t ← Term.exprToSyntax l
    let x := mkIdent (← mkFreshUserName `bl)
    evalTactic (← `(tactic| generalize $t:term = $x:ident at *))

open Lean Meta Elab Tactic in
/-- Destructs the conjunctions, disjunctions and existentials of the hypotheses. -/
partial def arithSplitHyps (g : MVarId) : MetaM (List MVarId) := g.withContext do
  for d in (← getLCtx) do
    if d.isImplementationDetail then continue
    let ty ← whnfR (← instantiateMVars d.type)
    if ty.isAppOfArity ``And 2 || ty.isAppOfArity ``Exists 2 || ty.isAppOfArity ``Or 2 then
      let subgoals ← g.cases d.fvarId
      return ← subgoals.toList.foldlM (init := []) fun acc sg =>
        return acc ++ (← arithSplitHyps sg.mvarId)
  return [g]

open Lean Meta Elab Tactic in
elab "bv_arith_split" : tactic => liftMetaTactic arithSplitHyps

open Lean Meta Elab Tactic in
/-- Adds, for the equalities of bit-vectors of the context, the equalities of
their bits at `i`. -/
elab "bv_arith_bit_hyps " i:ident : tactic => withMainContext do
  for d in (← getLCtx) do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    let some (t, _, _) := ty.eq? | continue
    unless t.isAppOfArity ``BitVec 1 do continue
    let h := mkIdent d.userName
    evalTactic (← `(tactic| have := congrArg (fun v => BitVec.getLsbD v $i) $h))

open Lean Meta Elab Tactic in
elab "bv_arith_ovf_eqs" : tactic => liftMetaTactic fun g => return [← arithOvfEqs g]

open Lean Meta Elab Tactic in
elab "bv_arith_bounds" : tactic => liftMetaTactic fun g => return [← arithOvfBounds g]

open Lean Meta Elab Tactic in
elab "bv_arith_bools" : tactic => liftMetaTactic arithSplitBools

end Lib

/-- The side conditions of the `bv_ofInt` lemmas: the ranges of literals. -/
macro "bv_arith_disch" : tactic => `(tactic| first
  | assumption
  | omega
  | (simp only [bv_range, Int.toNat_natCast]; done)
  | (refine Int.lt_of_le_of_lt ?_ (BitvecMod.Lib.arith_natCast_lt_two_pow _); omega)
  | (simp_all [bv_range]; done)
  | (apply BitvecMod.Lib.arith_ite_lt <;> intro <;> first
      | omega
      | (refine Int.lt_of_le_of_lt ?_ (BitvecMod.Lib.arith_natCast_lt_two_pow _); omega))
  | (apply BitvecMod.Lib.arith_ite_nonneg <;> intro <;> omega))

/-- The operations on literals as those on bit-vectors (`bv_ofInt`), with their
side conditions. -/
macro "bv_arith_lit_ops" : tactic => `(tactic| (
  (try simp only [Int.toNat_natCast, Syntax.bitvec_zmin_eq, BitVec.ushiftRight_eq',
    BitVec.shiftLeft_eq', BitVec.sshiftRight_eq'] at *)
  (try simp (disch := (bv_arith_disch; done)) only [bv_ofInt] at *)))

set_option hygiene false in
/-- `bv_sem_core`, with the operations on literals whose lemmas have hypotheses
(`ofInt_lit_and`, …). -/
macro "bv_arith_sem_core" : tactic => `(tactic| (
  first
    | intro n w ht ρ x e
    | intro w ρ x e
  bv_facts
  (try bv_nat_widths)
  (try simp only [bv_den, bv_lits] at e ⊢)
  (try bv_rw_tys)
  (try simp only [bv_lits, eq_self_iff_true, ite_true] at e ⊢)
  bv_arith_lit_ops
  run_tac Kanon.Proof.caseAllAtoms (some #[``BitvecMod.Lib.den_cases, ``BitvecMod.Lib.denB_cases])
  all_goals (try bv_bool_vars)
  all_goals (try simp only [Option.map_some, Option.map_none, Option.some.injEq,
    reduceCtorEq, BitvecMod.ckOp_some, BitvecMod.binOp_some, BitvecMod.negOp_some] at e ⊢)
  all_goals (try subst e)))

open Lean Meta Elab Tactic in
/-- The guards on masks (`bits_in`, `disjoint`) as facts on the bit-vectors of
the width of the goal. -/
elab "bv_arith_masks" : tactic => withMainContext do
  let some (t, _, _) := (← instantiateMVars (← getMainTarget)).eq? | throwError "no equality"
  unless t.isAppOfArity ``BitVec 1 do throwError "not bit-vectors"
  let n ← Term.exprToSyntax t.appArg!
  evalTactic (← `(tactic| simp (disch := (bv_arith_disch; done)) only
    [BitvecMod.Lib.arith_bits_in_ofInt (n := $n), BitvecMod.Lib.arith_disjoint_ofInt (n := $n),
     decide_eq_true_eq] at *))

/-- Proves an equality of bit-vectors bit by bit, with the bits of the
equalities of the context. -/
macro "bv_arith_bits" : tactic => `(tactic| (
  (try bv_arith_masks)
  (try bv_arith_lit_ops)
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  bv_arith_bit_hyps i
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_xor, BitVec.getLsbD_not,
    BitVec.getLsbD_setWidth, BitVec.getLsbD_append, ite_false, ite_true,
    BitVec.getLsbD_zero, BitVec.getLsbD_allOnes, BitVec.ushiftRight_eq', BitVec.shiftLeft_eq',
    BitVec.sshiftRight_eq', BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_sshiftRight, Bool.and_true, Bool.true_and, decide_true] at *
  bv_arith_lit_ops
  (try simp (disch := omega) only [BitVec.getLsbD_of_ge, Bool.and_false, Bool.false_and] at *)
  first
    | (congr 1; omega)
    | grind [BitVec.getLsbD_of_ge]))

/-- Proves overflow facts: splits the flags, and reasons on integers. -/
macro "bv_arith_ovf" : tactic => `(tactic| (
  (try bv_arith_gen_lits)
  bv_arith_bools
  all_goals (try simp_all)
  all_goals (repeat' (first | apply And.intro | intro))
  all_goals (try bv_arith_split)
  all_goals bv_arith_ovf_eqs
  all_goals (try simp only [BitvecMod.Lib.arith_sadd_ok, BitvecMod.Lib.arith_ssub_ok,
    BitvecMod.Lib.arith_smul_ok, BitvecMod.Lib.arith_uadd_ok, BitvecMod.Lib.arith_usub_ok,
    BitvecMod.Lib.arith_umul_ok, BitvecMod.Lib.arith_sadd_ovf, BitvecMod.Lib.arith_ssub_ovf,
    BitvecMod.Lib.arith_smul_ovf, BitvecMod.Lib.arith_uadd_ovf, BitvecMod.Lib.arith_usub_ovf,
    BitvecMod.Lib.arith_umul_ovf] at *)
  all_goals (try bv_arith_split)
  all_goals bv_arith_bounds
  all_goals omega))

/-- Closes a factorization by a constant (`arith_factor_ok`). -/
macro "bv_arith_factor" : tactic => `(tactic| (
  (try simp only [Bool.false_and, Bool.false_or, Bool.true_and] at ⊢)
  first
    | (with_reducible refine Eq.trans (BitvecMod.Lib.arith_factor_ok ?_ ?_ ?_ ?_ ?_) ?_
       all_goals (try bv_arith_lit_ops)
       all_goals first | (simp_all; done) | omega)
    | (with_reducible refine Eq.trans (BitvecMod.Lib.arith_factor_ok' ?_ ?_ ?_ ?_ ?_) ?_
       all_goals (try bv_arith_lit_ops)
       all_goals first | (simp_all; done) | omega)))

set_option hygiene false in
/-- Closes the value goals left by `bv_arith_sem_core` (its hypothesis `e`). -/
macro "bv_arith_close" : tactic => `(tactic| (
  (try (repeat' (first
    | (simp only [BitvecMod.ckOp_some, BitvecMod.ckOp_none_l, BitvecMod.ckOp_none_r,
        BitvecMod.binOp_some, BitvecMod.binOp_none_l, BitvecMod.binOp_none_r,
        BitvecMod.negOp_some, BitvecMod.negOp_none, Option.some.injEq, reduceCtorEq] at e)
    | split at e)))
  all_goals (try bv_arith_lit_ops)
  all_goals first
    | (bv_arith_factor; done)
    | skip
  all_goals (try (repeat' split))
  all_goals (try bv_arith_lit_ops)
  all_goals first
    | (bv_arith_bools
       all_goals simp_all [BitVec.mul_assoc, BitvecMod.Lib.arith_smulOverflow_neg_swap,
        BitvecMod.Lib.arith_umul_assoc_ok, BitvecMod.Lib.arith_smul_assoc_ok,
        BitvecMod.Lib.arith_umul_add_ok, BitVec.mul_add]
       done)
    | (bv_arith_bools
       all_goals simp_all [BitvecMod.Lib.arith_smulOverflow_neg_swap',
        BitvecMod.Lib.arith_umul_assoc_ok₂, BitvecMod.Lib.arith_umul_assoc_ok₃,
        BitvecMod.Lib.arith_umul_assoc_ok₄, BitvecMod.Lib.arith_smul_assoc_ok₂,
        BitvecMod.Lib.arith_smul_assoc_ok₃, BitvecMod.Lib.arith_smul_assoc_ok₄]
       all_goals simp_all [BitVec.mul_assoc, BitVec.mul_comm, BitvecMod.Lib.arith_mul_left_comm]
       done)
    | skip
  all_goals (try simp_all [BitvecMod.Lib.arith_ssubOverflow_zero_left])
  all_goals (try bv_arith_lit_ops)
  all_goals (try simp_all)
  all_goals first
    | done
    | omega
    | (grind [BitVec.neg_eq_not_add]; done)
    | (bv_arith_bools
       all_goals simp_all [BitvecMod.Lib.arith_saddOverflow_comm,
        BitvecMod.Lib.arith_uaddOverflow_comm, BitvecMod.Lib.arith_smulOverflow_comm,
        BitvecMod.Lib.arith_umulOverflow_comm, BitVec.add_comm, BitVec.mul_comm]
       done)
    | (simp_all [BitVec.add_assoc, BitVec.add_comm, BitvecMod.Lib.arith_add_left_comm,
        BitVec.mul_assoc, BitVec.mul_comm, BitvecMod.Lib.arith_mul_left_comm]; done)
    | (bv_arith_bits; done)
    | (bv_arith_ovf; done)))

open Lean Meta Elab Tactic in
/-- Fails on the value halves of `Refines.den` and `Refines.denB` (`∀ n : Nat, …`,
`S.WT s → ∀ ρ b, …`), so that they are not taken for the typing half
(`S.WT s → S.WT r ∧ …`). -/
elab "bv_arith_wt_goal" : tactic => withMainContext do
  let t ← whnfR (← instantiateMVars (← getMainTarget))
  let .forallE _ d b _ := t | throwError "not a typing goal"
  if (← whnfR d).isConstOf ``Nat || b.isForall then throwError "not a typing goal"

/-- `bv_wt`, closing the goals that are hypotheses before `simp_all` (which
can loop on the sorts of the operands). -/
macro "bv_arith_wt" : tactic => `(tactic| (
  bv_arith_wt_goal
  intro w
  bv_facts
  (try bv_nat_widths)
  all_goals (try refine ⟨?_, ?_⟩)
  all_goals first
    | done
    | assumption
    | (simp_all [bv_range]; done)
    | grind))

/-- Proves an arm of the functions of this file. -/
macro "bv_arith" : tactic => `(tactic| (
  kanon_rule_lift
  bv_rule_apply
  all_goals first
    | (bv_arith_wt; done)
    | (bv_arith_wt_goal; bv_wt; done)
    | (bv_arith_sem_core; all_goals bv_arith_close)))

end BitvecMod

namespace BitvecMod

attribute [kanon_tactic "bv_arith"] Bitvec.add.spec Bitvec.sub.spec Bitvec.mul.spec Bitvec.neg.spec
  Bitvec.and_.spec Bitvec.or_.spec Bitvec.xor.spec Bitvec.shl.spec Bitvec.lshr.spec Bitvec.ashr.spec
  Bitvec.not_bool.spec Bitvec.of_bool.spec Bitvec.to_bool.spec

end BitvecMod
