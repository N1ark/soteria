import Kanon.Lib.Den
import Kanon.Model.Bitvec.msb_of

/-!
# Literals

Facts about the literals that the language's instances of the modules' semantics
(`Lang/`) use: bit-vector literals in range and `log2`.
-/

namespace Kanon.Lib

open CoreMod

open Classical

/-! ## Constants in range -/

theorem toNat_ofInt_of_lt {n : Nat} {k : Int} (h0 : 0 ≤ k) (h1 : k < 2 ^ n) :
    (BitVec.ofInt n k).toNat = k.toNat := by
  rw [BitVec.toNat_ofInt, Int.emod_eq_of_lt h0 (by push_cast; exact h1)]

/-! ## Integer helpers -/

@[simp] theorem log2_two_pow (k : Nat) : log2 ((2 : Int) ^ k) = k := by
  rw [show (2 : Int) ^ k = ((2 ^ k : Nat) : Int) by push_cast; rfl, log2, Int.toNat_natCast,
    Nat.log2_two_pow]

theorem lt_two_pow_log2 {z w : Int} (hz : 0 < z) (h : log2 z < w) : z < 2 ^ w.toNat := by
  have hl := Nat.lt_log2_self (n := z.toNat)
  have hle : 2 ^ (Nat.log2 z.toNat + 1) ≤ 2 ^ w.toNat :=
    Nat.pow_le_pow_right (by omega) (by simp only [log2] at h; omega)
  have : ((z.toNat : Nat) : Int) < ((2 ^ w.toNat : Nat) : Int) := by exact_mod_cast (by omega)
  push_cast at this; omega

end Kanon.Lib
