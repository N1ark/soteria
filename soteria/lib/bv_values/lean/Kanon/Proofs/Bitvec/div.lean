import Kanon.Lib.Arith
import Kanon.Statements.Bitvec.div

/-! The arms of `Bitvec.div` that the default tactics do not prove. -/

namespace Kanon

open Classical Lib

/-- Division of a zero-extended value by a constant that fits in the value. -/
theorem zext_div_ok {m n : Nat} (hmn : m ≤ n) (x : BitVec m) {z : Int} (h0 : 0 ≤ z)
    (hz : 0 < z ∧ z < 2 ^ m ∨ m = n) (hzn : z < 2 ^ n) :
    (x.setWidth n).smtUDiv (BitVec.ofInt n z) = (x.smtUDiv (BitVec.ofInt m z)).setWidth n := by
  rcases hz with ⟨hz0, hzm⟩ | rfl
  · have hm : (BitVec.ofInt m z).toNat ≠ 0 := by rw [toNat_ofInt_of_lt h0 hzm]; omega
    have hn : (BitVec.ofInt n z).toNat ≠ 0 := by rw [toNat_ofInt_of_lt h0 hzn]; omega
    have := x.isLt
    have hp : 2 ^ m ≤ 2 ^ n := Nat.pow_le_pow_right (by omega) hmn
    apply BitVec.eq_of_toNat_eq
    rw [smtUDiv_toNat hn, BitVec.toNat_setWidth, BitVec.toNat_setWidth, smtUDiv_toNat hm,
      toNat_ofInt_of_lt h0 hzm, toNat_ofInt_of_lt h0 hzn, Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by have := Nat.div_le_self x.toNat z.toNat; omega)]
  · simp

@[kanon_arm] theorem Bitvec.div.r_zext.main.proof : Bitvec.div.r_zext.main.Stmt := by
  kanon_rule_sem
  all_goals kanon_split
  all_goals subst_vars
  rename_i FS O hO by_ z n ρ w1 hby kind x hs hn_ hz0 hzn hn hn0 hmsb hz1
  simp only [msb_of_lit, size_of_ty_bitVector] at *
  by_cases hp : 0 < z
  · have hlt : z < 2 ^ (kind : Int).toNat := lt_two_pow_log2 hp (by simpa [hp] using hmsb)
    simp only [Int.toNat_natCast] at hlt
    rw [Int.emod_eq_of_lt hz0 (by exact_mod_cast hlt)]
    exact (zext_div_ok (m := kind) (n := n) (by omega) x hz0 (.inl ⟨hp, hlt⟩) hzn).symm
  · have hz : z = 0 := by omega
    subst hz
    have hWn : kind = n := by simp only [hp, ite_false] at hmsb; omega
    subst hWn
    rw [Int.zero_emod]
    simp only [BitVec.setWidth_eq]

end Kanon
