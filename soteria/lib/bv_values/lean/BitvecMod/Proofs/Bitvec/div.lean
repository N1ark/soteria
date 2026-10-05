import BitvecMod.Lifts
import BitvecMod.Statements.Bitvec.div

/-! The arm of `Bitvec.div` that `bveq_rule` does not prove. -/

namespace BitvecMod

open Lib.BvEq

/-- The division of a zero-extension by a constant that fits in the extended value. -/
@[kanon_arm] theorem Bitvec.div.r_zext.main.proof : Bitvec.div.r_zext.main.Stmt := by
  bveq_rule_lift
  case hl.hs_v2 =>
    bveq_side_facts
    exact nonzero_masked_zext ‹_› ‹_› ‹_› ‹_› ‹_›
  all_goals kanon_on_refines bv_apply_den
  all_goals first | (bveq_wt; done) | bveq_sem_core
  all_goals
    rename_i hmsb
    subst e
    rw [msb_of_lit (by omega), Sem.size_of_ty_TBitVector] at hmsb
    refine (zext_div_ok (by omega) _ _ ?_).symm
    by_cases hp : 0 < k.toNat
    · simp only [Int.natCast_pos, hp, ite_true] at hmsb
      have := lt_two_pow_log2 (by omega) hmsb
      simp only [Int.toNat_natCast] at this
      exact .inl ⟨hp, by exact_mod_cast this⟩
    · simp only [Int.natCast_pos, hp, ite_false] at hmsb
      exact .inr (by omega)

end BitvecMod
