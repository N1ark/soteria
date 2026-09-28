import Bvr.Lib.Bitwise

/-! Bitwise operations and shifts, proved per alternative. -/

namespace Bvr

open Classical Lib

theorem bv_and.r_ones.a1.proof : bv_and.r_ones.a1.Stmt := by
  bvr_rule_sem
  all_goals simp_all [is_ones_mk]

theorem bv_and.r_ones.a2.proof : bv_and.r_ones.a2.Stmt := by
  bvr_rule_sem
  all_goals simp_all [is_ones_mk]

theorem bv_and.r_lshr_mask.a1.proof : bv_and.r_lshr_mask.a1.Stmt := by
  bvr_rule_sem
  all_goals subst_vars; exact (lshr_and_of_bits_in ‹_› _).symm

theorem bv_and.r_lshr_mask.a2.proof : bv_and.r_lshr_mask.a2.Stmt := by
  bvr_rule_sem
  all_goals subst_vars; rw [BitVec.and_comm]; exact (lshr_and_of_bits_in ‹_› _).symm

theorem bv_and.r_mask_or_disj.a1.proof : bv_and.r_mask_or_disj.a1.Stmt := by
  bvr_rule_sem
  all_goals subst_vars; exact (and_or_of_disjoint ‹_› _).symm

theorem bv_or.r_extend_shl.a1.proof : bv_or.r_extend_shl.a1.Stmt := by
  intro FS O hO nx base t5 w8 tail t11 z T t13 hg
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hg
  obtain ⟨hs, hnx⟩ := hg
  simp only [bvr_spec, ty]
  repeat' split
  all_goals simp only [decide_eq_true_eq] at *
  all_goals bvr_lift_body
  all_goals simp only [bvr_spec]
  all_goals apply Refines.den
  -- the guard on the shift amount is only needed for the values, and it
  -- makes `simp_all` loop on the widths
  all_goals first
    | (clear hs; bvr_wt; done)
    | (intro n w ht ρ x h
       bvr_facts
       bvr_lits
       bvr_cases
       all_goals (try simp_all)
       all_goals
         rw [or_shl_append _ _ (by omega)] at h
         subst h)
  · rfl
  · exact setWidth_setWidth_of_ge _ (by omega)
  · exact setWidth_append_extract _ _ (by omega)

end Bvr
