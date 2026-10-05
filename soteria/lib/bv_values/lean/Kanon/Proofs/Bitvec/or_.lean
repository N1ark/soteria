import Kanon.Lib.Bitwise
import Kanon.Statements.Bitvec.or_

/-! The arms of `Bitvec.or_` that the default tactics do not prove. -/

namespace Kanon

open Classical Lib

@[kanon_arm] theorem Bitvec.or_.r_extend_shl.main.proof : Bitvec.or_.r_extend_shl.main.Stmt := by
  intro FS O hO nx base t5 w8 tail t11 z T t13 hg
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hg
  obtain ⟨hs, hnx⟩ := hg
  simp only [kanon_spec, ty]
  repeat' split
  all_goals simp only [decide_eq_true_eq] at *
  all_goals kanon_lift_body
  all_goals simp only [kanon_spec]
  all_goals apply Refines.den
  -- the guard on the shift amount is only needed for the values, and it
  -- makes `simp_all` loop on the widths
  all_goals first
    | (clear hs; kanon_wt_bv; done)
    | (intro n w ht ρ x h
       kanon_facts
       kanon_lits
       kanon_lit_ops
       kanon_cases
       all_goals (try simp_all)
       all_goals kanon_zlits
       all_goals
         rw [or_shl_append _ _ (by omega)] at h
         subst h)
  · rfl
  · exact BitVec.setWidth_setWidth (by omega)
  · exact setWidth_append_extract _ _ (by omega)

end Kanon
