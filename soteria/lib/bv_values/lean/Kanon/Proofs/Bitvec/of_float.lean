import Kanon.Lib.Resize
import Kanon.Statements.Bitvec.of_float

/-! The arms of `Bitvec.of_float` that the default tactics do not prove. -/

namespace Kanon

open Classical Lib

@[kanon_arm] theorem Bitvec.of_float.r_lit.main.proof : Bitvec.of_float.r_lit.main.Stmt := by
  intro FS O hO rm s n f T
  rcases ez : O.orc.f_to_int rm s n f with _ | z
  · simp [firstSome]; exact Sem.Refines.refl
  · simp [firstSome]
    refine Sem.Refines.intro_eval (fun w => ?_) (fun ρ v w w' e => ?_)
    · have := (WT_op1.1 w).1; simp [Op1.WT] at this
      exact ⟨mk_masked_WT this.1, by simp [Bitvec.of_float.spec]⟩
    · have ⟨w1, w2⟩ := WT_op1.1 w
      simp [Op1.WT] at w1
      rw [← eval] at e ⊢
      rw [Bitvec.of_float.spec, eval_op1 w, eval_float w2] at e
      rw [eval_mk_masked w1.1, ← hO.orc.to_int rm s n f z (Float.WF_of_WT w2) w1.1 ez]
      exact e

end Kanon
