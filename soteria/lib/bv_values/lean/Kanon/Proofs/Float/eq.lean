import Kanon.Lib.Resize
import Kanon.Statements.Float.eq

/-! The arms of `Float.eq` that the default tactics do not prove. -/

namespace Kanon

open CoreMod

open Classical Lib

@[kanon_arm] theorem Float.eq.r_same.main.proof : Float.eq.r_same.main.Stmt := by
  intro FS O hO v1 v2 h
  simp only [decide_eq_true_eq] at h; subst h
  refine Sem.Refines.trans ?_ (Refines.b_not hO (hO.float_is_floatclass .NaN v1))
  refine Sem.Refines.intro_eval (fun w => ?_) (fun ρ v w w' e => ?_)
  · obtain ⟨hp, _, _, w1, _⟩ := (WT_fcmp (Or.inl rfl)).1 w
    refine ⟨WT_op1.2 ⟨by simp [Op1.WT, Float.is_floatclass.spec],
      WT_op1.2 ⟨by simpa [Op1.WT] using hp, w1⟩⟩, rfl⟩
  · have ⟨_, w1⟩ := WT_op1.1 w'
    rw [← eval] at e ⊢
    rw [Float.eq.spec, eval_op2 w] at e
    rw [Bool.not_.spec, eval_op1 w', Float.is_floatclass.spec, eval_op1 w1]
    simp only [evOp2, fBin_eq_some] at e
    obtain ⟨p, x, y, h1, h2, h3⟩ := e
    rw [h1] at h2; cases h2
    rw [h1]; simp at h3; simp [evOp1, ← h3, FBits.isClass]

@[kanon_arm] theorem Float.eq.r_lit.main.proof : Float.eq.r_lit.main.Stmt := by
  intro FS O hO v2 f T
  exact Refines.feq_lit hO (hO.bool_eq _ _)

@[kanon_arm] theorem Float.eq.r_default.main.proof : Float.eq.r_default.main.Stmt := by
  intro FS O hO v1 v2
  simp only [Float.eq.spec, mk_commut_binop]
  split
  · exact Sem.Refines.refl
  · exact Refines.comm (by simp [Op2.Comm]) fun _ => rfl

end Kanon
