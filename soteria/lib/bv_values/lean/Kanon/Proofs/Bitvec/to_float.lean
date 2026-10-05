import Kanon.Lib.Resize
import Kanon.Statements.Bitvec.to_float

/-! The arms of `Bitvec.to_float` that the default tactics do not prove. -/

namespace Kanon

open Classical Lib

@[kanon_arm] theorem Bitvec.to_float.r_lit.main.proof : Bitvec.to_float.r_lit.main.Stmt := by
  intro FS O hO rm s p z T
  have key : (Bitvec.to_float.spec rm s p (.mk (.BitVec z) T)).WT →
      ∃ n : Int, 0 < n ∧ T = .TBitVector n ∧ 0 ≤ z ∧ z < 2 ^ n.toNat := by
    intro w
    have ⟨w1, w2⟩ := WT_op1.1 w
    simp [Op1.WT] at w1
    obtain ⟨n, hn, rfl⟩ := w1
    exact ⟨n, hn, rfl, (WT_bitVec_bv.1 w2).2⟩
  simp only [size_eq, Term.ty_mk]
  rcases ez : O.orc.f_of_int rm s p (size_of_ty T) z with _ | f
  · simp [firstSome]; exact Sem.Refines.refl
  · simp [firstSome]
    refine Sem.Refines.intro_eval (fun w => ?_) (fun ρ v w w' e => ?_)
    all_goals obtain ⟨n, hn, rfl, h0, h1⟩ := key w
    all_goals obtain ⟨hp, hf, he⟩ := hO.orc.of_int rm s p n z f hn h0 h1 ez
    · refine ⟨?_, by simp [Bitvec.to_float.spec, hp]⟩
      simp only [Term.WT, hp]; exact ⟨trivial, by simpa [Float.WF, hp] using hf⟩
    · rw [← eval] at e ⊢
      rw [Bitvec.to_float.spec, eval_op1 w, eval_bitVec' (WT_op1.1 w).2 rfl, he] at e
      rw [eval_eq_ev w']; simp only [ev]; exact e

end Kanon
