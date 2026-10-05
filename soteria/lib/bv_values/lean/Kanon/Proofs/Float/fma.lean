import Kanon.Lib.Resize
import Kanon.Statements.Float.fma

/-! The arms of `Float.fma` that the default tactics do not prove. -/

namespace Kanon

open CoreMod

open Classical Lib

@[kanon_arm] theorem Float.fma.r_lits.main.proof : Float.fma.r_lits.main.Stmt := by
  intro FS O hO fa Ta fb Tb fc Tc
  have key : (Float.fma.spec (.mk (.Float fa) Ta) (.mk (.Float fb) Tb) (.mk (.Float fc) Tc)).WT →
      Ta = .TFloat fa.prec ∧ fa.WF ∧ fb.WF ∧ fc.WF ∧ fa.prec = fb.prec ∧ fa.prec = fc.prec := by
    intro w
    obtain ⟨w0, w1, w2, w3⟩ := WT_op3.1 w
    obtain ⟨h1, h2⟩ := WT_float.1 w1
    obtain ⟨h3, h4⟩ := WT_float.1 w2
    obtain ⟨h5, h6⟩ := WT_float.1 w3
    simp only [Op3.WT, Term.ty_mk] at w0
    subst h1 h3 h5
    simp only [Ty.TFloat.injEq] at w0
    exact ⟨rfl, h2, h4, h6, w0.2.1.symm, w0.2.2.1.symm⟩
  refine Sem.Refines.intro_eval (fun w => ?_) (fun ρ v w w' e => ?_)
  · obtain ⟨hT, h1, h2, h3, hp, hp'⟩ := key w
    have := hO.orc.fma fa fb fc h1 h2 h3 hp hp'
    exact ⟨WT_float.2 ⟨by simp [this.1], this.2.1⟩, by simp [hT, this.1, Float.fma.spec]⟩
  · obtain ⟨hT, h1, h2, h3, hp, hp'⟩ := key w
    have := hO.orc.fma fa fb fc h1 h2 h3 hp hp'
    obtain ⟨_, w1, w2, w3⟩ := WT_op3.1 w
    rw [← eval] at e ⊢
    rw [Float.fma.spec, eval_fma w, eval_float w1, eval_float w2, eval_float w3, this.2.2] at e
    rw [eval_float w']; exact e

end Kanon
