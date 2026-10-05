import Kanon.Lib.Resize
import Kanon.Statements.Float.fmod

/-! The arms of `Float.fmod` that the default tactics do not prove. -/

namespace Kanon

open CoreMod

open Classical Lib

@[kanon_arm] theorem Float.fmod.r_lits.main.proof : Float.fmod.r_lits.main.Stmt := by
  intro FS O hO f1 T1 f2 T2
  have key : (Float.fmod.spec (.mk (.Float f1) T1) (.mk (.Float f2) T2)).WT →
      T1 = .TFloat f1.prec ∧ T2 = .TFloat f2.prec ∧ f1.WF ∧ f2.WF ∧ f1.prec = f2.prec := by
    intro w
    obtain ⟨_, _, wr, _⟩ := WT_op3.1 w
    obtain ⟨w0, w1, w2⟩ := WT_op2.1 wr
    obtain ⟨h1, h2⟩ := WT_float.1 w1
    obtain ⟨h3, h4⟩ := WT_float.1 w2
    simp only [Op2.WT, Term.ty_mk] at w0
    subst h1 h3
    simp only [Ty.TFloat.injEq] at w0
    exact ⟨rfl, rfl, h2, h4, w0.2.1.symm⟩
  refine Sem.Refines.intro_eval (fun w => ?_) (fun ρ v w w' e => ?_)
  · obtain ⟨hT, _, h1, h2, hp⟩ := key w
    have := hO.orc.fmod f1 f2 ⟨fun _ => none⟩ h1 h2 hp
    exact ⟨WT_float.2 ⟨by simp [this.1], this.2.1⟩,
      by simp [hT, this.1, Float.fmod.spec, Float.raw_fmod_of_rem]⟩
  · obtain ⟨hT, hT', h1, h2, hp⟩ := key w
    have := hO.orc.fmod f1 f2 ρ h1 h2 hp
    subst hT hT'
    rw [← eval] at e ⊢
    rw [eval_float w']
    simp only [Float.fmod.spec, Float.term, ty_eq, Term.ty_mk] at e this
    rw [this.2.2] at e; exact e

end Kanon
