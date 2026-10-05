import Kanon.Lib.Compare
import Kanon.Lib.Rule
import Kanon.Statements.Bitvec.lt_zero

/-! The arms of `Bitvec.lt_zero` that the default tactics do not prove. -/

namespace Kanon

open CoreMod

open Classical Lib

/-- `ite g p p` is `p`. -/
theorem refines_ite_same {FS g p} : Refines FS (.mk (.Op3 .Ite g p p) .TBool) p := by
  refine Refines.denB (fun _ => rfl) (fun w => ?_) (fun w ρ b h => ?_)
  · obtain ⟨⟨-, -, e⟩, -, wp, -⟩ := WT_op3.1 w
    exact ⟨wp, e.symm⟩
  · simp only [denB] at h
    split at h <;> simp_all

@[kanon_arm] theorem Bitvec.lt_zero.r_ite.main.proof : Bitvec.lt_zero.r_ite.main.Stmt := by
  intro FS O hO g l r t
  simp only
  split
  · rename_i he
    simp only [decide_eq_true_eq] at he
    refine Sem.Refines.trans ?_ (Sem.Refines.trans (Refines.ite (g := g) Sem.Refines.refl
      (hO.bitvec_lt_zero l) (he ▸ hO.bitvec_lt_zero r) (fun _ => rfl)) refines_ite_same)
    simp only [kanon_spec]
    apply Refines.denB (fun _ => rfl)
    · kanon_wt_bv
    · kanon_sem_bv
  · exact Sem.Refines.refl

end Kanon
