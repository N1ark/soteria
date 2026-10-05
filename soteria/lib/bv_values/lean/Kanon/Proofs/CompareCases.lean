import Kanon.Lib.Compare
import Kanon.Lib.Rule

/-! Comparisons (`bv_lt`, `bv_leq`), proved per alternative. -/

namespace Kanon

open Classical Lib

@[kanon_arm] theorem bv_leq.r_udiv_big.main.proof : bv_leq.r_udiv_big.main.Stmt := by
  kanon_cmp_using [smtUDiv_ule_of_umulOverflow]

/-- `ite g p p` is `p`. -/
theorem refines_ite_same {FS g p} : Refines FS (.mk (.Op3 .Ite g p p) .TBool) p := by
  refine Refines.denB (fun _ => rfl) (fun w => ?_) (fun w ρ b h => ?_)
  · obtain ⟨⟨-, -, e⟩, -, wp, -⟩ := WT_op3.1 w
    exact ⟨wp, e.symm⟩
  · simp only [denB] at h
    split at h <;> simp_all

@[kanon_arm] theorem bv_lt_zero.r_ite.main.proof : bv_lt_zero.r_ite.main.Stmt := by
  intro FS O hO g l r t
  simp only
  split
  · rename_i he
    simp only [decide_eq_true_eq] at he
    refine Sem.Refines.trans ?_ (Sem.Refines.trans (Refines.ite (g := g) Sem.Refines.refl
      (hO.bv_lt_zero l) (he ▸ hO.bv_lt_zero r) (fun _ => rfl)) refines_ite_same)
    simp only [kanon_spec]
    apply Refines.denB (fun _ => rfl)
    · kanon_wt_bv
    · kanon_sem_bv
  · exact Sem.Refines.refl

end Kanon
