import Bvr.Lib.Compare

/-! Comparisons (`bv_lt`, `bv_leq`), proved per alternative. -/

namespace Bvr

open Classical Lib

theorem bv_leq.r_udiv_big.a1.proof : bv_leq.r_udiv_big.a1.Stmt := by
  bvr_cmp_using [smtUDiv_ule_of_umulOverflow]

/-- `ite g p p` is `p`. -/
theorem refines_ite_same {FS g p} : Refines FS (.mk (.Triop .Ite g p p) .TBool) p := by
  refine Refines.denB (fun _ => rfl) (fun w => ?_) (fun w ρ b h => ?_)
  · obtain ⟨⟨-, -, e⟩, -, wp, -⟩ := WT_triop.1 w
    simp at e; exact ⟨wp, e.symm⟩
  · simp only [denB] at h
    split at h <;> simp_all

theorem bv_lt_zero.r_ite.a1.proof : bv_lt_zero.r_ite.a1.Stmt := by
  intro FS O hO g l r t
  simp only
  split
  · rename_i he
    simp only [equal, decide_eq_true_eq] at he
    refine Refines.trans ?_ (Refines.trans (Refines.ite (g := g) Refines.refl (hO.bv_lt_zero l)
      (he ▸ hO.bv_lt_zero r) (fun _ => rfl)) refines_ite_same)
    simp only [bvr_spec]
    apply Refines.denB (fun _ => rfl)
    · bvr_wt
    · bvr_sem
  · exact Refines.refl

end Bvr
