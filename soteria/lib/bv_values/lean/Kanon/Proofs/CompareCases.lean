import Kanon.Lib.Compare

/-! Comparisons (`bv_lt`, `bv_leq`), proved per alternative. -/

namespace Kanon

open Classical Lib

@[kanon_arm] theorem bv_leq.r_udiv_big.main.proof : bv_leq.r_udiv_big.main.Stmt := by
  kanon_cmp_using [smtUDiv_ule_of_umulOverflow]

/-- `ite g p p` is `p`. -/
theorem refines_ite_same {FS g p} : Refines FS (.mk (.Triop .Ite g p p) .TBool) p := by
  refine Refines.denB (fun _ => rfl) (fun w => ?_) (fun w ρ b h => ?_)
  · obtain ⟨⟨-, -, e⟩, -, wp, -⟩ := WT_triop.1 w
    simp at e; exact ⟨wp, e.symm⟩
  · simp only [denB] at h
    split at h <;> simp_all

@[kanon_arm] theorem bv_lt_zero.r_ite.main.proof : bv_lt_zero.r_ite.main.Stmt := by
  intro FS O hO g l r t
  simp only
  split
  · rename_i he
    simp only [equal, decide_eq_true_eq] at he
    refine Refines.trans ?_ (Refines.trans (Refines.ite (g := g) Refines.refl (hO.bv_lt_zero l)
      (he ▸ hO.bv_lt_zero r) (fun _ => rfl)) refines_ite_same)
    simp only [kanon_spec]
    apply Refines.denB (fun _ => rfl)
    · kanon_wt
    · kanon_sem
  · exact Refines.refl

end Kanon
