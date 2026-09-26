import Bvr.Lemmas

/-! Booleans: `b_and`, `b_or`, `b_not`, `b_ite`, `b_mk_exists`, `b_distinct`, `sem_eq_untyped`. -/

namespace Bvr

open Classical

theorem b_and.r_same.proof : b_and.r_same.Stmt := by
  sorry

theorem b_and.r_false_.proof : b_and.r_false_.Stmt := by
  intro FS O hO v1 v2 res h
  simp only [b_and.r_false_] at h
  rcases orElse_eq_some h with h | h <;> split at h <;> simp at h <;> subst h
  all_goals
    refine Refines.intro (fun w => ?_) (fun ρ v w w' e => ?_)
    · simp_all [b_and.spec, WT_and]
    · simp only [b_and.spec] at w e
      rw [eval_binop w] at e
      obtain ⟨_, _, _, w1, w2⟩ := WT_and.1 w
      simp_all [Ty.sort_eq_bool, evBinop, pand_eq_some, eval_bool] <;> grind

theorem b_and.r_true_l.proof : b_and.r_true_l.Stmt := by
  sorry

theorem b_and.r_true_r.proof : b_and.r_true_r.Stmt := by
  sorry

theorem b_and.r_not.proof : b_and.r_not.Stmt := by
  sorry

theorem b_and.r_and_l.proof : b_and.r_and_l.Stmt := by
  sorry

theorem b_and.r_and_r.proof : b_and.r_and_r.Stmt := by
  sorry

theorem b_and.r_or_l.proof : b_and.r_or_l.Stmt := by
  sorry

theorem b_and.r_or_r.proof : b_and.r_or_r.Stmt := by
  sorry

theorem b_and.r_eq_neq.proof : b_and.r_eq_neq.Stmt := by
  sorry

theorem b_and.r_eq_extracts.proof : b_and.r_eq_extracts.Stmt := by
  sorry

theorem b_and.r_upper_bounds.proof : b_and.r_upper_bounds.Stmt := by
  sorry

theorem b_and.r_lower_bounds.proof : b_and.r_lower_bounds.Stmt := by
  sorry

theorem b_and.r_default.proof : b_and.r_default.Stmt := by
  sorry

theorem b_or.r_same.proof : b_or.r_same.Stmt := by
  sorry

theorem b_or.r_true_.proof : b_or.r_true_.Stmt := by
  sorry

theorem b_or.r_false_l.proof : b_or.r_false_l.Stmt := by
  sorry

theorem b_or.r_false_r.proof : b_or.r_false_r.Stmt := by
  sorry

theorem b_or.r_not.proof : b_or.r_not.Stmt := by
  sorry

theorem b_or.r_lt_lt.proof : b_or.r_lt_lt.Stmt := by
  sorry

theorem b_or.r_lt_leq.proof : b_or.r_lt_leq.Stmt := by
  sorry

theorem b_or.r_or_l.proof : b_or.r_or_l.Stmt := by
  sorry

theorem b_or.r_or_r.proof : b_or.r_or_r.Stmt := by
  sorry

theorem b_or.r_and_l.proof : b_or.r_and_l.Stmt := by
  sorry

theorem b_or.r_and_r.proof : b_or.r_and_r.Stmt := by
  sorry

theorem b_or.r_complementary.proof : b_or.r_complementary.Stmt := by
  sorry

theorem b_or.r_bound_eq.proof : b_or.r_bound_eq.Stmt := by
  sorry

theorem b_or.r_eq_bound.proof : b_or.r_eq_bound.Stmt := by
  sorry

theorem b_or.r_upper_bounds.proof : b_or.r_upper_bounds.Stmt := by
  sorry

theorem b_or.r_lower_bounds.proof : b_or.r_lower_bounds.Stmt := by
  sorry

theorem b_or.r_default.proof : b_or.r_default.Stmt := by
  sorry

theorem b_not.r_true_.proof : b_not.r_true_.Stmt := by
  sorry

theorem b_not.r_false_.proof : b_not.r_false_.Stmt := by
  sorry

theorem b_not.r_not.proof : b_not.r_not.Stmt := by
  sorry

theorem b_not.r_lt.proof : b_not.r_lt.Stmt := by
  sorry

theorem b_not.r_leq.proof : b_not.r_leq.Stmt := by
  sorry

theorem b_not.r_or_.proof : b_not.r_or_.Stmt := by
  sorry

theorem b_not.r_and_.proof : b_not.r_and_.Stmt := by
  sorry

theorem b_not.r_ite.proof : b_not.r_ite.Stmt := by
  sorry

theorem b_not.r_eq_bit.proof : b_not.r_eq_bit.Stmt := by
  sorry

theorem b_not.r_distinct.proof : b_not.r_distinct.Stmt := by
  sorry

theorem b_not.r_default.proof : b_not.r_default.Stmt := by
  sorry

theorem b_ite.r_true_.proof : b_ite.r_true_.Stmt := by
  sorry

theorem b_ite.r_false_.proof : b_ite.r_false_.Stmt := by
  sorry

theorem b_ite.r_bool.proof : b_ite.r_bool.Stmt := by
  sorry

theorem b_ite.r_not_bool.proof : b_ite.r_not_bool.Stmt := by
  sorry

theorem b_ite.r_false_then.proof : b_ite.r_false_then.Stmt := by
  sorry

theorem b_ite.r_true_then.proof : b_ite.r_true_then.Stmt := by
  sorry

theorem b_ite.r_false_else.proof : b_ite.r_false_else.Stmt := by
  sorry

theorem b_ite.r_true_else.proof : b_ite.r_true_else.Stmt := by
  sorry

theorem b_ite.r_bv_of_bool.proof : b_ite.r_bv_of_bool.Stmt := by
  sorry

theorem b_ite.r_not_guard.proof : b_ite.r_not_guard.Stmt := by
  sorry

theorem b_ite.r_guard_then.proof : b_ite.r_guard_then.Stmt := by
  sorry

theorem b_ite.r_guard_else.proof : b_ite.r_guard_else.Stmt := by
  sorry

theorem b_ite.r_ite_then.proof : b_ite.r_ite_then.Stmt := by
  sorry

theorem b_ite.r_ite_else.proof : b_ite.r_ite_else.Stmt := by
  sorry

theorem b_ite.r_and_ite_then.proof : b_ite.r_and_ite_then.Stmt := by
  sorry

theorem b_ite.r_or_ite_else.proof : b_ite.r_or_ite_else.Stmt := by
  sorry

theorem b_ite.r_same.proof : b_ite.r_same.Stmt := by
  sorry

theorem b_ite.r_default.proof : b_ite.r_default.Stmt := by
  sorry

theorem b_mk_exists.r_empty.proof : b_mk_exists.r_empty.Stmt := by
  sorry

theorem b_mk_exists.r_default.proof : b_mk_exists.r_default.Stmt := by
  sorry

theorem sem_eq_untyped.r_main.proof : sem_eq_untyped.r_main.Stmt := by
  sorry

theorem b_distinct.r_small.proof : b_distinct.r_small.Stmt := by
  sorry

theorem b_distinct.r_default.proof : b_distinct.r_default.Stmt := by
  sorry

end Bvr
