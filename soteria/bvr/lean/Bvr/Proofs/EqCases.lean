import Bvr.Lib.Eq

/-! Equality and the overflow checks, proved per alternative. -/

namespace Bvr

open Classical Lib SemEq

theorem sem_eq.r_mul_const.a1.proof : sem_eq.r_mul_const.a1.Stmt := by
  bvr_rule_lift
  all_goals
    refine Refines.eq_mul_const (by simp only [is_checked, Bool.or_eq_true]; assumption)
      (fun W hW hx wx hs => ?_) (fun W N M X ρ hW hx hs hn hm ex => ?_)
  all_goals first
    | (simp [WT_eq, hx, wx, bv_zero, mk_masked, WT_bitVec_bv, hW, emod_two_pow_nonneg,
        emod_two_pow_lt]; done)
    | skip
  all_goals simp only [hn, hm, hs, bv_zero, mk_masked, v_false, denB_of_bool, denB_eq_lit hW hx ex,
    tdiv, divisible, decide_eq_true_eq, Bool.and_eq_true] at *
  all_goals (try rw [zshiftl_one_pred hW] at *)
  all_goals (try rw [zshiftl_one_nat] at *)
  all_goals simp only [denB, Option.some.injEq, decide_eq_decide, Int.toNat_natCast,
    false_eq_decide, BitVec.ofInt_emod_two_pow] at *
  all_goals first
    | (simp_all; done)
    | exact mulc_zero ‹_› ‹_›
    | exact mulc_fits hW ‹_› ‹_› (by simp_all)
    | exact mulc_nofit ‹_› ‹_› (by simp_all)
    | exact mulc_nodvd ‹_›

theorem sem_eq.r_mul_cancel.a1.proof : sem_eq.r_mul_cancel.a1.Stmt := by
  bvr_rule_b_sem
  all_goals first
    | (rw [← mul_cancel_flags ‹_› ‹_› ‹_›]; assumption)
    | (rw [← mul_cancel_flags (b := ‹BitVec _›) ‹_› ‹_› ‹_›]; assumption)

theorem sem_eq.r_zext_const.a1.proof : sem_eq.r_zext_const.a1.Stmt := by
  bvr_rule_b_sem
  all_goals simp_all [zext_mask, setWidth_eq_iff'] <;> omega

theorem sem_eq.r_ite_concat.a1.proof : sem_eq.r_ite_concat.a1.Stmt := by
  bvr_rule_b_arith

theorem sem_eq.r_msb.a1.proof : sem_eq.r_msb.a1.Stmt := by
  intro FS O hO v1 v2 h
  simp only [Bool.and_eq_true, decide_eq_true_eq, ty_eq] at h
  simp only [bvr_spec]
  bvr_lift_body
  exact Refines.eq_low h.1 h.2.2.1 (le_zmax_left _ _) (le_zmax_right _ _) h.2.2.2

theorem bv_rem.r_pow2.a1.proof : bv_rem.r_pow2.a1.Stmt := by
  intro FS O hO signed v1 r__z r__T h
  simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at h
  obtain ⟨rfl, hp, h1⟩ := h
  simp only [bvr_spec]
  bvr_lift_body
  exact Refines.rem_pow2 hp h1

theorem bv_mul_overflows.r_msb.a1.proof : bv_mul_overflows.r_msb.a1.Stmt := by
  intro FS O hO signed v1 v2 h
  exact Refines.mulOvf_msb h

end Bvr
