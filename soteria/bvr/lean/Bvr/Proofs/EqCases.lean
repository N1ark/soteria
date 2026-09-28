import Bvr.Lib.Eq

/-! Equality and the overflow checks, proved per alternative. -/

namespace Bvr

open Classical Lib SemEq

theorem sem_eq.r_same.a1.proof : sem_eq.r_same.a1.Stmt := by
  bvr_rule_b

theorem sem_eq.r_bools.a1.proof : sem_eq.r_bools.a1.Stmt := by
  bvr_rule_b

theorem sem_eq.r_ptrs.a1.proof : sem_eq.r_ptrs.a1.Stmt := by
  bvr_rule_b

theorem sem_eq.r_bvs.a1.proof : sem_eq.r_bvs.a1.Stmt := by
  bvr_rule_b

theorem sem_eq.r_floats.a1.proof : sem_eq.r_floats.a1.Stmt := by
  bvr_rule_b

theorem sem_eq.r_neg_r.a1.proof : sem_eq.r_neg_r.a1.Stmt := by
  bvr_rule_b

theorem sem_eq.r_neg_l.a1.proof : sem_eq.r_neg_l.a1.Stmt := by
  bvr_rule_b

theorem sem_eq.r_not_r.a1.proof : sem_eq.r_not_r.a1.Stmt := by
  bvr_rule_b

theorem sem_eq.r_not_l.a1.proof : sem_eq.r_not_l.a1.Stmt := by
  bvr_rule_b

theorem sem_eq.r_add_const_r.a1.proof : sem_eq.r_add_const_r.a1.Stmt := by
  bvr_rule_b

theorem sem_eq.r_add_const_l.a1.proof : sem_eq.r_add_const_l.a1.Stmt := by
  bvr_rule_b

theorem sem_eq.r_sub_const_r1.a1.proof : sem_eq.r_sub_const_r1.a1.Stmt := by
  bvr_rule_b

theorem sem_eq.r_sub_const_r2.a1.proof : sem_eq.r_sub_const_r2.a1.Stmt := by
  bvr_rule_b

theorem sem_eq.r_sub_const_l1.a1.proof : sem_eq.r_sub_const_l1.a1.Stmt := by
  bvr_rule_b

theorem sem_eq.r_sub_const_l2.a1.proof : sem_eq.r_sub_const_l2.a1.Stmt := by
  bvr_rule_b

theorem sem_eq.r_self_add_r.a1.proof : sem_eq.r_self_add_r.a1.Stmt := by
  bvr_rule_b

theorem sem_eq.r_self_add_l.a1.proof : sem_eq.r_self_add_l.a1.Stmt := by
  bvr_rule_b

theorem sem_eq.r_add_add.a1.proof : sem_eq.r_add_add.a1.Stmt := by
  bvr_rule_b

theorem sem_eq.r_mul_const.a1.proof : sem_eq.r_mul_const.a1.Stmt := by
  bvr_lift_b
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

theorem sem_eq.r_ite_ite.a1.proof : sem_eq.r_ite_ite.a1.Stmt := by
  bvr_rule_b

theorem sem_eq.r_mul_cancel.a1.proof : sem_eq.r_mul_cancel.a1.Stmt := by
  bvr_rule_b_sem
  all_goals first
    | (rw [← mul_cancel_flags ‹_› ‹_› ‹_›]; assumption)
    | (rw [← mul_cancel_flags (b := ‹BitVec _›) ‹_› ‹_› ‹_›]; assumption)

theorem sem_eq.r_or_zero.a1.proof : sem_eq.r_or_zero.a1.Stmt := by
  bvr_rule_b

theorem sem_eq.r_or_zero.a2.proof : sem_eq.r_or_zero.a2.Stmt := by
  bvr_rule_b

theorem sem_eq.r_and_mask.a1.proof : sem_eq.r_and_mask.a1.Stmt := by
  bvr_rule_b

theorem sem_eq.r_concat_const.a1.proof : sem_eq.r_concat_const.a1.Stmt := by
  bvr_rule_b

theorem sem_eq.r_zext_const.a1.proof : sem_eq.r_zext_const.a1.Stmt := by
  bvr_rule_b_sem
  all_goals simp_all [zext_mask, setWidth_eq_iff'] <;> omega

theorem sem_eq.r_ite_concat.a1.proof : sem_eq.r_ite_concat.a1.Stmt := by
  bvr_rule_b_arith

theorem sem_eq.r_concat_concat.a1.proof : sem_eq.r_concat_concat.a1.Stmt := by
  bvr_rule_b

theorem sem_eq.r_ite_const_l.a1.proof : sem_eq.r_ite_const_l.a1.Stmt := by
  bvr_rule_b

theorem sem_eq.r_ite_const_l.a2.proof : sem_eq.r_ite_const_l.a2.Stmt := by
  bvr_rule_b

theorem sem_eq.r_ite_const_r.a1.proof : sem_eq.r_ite_const_r.a1.Stmt := by
  bvr_rule_b

theorem sem_eq.r_ite_const_r.a2.proof : sem_eq.r_ite_const_r.a2.Stmt := by
  bvr_rule_b

theorem sem_eq.r_false_l.a1.proof : sem_eq.r_false_l.a1.Stmt := by
  bvr_rule_b

theorem sem_eq.r_false_r.a1.proof : sem_eq.r_false_r.a1.Stmt := by
  bvr_rule_b

theorem sem_eq.r_true_l.a1.proof : sem_eq.r_true_l.a1.Stmt := by
  bvr_rule_b

theorem sem_eq.r_true_r.a1.proof : sem_eq.r_true_r.a1.Stmt := by
  bvr_rule_b

theorem sem_eq.r_of_bools.a1.proof : sem_eq.r_of_bools.a1.Stmt := by
  bvr_rule_b

theorem sem_eq.r_nots.a1.proof : sem_eq.r_nots.a1.Stmt := by
  bvr_rule_b

theorem sem_eq.r_of_bool_const.a1.proof : sem_eq.r_of_bool_const.a1.Stmt := by
  bvr_rule_b

theorem sem_eq.r_msb.a1.proof : sem_eq.r_msb.a1.Stmt := by
  intro FS O hO v1 v2 h
  simp only [Bool.and_eq_true, decide_eq_true_eq, ty_eq] at h
  simp only [bvr_spec]
  bvr_lift_body
  exact Refines.eq_low h.1 h.2.2.1 (le_zmax_left _ _) (le_zmax_right _ _) h.2.2.2

theorem sem_eq.r_default.a1.proof : sem_eq.r_default.a1.Stmt := by
  bvr_rule_b

theorem bv_neg.r_lit.a1.proof : bv_neg.r_lit.a1.Stmt := by
  bvr_rule_b

theorem bv_neg.r_neg.a1.proof : bv_neg.r_neg.a1.Stmt := by
  bvr_rule_b

theorem bv_neg.r_ite.a1.proof : bv_neg.r_ite.a1.Stmt := by
  bvr_rule_b

theorem bv_neg.r_of_bool.a1.proof : bv_neg.r_of_bool.a1.Stmt := by
  bvr_rule_b

theorem bv_neg.r_default.a1.proof : bv_neg.r_default.a1.Stmt := by
  bvr_rule_b

theorem bv_mod.r_lits.a1.proof : bv_mod.r_lits.a1.Stmt := by
  bvr_rule_b

theorem bv_mod.r_default.a1.proof : bv_mod.r_default.a1.Stmt := by
  bvr_rule_b

theorem bv_rem.r_lits.a1.proof : bv_rem.r_lits.a1.Stmt := by
  bvr_rule_b

theorem bv_rem.r_zero_l.a1.proof : bv_rem.r_zero_l.a1.Stmt := by
  bvr_rule_b

theorem bv_rem.r_one_r.a1.proof : bv_rem.r_one_r.a1.Stmt := by
  bvr_rule_b

theorem bv_rem.r_pow2.a1.proof : bv_rem.r_pow2.a1.Stmt := by
  intro FS O hO signed v1 r__z r__T h
  simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at h
  obtain ⟨rfl, hp, h1⟩ := h
  simp only [bvr_spec]
  bvr_lift_body
  exact Refines.rem_pow2 hp h1

theorem bv_rem.r_add.a1.proof : bv_rem.r_add.a1.Stmt := by
  bvr_rule_b

theorem bv_rem.r_rem_rem.a1.proof : bv_rem.r_rem_rem.a1.Stmt := by
  bvr_rule_b

theorem bv_rem.r_default.a1.proof : bv_rem.r_default.a1.Stmt := by
  bvr_rule_b

theorem bv_add_overflows.r_lits.a1.proof : bv_add_overflows.r_lits.a1.Stmt := by
  bvr_rule_b

theorem bv_add_overflows.r_zero.a1.proof : bv_add_overflows.r_zero.a1.Stmt := by
  bvr_rule_b

theorem bv_add_overflows.r_zero.a2.proof : bv_add_overflows.r_zero.a2.Stmt := by
  bvr_rule_b

theorem bv_add_overflows.r_size1.a1.proof : bv_add_overflows.r_size1.a1.Stmt := by
  bvr_rule_b

theorem bv_add_overflows.r_unsigned.a1.proof : bv_add_overflows.r_unsigned.a1.Stmt := by
  bvr_rule_b

theorem bv_add_overflows.r_unsigned.a2.proof : bv_add_overflows.r_unsigned.a2.Stmt := by
  bvr_rule_b

theorem bv_add_overflows.r_signed.a1.proof : bv_add_overflows.r_signed.a1.Stmt := by
  bvr_rule_b

theorem bv_add_overflows.r_signed.a2.proof : bv_add_overflows.r_signed.a2.Stmt := by
  bvr_rule_b

theorem bv_add_overflows.r_of_bools.a1.proof : bv_add_overflows.r_of_bools.a1.Stmt := by
  bvr_rule_b

theorem bv_add_overflows.r_of_bool.a1.proof : bv_add_overflows.r_of_bool.a1.Stmt := by
  bvr_rule_b

theorem bv_add_overflows.r_of_bool.a2.proof : bv_add_overflows.r_of_bool.a2.Stmt := by
  bvr_rule_b

theorem bv_add_overflows.r_default.a1.proof : bv_add_overflows.r_default.a1.Stmt := by
  bvr_rule_b

theorem bv_mul_overflows.r_lits.a1.proof : bv_mul_overflows.r_lits.a1.Stmt := by
  bvr_rule_b

theorem bv_mul_overflows.r_size1.a1.proof : bv_mul_overflows.r_size1.a1.Stmt := by
  bvr_rule_b

theorem bv_mul_overflows.r_msb.a1.proof : bv_mul_overflows.r_msb.a1.Stmt := by
  intro FS O hO signed v1 v2 h
  exact Refines.mulOvf_msb h

theorem bv_mul_overflows.r_const.a1.proof : bv_mul_overflows.r_const.a1.Stmt := by
  bvr_rule_b

theorem bv_mul_overflows.r_const.a2.proof : bv_mul_overflows.r_const.a2.Stmt := by
  bvr_rule_b

theorem bv_mul_overflows.r_div.a1.proof : bv_mul_overflows.r_div.a1.Stmt := by
  bvr_rule_b

theorem bv_mul_overflows.r_div.a2.proof : bv_mul_overflows.r_div.a2.Stmt := by
  bvr_rule_b

theorem bv_mul_overflows.r_default.a1.proof : bv_mul_overflows.r_default.a1.Stmt := by
  bvr_rule_b

theorem bv_neg_overflows.r_main.a1.proof : bv_neg_overflows.r_main.a1.Stmt := by
  bvr_rule_b

theorem bv_sub_overflows.r_lits.a1.proof : bv_sub_overflows.r_lits.a1.Stmt := by
  bvr_rule_b

theorem bv_sub_overflows.r_same.a1.proof : bv_sub_overflows.r_same.a1.Stmt := by
  bvr_rule_b

theorem bv_sub_overflows.r_unsigned.a1.proof : bv_sub_overflows.r_unsigned.a1.Stmt := by
  bvr_rule_b

theorem bv_sub_overflows.r_default.a1.proof : bv_sub_overflows.r_default.a1.Stmt := by
  bvr_rule_b

end Bvr
