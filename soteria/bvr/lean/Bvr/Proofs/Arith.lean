import Bvr.Lemmas

/-! Bit-vector arithmetic and overflow checks. -/

namespace Bvr

open Classical

theorem bv_add.r_lits.proof : bv_add.r_lits.Stmt := by
  sorry

theorem bv_add.r_neg_l.proof : bv_add.r_neg_l.Stmt := by
  sorry

theorem bv_add.r_neg_r.proof : bv_add.r_neg_r.Stmt := by
  sorry

theorem bv_add.r_zero_r.proof : bv_add.r_zero_r.Stmt := by
  sorry

theorem bv_add.r_zero_l.proof : bv_add.r_zero_l.Stmt := by
  sorry

theorem bv_add.r_not_one.proof : bv_add.r_not_one.Stmt := by
  sorry

theorem bv_add.r_add_const.proof : bv_add.r_add_const.Stmt := by
  sorry

theorem bv_add.r_sub_const_r.proof : bv_add.r_sub_const_r.Stmt := by
  sorry

theorem bv_add.r_sub_const_l.proof : bv_add.r_sub_const_l.Stmt := by
  sorry

theorem bv_add.r_sub_cancel_r.proof : bv_add.r_sub_cancel_r.Stmt := by
  sorry

theorem bv_add.r_sub_cancel_l.proof : bv_add.r_sub_cancel_l.Stmt := by
  sorry

theorem bv_add.r_add_sub.proof : bv_add.r_add_sub.Stmt := by
  sorry

theorem bv_add.r_factor.proof : bv_add.r_factor.Stmt := by
  sorry

theorem bv_add.r_factor_const.proof : bv_add.r_factor_const.Stmt := by
  sorry

theorem bv_add.r_ite.proof : bv_add.r_ite.Stmt := by
  sorry

theorem bv_add.r_default.proof : bv_add.r_default.Stmt := by
  sorry

theorem bv_sub.r_lits.proof : bv_sub.r_lits.Stmt := by
  sorry

theorem bv_sub.r_zero_r.proof : bv_sub.r_zero_r.Stmt := by
  sorry

theorem bv_sub.r_zero_l.proof : bv_sub.r_zero_l.Stmt := by
  sorry

theorem bv_sub.r_same.proof : bv_sub.r_same.Stmt := by
  sorry

theorem bv_sub.r_neg_r.proof : bv_sub.r_neg_r.Stmt := by
  sorry

theorem bv_sub.r_sub_const_l.proof : bv_sub.r_sub_const_l.Stmt := by
  sorry

theorem bv_sub.r_sub_const_r.proof : bv_sub.r_sub_const_r.Stmt := by
  sorry

theorem bv_sub.r_const_add.proof : bv_sub.r_const_add.Stmt := by
  sorry

theorem bv_sub.r_add_const.proof : bv_sub.r_add_const.Stmt := by
  sorry

theorem bv_sub.r_add_cancel_l.proof : bv_sub.r_add_cancel_l.Stmt := by
  sorry

theorem bv_sub.r_add_cancel_r.proof : bv_sub.r_add_cancel_r.Stmt := by
  sorry

theorem bv_sub.r_add_add.proof : bv_sub.r_add_add.Stmt := by
  sorry

theorem bv_sub.r_sub_sub.proof : bv_sub.r_sub_sub.Stmt := by
  sorry

theorem bv_sub.r_ite_ite.proof : bv_sub.r_ite_ite.Stmt := by
  sorry

theorem bv_sub.r_ite_l.proof : bv_sub.r_ite_l.Stmt := by
  sorry

theorem bv_sub.r_ite_r.proof : bv_sub.r_ite_r.Stmt := by
  sorry

theorem bv_sub.r_of_bool_l.proof : bv_sub.r_of_bool_l.Stmt := by
  sorry

theorem bv_sub.r_of_bool_r.proof : bv_sub.r_of_bool_r.Stmt := by
  sorry

theorem bv_sub.r_default.proof : bv_sub.r_default.Stmt := by
  sorry

theorem bv_neg.r_lit.proof : bv_neg.r_lit.Stmt := by
  sorry

theorem bv_neg.r_neg.proof : bv_neg.r_neg.Stmt := by
  sorry

theorem bv_neg.r_ite.proof : bv_neg.r_ite.Stmt := by
  sorry

theorem bv_neg.r_of_bool.proof : bv_neg.r_of_bool.Stmt := by
  sorry

theorem bv_neg.r_default.proof : bv_neg.r_default.Stmt := by
  sorry

theorem bv_mod.r_lits.proof : bv_mod.r_lits.Stmt := by
  sorry

theorem bv_mod.r_default.proof : bv_mod.r_default.Stmt := by
  sorry

theorem bv_rem.r_lits.proof : bv_rem.r_lits.Stmt := by
  sorry

theorem bv_rem.r_zero_l.proof : bv_rem.r_zero_l.Stmt := by
  sorry

theorem bv_rem.r_one_r.proof : bv_rem.r_one_r.Stmt := by
  sorry

theorem bv_rem.r_pow2.proof : bv_rem.r_pow2.Stmt := by
  sorry

theorem bv_rem.r_add.proof : bv_rem.r_add.Stmt := by
  sorry

theorem bv_rem.r_rem_rem.proof : bv_rem.r_rem_rem.Stmt := by
  sorry

theorem bv_rem.r_default.proof : bv_rem.r_default.Stmt := by
  sorry

theorem bv_mul.r_lits.proof : bv_mul.r_lits.Stmt := by
  sorry

theorem bv_mul.r_one_r.proof : bv_mul.r_one_r.Stmt := by
  sorry

theorem bv_mul.r_one_l.proof : bv_mul.r_one_l.Stmt := by
  sorry

theorem bv_mul.r_zero_r.proof : bv_mul.r_zero_r.Stmt := by
  sorry

theorem bv_mul.r_zero_l.proof : bv_mul.r_zero_l.Stmt := by
  sorry

theorem bv_mul.r_neg.proof : bv_mul.r_neg.Stmt := by
  sorry

theorem bv_mul.r_mul_const.proof : bv_mul.r_mul_const.Stmt := by
  sorry

theorem bv_mul.r_ite.proof : bv_mul.r_ite.Stmt := by
  sorry

theorem bv_mul.r_default.proof : bv_mul.r_default.Stmt := by
  sorry

theorem bv_div.r_lits.proof : bv_div.r_lits.Stmt := by
  sorry

theorem bv_div.r_one.proof : bv_div.r_one.Stmt := by
  sorry

theorem bv_div.r_mul_lits.proof : bv_div.r_mul_lits.Stmt := by
  sorry

theorem bv_div.r_mul_div.proof : bv_div.r_mul_div.Stmt := by
  sorry

theorem bv_div.r_div_mul.proof : bv_div.r_div_mul.Stmt := by
  sorry

theorem bv_div.r_div_div.proof : bv_div.r_div_div.Stmt := by
  sorry

theorem bv_div.r_zext.proof : bv_div.r_zext.Stmt := by
  sorry

theorem bv_div.r_default.proof : bv_div.r_default.Stmt := by
  sorry

theorem bv_add_overflows.r_lits.proof : bv_add_overflows.r_lits.Stmt := by
  sorry

theorem bv_add_overflows.r_zero.proof : bv_add_overflows.r_zero.Stmt := by
  sorry

theorem bv_add_overflows.r_size1.proof : bv_add_overflows.r_size1.Stmt := by
  sorry

theorem bv_add_overflows.r_unsigned.proof : bv_add_overflows.r_unsigned.Stmt := by
  sorry

theorem bv_add_overflows.r_signed.proof : bv_add_overflows.r_signed.Stmt := by
  sorry

theorem bv_add_overflows.r_of_bools.proof : bv_add_overflows.r_of_bools.Stmt := by
  sorry

theorem bv_add_overflows.r_of_bool.proof : bv_add_overflows.r_of_bool.Stmt := by
  sorry

theorem bv_add_overflows.r_default.proof : bv_add_overflows.r_default.Stmt := by
  sorry

theorem bv_mul_overflows.r_lits.proof : bv_mul_overflows.r_lits.Stmt := by
  sorry

theorem bv_mul_overflows.r_size1.proof : bv_mul_overflows.r_size1.Stmt := by
  sorry

theorem bv_mul_overflows.r_msb.proof : bv_mul_overflows.r_msb.Stmt := by
  sorry

theorem bv_mul_overflows.r_const.proof : bv_mul_overflows.r_const.Stmt := by
  sorry

theorem bv_mul_overflows.r_div.proof : bv_mul_overflows.r_div.Stmt := by
  sorry

theorem bv_mul_overflows.r_default.proof : bv_mul_overflows.r_default.Stmt := by
  sorry

theorem bv_neg_overflows.r_main.proof : bv_neg_overflows.r_main.Stmt := by
  sorry

theorem bv_sub_overflows.r_lits.proof : bv_sub_overflows.r_lits.Stmt := by
  sorry

theorem bv_sub_overflows.r_same.proof : bv_sub_overflows.r_same.Stmt := by
  sorry

theorem bv_sub_overflows.r_unsigned.proof : bv_sub_overflows.r_unsigned.Stmt := by
  sorry

theorem bv_sub_overflows.r_default.proof : bv_sub_overflows.r_default.Stmt := by
  sorry

end Bvr
