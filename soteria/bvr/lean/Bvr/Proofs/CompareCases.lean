import Bvr.Lib.Compare

/-! Comparisons (`bv_lt`, `bv_leq`), proved per alternative. -/

namespace Bvr

open Classical Lib

theorem bv_lt.r_lits.a1.proof : bv_lt.r_lits.a1.Stmt := by
  bvr_cmp

theorem bv_lt.r_same.a1.proof : bv_lt.r_same.a1.Stmt := by
  bvr_cmp

theorem bv_lt.r_negs.a1.proof : bv_lt.r_negs.a1.Stmt := by
  bvr_cmp

theorem bv_lt.r_neg_l.a1.proof : bv_lt.r_neg_l.a1.Stmt := by
  bvr_cmp

theorem bv_lt.r_neg_r.a1.proof : bv_lt.r_neg_r.a1.Stmt := by
  bvr_cmp

theorem bv_lt.r_const_add.a1.proof : bv_lt.r_const_add.a1.Stmt := by
  bvr_cmp

theorem bv_lt.r_const_add.a2.proof : bv_lt.r_const_add.a2.Stmt := by
  bvr_cmp

theorem bv_lt.r_add_const.a1.proof : bv_lt.r_add_const.a1.Stmt := by
  bvr_cmp

theorem bv_lt.r_add_const.a2.proof : bv_lt.r_add_const.a2.Stmt := by
  bvr_cmp

theorem bv_lt.r_self_add_r.a1.proof : bv_lt.r_self_add_r.a1.Stmt := by
  bvr_cmp

theorem bv_lt.r_self_add_l.a1.proof : bv_lt.r_self_add_l.a1.Stmt := by
  bvr_cmp

theorem bv_lt.r_add_add.a1.proof : bv_lt.r_add_add.a1.Stmt := by
  bvr_cmp

theorem bv_lt.r_add_add.a2.proof : bv_lt.r_add_add.a2.Stmt := by
  bvr_cmp

theorem bv_lt.r_add_add.a3.proof : bv_lt.r_add_add.a3.Stmt := by
  bvr_cmp

theorem bv_lt.r_add_add.a4.proof : bv_lt.r_add_add.a4.Stmt := by
  bvr_cmp

theorem bv_lt.r_one.a1.proof : bv_lt.r_one.a1.Stmt := by
  bvr_cmp

theorem bv_lt.r_of_bool.a1.proof : bv_lt.r_of_bool.a1.Stmt := by
  bvr_cmp

theorem bv_lt.r_ite_l.a1.proof : bv_lt.r_ite_l.a1.Stmt := by
  bvr_cmp

theorem bv_lt.r_ite_r.a1.proof : bv_lt.r_ite_r.a1.Stmt := by
  bvr_cmp

theorem bv_lt.r_lt_zero.a1.proof : bv_lt.r_lt_zero.a1.Stmt := by
  intro FS O hO s v z T h
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at h
  obtain ⟨rfl, rfl, -⟩ := h
  exact refines_lt_zero_aux hO

theorem bv_lt.r_max_l.a1.proof : bv_lt.r_max_l.a1.Stmt := by
  bvr_cmp

theorem bv_lt.r_min_r.a1.proof : bv_lt.r_min_r.a1.Stmt := by
  bvr_cmp

theorem bv_lt.r_min_l.a1.proof : bv_lt.r_min_l.a1.Stmt := by
  bvr_cmp

theorem bv_lt.r_max_r.a1.proof : bv_lt.r_max_r.a1.Stmt := by
  bvr_cmp

set_option maxHeartbeats 1000000 in
theorem bv_lt.r_const_mul.a1.proof : bv_lt.r_const_mul.a1.Stmt := by
  bvr_cmp

set_option maxHeartbeats 1000000 in
theorem bv_lt.r_mul_const.a1.proof : bv_lt.r_mul_const.a1.Stmt := by
  bvr_cmp

theorem bv_lt.r_mul_mul.a1.proof : bv_lt.r_mul_mul.a1.Stmt := by
  bvr_cmp

theorem bv_lt.r_const_sub1.a1.proof : bv_lt.r_const_sub1.a1.Stmt := by
  bvr_cmp

theorem bv_lt.r_const_sub2.a1.proof : bv_lt.r_const_sub2.a1.Stmt := by
  bvr_cmp

theorem bv_lt.r_sub_const1.a1.proof : bv_lt.r_sub_const1.a1.Stmt := by
  bvr_cmp

theorem bv_lt.r_sub_const2.a1.proof : bv_lt.r_sub_const2.a1.Stmt := by
  bvr_cmp

theorem bv_lt.r_ub_r.a1.proof : bv_lt.r_ub_r.a1.Stmt := by
  bvr_cmp

theorem bv_lt.r_ub_l.a1.proof : bv_lt.r_ub_l.a1.Stmt := by
  bvr_cmp

theorem bv_lt.r_to_unsigned_l.a1.proof : bv_lt.r_to_unsigned_l.a1.Stmt := by
  bvr_cmp

theorem bv_lt.r_to_unsigned_r.a1.proof : bv_lt.r_to_unsigned_r.a1.Stmt := by
  bvr_cmp

theorem bv_lt.r_default.a1.proof : bv_lt.r_default.a1.Stmt := by
  bvr_cmp

theorem bv_leq.r_same.a1.proof : bv_leq.r_same.a1.Stmt := by
  bvr_cmp

theorem bv_leq.r_lits.a1.proof : bv_leq.r_lits.a1.Stmt := by
  bvr_cmp

theorem bv_leq.r_negs.a1.proof : bv_leq.r_negs.a1.Stmt := by
  bvr_cmp

theorem bv_leq.r_neg_l.a1.proof : bv_leq.r_neg_l.a1.Stmt := by
  bvr_cmp

theorem bv_leq.r_neg_r.a1.proof : bv_leq.r_neg_r.a1.Stmt := by
  bvr_cmp

theorem bv_leq.r_const_add.a1.proof : bv_leq.r_const_add.a1.Stmt := by
  bvr_cmp

theorem bv_leq.r_const_add.a2.proof : bv_leq.r_const_add.a2.Stmt := by
  bvr_cmp

theorem bv_leq.r_add_const.a1.proof : bv_leq.r_add_const.a1.Stmt := by
  bvr_cmp

theorem bv_leq.r_add_const.a2.proof : bv_leq.r_add_const.a2.Stmt := by
  bvr_cmp

theorem bv_leq.r_add_add.a1.proof : bv_leq.r_add_add.a1.Stmt := by
  bvr_cmp

theorem bv_leq.r_add_add.a2.proof : bv_leq.r_add_add.a2.Stmt := by
  bvr_cmp

theorem bv_leq.r_add_add.a3.proof : bv_leq.r_add_add.a3.Stmt := by
  bvr_cmp

theorem bv_leq.r_add_add.a4.proof : bv_leq.r_add_add.a4.Stmt := by
  bvr_cmp

theorem bv_leq.r_self_add_r.a1.proof : bv_leq.r_self_add_r.a1.Stmt := by
  bvr_cmp

theorem bv_leq.r_self_add_l.a1.proof : bv_leq.r_self_add_l.a1.Stmt := by
  bvr_cmp

theorem bv_leq.r_min_l.a1.proof : bv_leq.r_min_l.a1.Stmt := by
  bvr_cmp

theorem bv_leq.r_max_r.a1.proof : bv_leq.r_max_r.a1.Stmt := by
  bvr_cmp

set_option maxHeartbeats 1000000 in
theorem bv_leq.r_const_mul.a1.proof : bv_leq.r_const_mul.a1.Stmt := by
  bvr_cmp

set_option maxHeartbeats 1000000 in
theorem bv_leq.r_mul_const.a1.proof : bv_leq.r_mul_const.a1.Stmt := by
  bvr_cmp

theorem bv_leq.r_mul_mul.a1.proof : bv_leq.r_mul_mul.a1.Stmt := by
  bvr_cmp

theorem bv_leq.r_udiv_big.a1.proof : bv_leq.r_udiv_big.a1.Stmt := by
  bvr_cmp_using [smtUDiv_ule_of_umulOverflow]

theorem bv_leq.r_ite_l.a1.proof : bv_leq.r_ite_l.a1.Stmt := by
  bvr_cmp

theorem bv_leq.r_ite_r.a1.proof : bv_leq.r_ite_r.a1.Stmt := by
  bvr_cmp

theorem bv_leq.r_const_sub1.a1.proof : bv_leq.r_const_sub1.a1.Stmt := by
  bvr_cmp

theorem bv_leq.r_const_sub2.a1.proof : bv_leq.r_const_sub2.a1.Stmt := by
  bvr_cmp

theorem bv_leq.r_sub_const1.a1.proof : bv_leq.r_sub_const1.a1.Stmt := by
  bvr_cmp

theorem bv_leq.r_sub_const2.a1.proof : bv_leq.r_sub_const2.a1.Stmt := by
  bvr_cmp

theorem bv_leq.r_ub_r.a1.proof : bv_leq.r_ub_r.a1.Stmt := by
  bvr_cmp

theorem bv_leq.r_ub_l.a1.proof : bv_leq.r_ub_l.a1.Stmt := by
  bvr_cmp

theorem bv_leq.r_to_unsigned_l.a1.proof : bv_leq.r_to_unsigned_l.a1.Stmt := by
  bvr_cmp

theorem bv_leq.r_to_unsigned_r.a1.proof : bv_leq.r_to_unsigned_r.a1.Stmt := by
  bvr_cmp

theorem bv_leq.r_default.a1.proof : bv_leq.r_default.a1.Stmt := by
  bvr_cmp

end Bvr
