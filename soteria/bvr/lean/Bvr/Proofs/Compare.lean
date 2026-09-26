import Bvr.Proofs.CompareLemmas

/-! Bit-vector comparisons (`bv_lt`, `bv_leq`). -/

namespace Bvr

open Classical CompareL

theorem bv_lt.r_lits.proof : bv_lt.r_lits.Stmt := by
  sorry

theorem bv_lt.r_same.proof : bv_lt.r_same.Stmt := by
  sorry

theorem bv_lt.r_negs.proof : bv_lt.r_negs.Stmt := by
  sorry

theorem bv_lt.r_neg_l.proof : bv_lt.r_neg_l.Stmt := by
  sorry

theorem bv_lt.r_neg_r.proof : bv_lt.r_neg_r.Stmt := by
  sorry

theorem bv_lt.r_const_add.proof : bv_lt.r_const_add.Stmt := by
  sorry

theorem bv_lt.r_add_const.proof : bv_lt.r_add_const.Stmt := by
  sorry

theorem bv_lt.r_self_add_r.proof : bv_lt.r_self_add_r.Stmt := by
  sorry

theorem bv_lt.r_self_add_l.proof : bv_lt.r_self_add_l.Stmt := by
  sorry

theorem bv_lt.r_add_add.proof : bv_lt.r_add_add.Stmt := by
  sorry

theorem bv_lt.r_one.proof : bv_lt.r_one.Stmt := by
  sorry

theorem bv_lt.r_of_bool.proof : bv_lt.r_of_bool.Stmt := by
  sorry

theorem bv_lt.r_ite_l.proof : bv_lt.r_ite_l.Stmt := by
  sorry

theorem bv_lt.r_ite_r.proof : bv_lt.r_ite_r.Stmt := by
  sorry

theorem bv_lt.r_lt_zero.proof : bv_lt.r_lt_zero.Stmt := by
  sorry

theorem bv_lt.r_max_l.proof : bv_lt.r_max_l.Stmt := by
  sorry

theorem bv_lt.r_min_r.proof : bv_lt.r_min_r.Stmt := by
  sorry

theorem bv_lt.r_min_l.proof : bv_lt.r_min_l.Stmt := by
  sorry

theorem bv_lt.r_max_r.proof : bv_lt.r_max_r.Stmt := by
  sorry

theorem bv_lt.r_const_mul.proof : bv_lt.r_const_mul.Stmt := by
  sorry

theorem bv_lt.r_mul_const.proof : bv_lt.r_mul_const.Stmt := by
  sorry

theorem bv_lt.r_mul_mul.proof : bv_lt.r_mul_mul.Stmt := by
  sorry

theorem bv_lt.r_const_sub1.proof : bv_lt.r_const_sub1.Stmt := by
  sorry

theorem bv_lt.r_const_sub2.proof : bv_lt.r_const_sub2.Stmt := by
  sorry

theorem bv_lt.r_sub_const1.proof : bv_lt.r_sub_const1.Stmt := by
  sorry

theorem bv_lt.r_sub_const2.proof : bv_lt.r_sub_const2.Stmt := by
  sorry

theorem bv_lt.r_ub_r.proof : bv_lt.r_ub_r.Stmt := by
  sorry

theorem bv_lt.r_ub_l.proof : bv_lt.r_ub_l.Stmt := by
  sorry

theorem bv_lt.r_to_unsigned_l.proof : bv_lt.r_to_unsigned_l.Stmt := by
  sorry

theorem bv_lt.r_to_unsigned_r.proof : bv_lt.r_to_unsigned_r.Stmt := by
  sorry

theorem bv_lt.r_default.proof : bv_lt.r_default.Stmt := by
  sorry

theorem bv_leq.r_same.proof : bv_leq.r_same.Stmt := by
  sorry

theorem bv_leq.r_lits.proof : bv_leq.r_lits.Stmt := by
  sorry

theorem bv_leq.r_negs.proof : bv_leq.r_negs.Stmt := by
  sorry

theorem bv_leq.r_neg_l.proof : bv_leq.r_neg_l.Stmt := by
  sorry

theorem bv_leq.r_neg_r.proof : bv_leq.r_neg_r.Stmt := by
  sorry

theorem bv_leq.r_const_add.proof : bv_leq.r_const_add.Stmt := by
  sorry

theorem bv_leq.r_add_const.proof : bv_leq.r_add_const.Stmt := by
  sorry

theorem bv_leq.r_add_add.proof : bv_leq.r_add_add.Stmt := by
  sorry

theorem bv_leq.r_self_add_r.proof : bv_leq.r_self_add_r.Stmt := by
  sorry

theorem bv_leq.r_self_add_l.proof : bv_leq.r_self_add_l.Stmt := by
  sorry

theorem bv_leq.r_min_l.proof : bv_leq.r_min_l.Stmt := by
  sorry

theorem bv_leq.r_max_r.proof : bv_leq.r_max_r.Stmt := by
  sorry

theorem bv_leq.r_const_mul.proof : bv_leq.r_const_mul.Stmt := by
  sorry

theorem bv_leq.r_mul_const.proof : bv_leq.r_mul_const.Stmt := by
  sorry

theorem bv_leq.r_mul_mul.proof : bv_leq.r_mul_mul.Stmt := by
  sorry

theorem bv_leq.r_udiv_big.proof : bv_leq.r_udiv_big.Stmt := by
  sorry

theorem bv_leq.r_ite_l.proof : bv_leq.r_ite_l.Stmt := by
  sorry

theorem bv_leq.r_ite_r.proof : bv_leq.r_ite_r.Stmt := by
  sorry

theorem bv_leq.r_const_sub1.proof : bv_leq.r_const_sub1.Stmt := by
  sorry

theorem bv_leq.r_const_sub2.proof : bv_leq.r_const_sub2.Stmt := by
  sorry

theorem bv_leq.r_sub_const1.proof : bv_leq.r_sub_const1.Stmt := by
  sorry

theorem bv_leq.r_sub_const2.proof : bv_leq.r_sub_const2.Stmt := by
  sorry

theorem bv_leq.r_ub_r.proof : bv_leq.r_ub_r.Stmt := by
  sorry

theorem bv_leq.r_ub_l.proof : bv_leq.r_ub_l.Stmt := by
  sorry

theorem bv_leq.r_to_unsigned_l.proof : bv_leq.r_to_unsigned_l.Stmt := by
  sorry

theorem bv_leq.r_to_unsigned_r.proof : bv_leq.r_to_unsigned_r.Stmt := by
  sorry

theorem bv_leq.r_default.proof : bv_leq.r_default.Stmt := by
  sorry

end Bvr
