import Bvr.Lib.Compare

/-! Comparisons (`bv_lt`, `bv_leq`), proved per alternative. -/

namespace Bvr

open Classical Lib

theorem bv_lt.r_add_add.a1.proof : bv_lt.r_add_add.a1.Stmt := by
  bvr_cmp

theorem bv_lt.r_add_add.a2.proof : bv_lt.r_add_add.a2.Stmt := by
  bvr_cmp

theorem bv_lt.r_add_add.a3.proof : bv_lt.r_add_add.a3.Stmt := by
  bvr_cmp

theorem bv_lt.r_add_add.a4.proof : bv_lt.r_add_add.a4.Stmt := by
  bvr_cmp

theorem bv_lt.r_lt_zero.a1.proof : bv_lt.r_lt_zero.a1.Stmt := by
  intro FS O hO s v z T h
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at h
  obtain ⟨rfl, rfl, -⟩ := h
  exact refines_lt_zero_aux hO

set_option maxHeartbeats 1000000 in
theorem bv_lt.r_const_mul.a1.proof : bv_lt.r_const_mul.a1.Stmt := by
  bvr_cmp

set_option maxHeartbeats 1000000 in
theorem bv_lt.r_mul_const.a1.proof : bv_lt.r_mul_const.a1.Stmt := by
  bvr_cmp

theorem bv_leq.r_add_add.a1.proof : bv_leq.r_add_add.a1.Stmt := by
  bvr_cmp

theorem bv_leq.r_add_add.a2.proof : bv_leq.r_add_add.a2.Stmt := by
  bvr_cmp

theorem bv_leq.r_add_add.a3.proof : bv_leq.r_add_add.a3.Stmt := by
  bvr_cmp

theorem bv_leq.r_add_add.a4.proof : bv_leq.r_add_add.a4.Stmt := by
  bvr_cmp

set_option maxHeartbeats 1000000 in
theorem bv_leq.r_const_mul.a1.proof : bv_leq.r_const_mul.a1.Stmt := by
  bvr_cmp

set_option maxHeartbeats 1000000 in
theorem bv_leq.r_mul_const.a1.proof : bv_leq.r_mul_const.a1.Stmt := by
  bvr_cmp

theorem bv_leq.r_udiv_big.a1.proof : bv_leq.r_udiv_big.a1.Stmt := by
  bvr_cmp_using [smtUDiv_ule_of_umulOverflow]

end Bvr
