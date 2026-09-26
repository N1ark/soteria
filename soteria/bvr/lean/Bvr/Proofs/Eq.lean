import Bvr.Lemmas

/-! Equality (`sem_eq`), floats and pointers. -/

namespace Bvr

open Classical

theorem sem_eq.r_same.proof : sem_eq.r_same.Stmt := by
  sorry

theorem sem_eq.r_bools.proof : sem_eq.r_bools.Stmt := by
  sorry

theorem sem_eq.r_ptrs.proof : sem_eq.r_ptrs.Stmt := by
  sorry

theorem sem_eq.r_bvs.proof : sem_eq.r_bvs.Stmt := by
  sorry

theorem sem_eq.r_floats.proof : sem_eq.r_floats.Stmt := by
  sorry

theorem sem_eq.r_neg_r.proof : sem_eq.r_neg_r.Stmt := by
  sorry

theorem sem_eq.r_neg_l.proof : sem_eq.r_neg_l.Stmt := by
  sorry

theorem sem_eq.r_not_r.proof : sem_eq.r_not_r.Stmt := by
  sorry

theorem sem_eq.r_not_l.proof : sem_eq.r_not_l.Stmt := by
  sorry

theorem sem_eq.r_add_const_r.proof : sem_eq.r_add_const_r.Stmt := by
  sorry

theorem sem_eq.r_add_const_l.proof : sem_eq.r_add_const_l.Stmt := by
  sorry

theorem sem_eq.r_sub_const_r1.proof : sem_eq.r_sub_const_r1.Stmt := by
  sorry

theorem sem_eq.r_sub_const_r2.proof : sem_eq.r_sub_const_r2.Stmt := by
  sorry

theorem sem_eq.r_sub_const_l1.proof : sem_eq.r_sub_const_l1.Stmt := by
  sorry

theorem sem_eq.r_sub_const_l2.proof : sem_eq.r_sub_const_l2.Stmt := by
  sorry

theorem sem_eq.r_self_add_r.proof : sem_eq.r_self_add_r.Stmt := by
  sorry

theorem sem_eq.r_self_add_l.proof : sem_eq.r_self_add_l.Stmt := by
  sorry

theorem sem_eq.r_add_add.proof : sem_eq.r_add_add.Stmt := by
  sorry

theorem sem_eq.r_mul_const.proof : sem_eq.r_mul_const.Stmt := by
  sorry

theorem sem_eq.r_ite_ite.proof : sem_eq.r_ite_ite.Stmt := by
  sorry

theorem sem_eq.r_mul_cancel.proof : sem_eq.r_mul_cancel.Stmt := by
  sorry

theorem sem_eq.r_or_zero.proof : sem_eq.r_or_zero.Stmt := by
  sorry

theorem sem_eq.r_and_mask.proof : sem_eq.r_and_mask.Stmt := by
  sorry

theorem sem_eq.r_concat_const.proof : sem_eq.r_concat_const.Stmt := by
  sorry

theorem sem_eq.r_zext_const.proof : sem_eq.r_zext_const.Stmt := by
  sorry

theorem sem_eq.r_ite_concat.proof : sem_eq.r_ite_concat.Stmt := by
  sorry

theorem sem_eq.r_concat_concat.proof : sem_eq.r_concat_concat.Stmt := by
  sorry

theorem sem_eq.r_ite_const_l.proof : sem_eq.r_ite_const_l.Stmt := by
  sorry

theorem sem_eq.r_ite_const_r.proof : sem_eq.r_ite_const_r.Stmt := by
  sorry

theorem sem_eq.r_false_l.proof : sem_eq.r_false_l.Stmt := by
  sorry

theorem sem_eq.r_false_r.proof : sem_eq.r_false_r.Stmt := by
  sorry

theorem sem_eq.r_true_l.proof : sem_eq.r_true_l.Stmt := by
  sorry

theorem sem_eq.r_true_r.proof : sem_eq.r_true_r.Stmt := by
  sorry

theorem sem_eq.r_of_bools.proof : sem_eq.r_of_bools.Stmt := by
  sorry

theorem sem_eq.r_nots.proof : sem_eq.r_nots.Stmt := by
  sorry

theorem sem_eq.r_of_bool_const.proof : sem_eq.r_of_bool_const.Stmt := by
  sorry

theorem sem_eq.r_msb.proof : sem_eq.r_msb.Stmt := by
  sorry

theorem sem_eq.r_default.proof : sem_eq.r_default.Stmt := by
  sorry

theorem float_is_floatclass.r_lit.proof : float_is_floatclass.r_lit.Stmt := by
  sorry

theorem float_is_floatclass.r_default.proof : float_is_floatclass.r_default.Stmt := by
  sorry

theorem float_is_negative.r_lit.proof : float_is_negative.r_lit.Stmt := by
  sorry

theorem float_is_negative.r_default.proof : float_is_negative.r_default.Stmt := by
  sorry

theorem float_is_positive.r_lit.proof : float_is_positive.r_lit.Stmt := by
  sorry

theorem float_is_positive.r_default.proof : float_is_positive.r_default.Stmt := by
  sorry

theorem float_cast.r_lit.proof : float_cast.r_lit.Stmt := by
  sorry

theorem float_cast.r_same.proof : float_cast.r_same.Stmt := by
  sorry

theorem float_cast.r_default.proof : float_cast.r_default.Stmt := by
  sorry

theorem float_eq.r_lits.proof : float_eq.r_lits.Stmt := by
  sorry

theorem float_eq.r_same.proof : float_eq.r_same.Stmt := by
  sorry

theorem float_eq.r_lit_l.proof : float_eq.r_lit_l.Stmt := by
  sorry

theorem float_eq.r_lit_r.proof : float_eq.r_lit_r.Stmt := by
  sorry

theorem float_eq.r_default.proof : float_eq.r_default.Stmt := by
  sorry

theorem float_lt.r_lits.proof : float_lt.r_lits.Stmt := by
  sorry

theorem float_lt.r_default.proof : float_lt.r_default.Stmt := by
  sorry

theorem float_leq.r_lits.proof : float_leq.r_lits.Stmt := by
  sorry

theorem float_leq.r_default.proof : float_leq.r_default.Stmt := by
  sorry

theorem float_add.r_lits.proof : float_add.r_lits.Stmt := by
  sorry

theorem float_add.r_default.proof : float_add.r_default.Stmt := by
  sorry

theorem float_sub.r_lits.proof : float_sub.r_lits.Stmt := by
  sorry

theorem float_sub.r_default.proof : float_sub.r_default.Stmt := by
  sorry

theorem float_div.r_lits.proof : float_div.r_lits.Stmt := by
  sorry

theorem float_div.r_default.proof : float_div.r_default.Stmt := by
  sorry

theorem float_mul.r_lits.proof : float_mul.r_lits.Stmt := by
  sorry

theorem float_mul.r_default.proof : float_mul.r_default.Stmt := by
  sorry

theorem float_rem.r_lits.proof : float_rem.r_lits.Stmt := by
  sorry

theorem float_rem.r_default.proof : float_rem.r_default.Stmt := by
  sorry

theorem float_abs.r_lit.proof : float_abs.r_lit.Stmt := by
  sorry

theorem float_abs.r_abs.proof : float_abs.r_abs.Stmt := by
  sorry

theorem float_abs.r_default.proof : float_abs.r_default.Stmt := by
  sorry

theorem float_neg.r_lit.proof : float_neg.r_lit.Stmt := by
  sorry

theorem float_neg.r_neg.proof : float_neg.r_neg.Stmt := by
  sorry

theorem float_neg.r_default.proof : float_neg.r_default.Stmt := by
  sorry

theorem float_fma.r_lits.proof : float_fma.r_lits.Stmt := by
  sorry

theorem float_fma.r_default.proof : float_fma.r_default.Stmt := by
  sorry

theorem float_fmod_of_rem.r_main.proof : float_fmod_of_rem.r_main.Stmt := by
  sorry

theorem float_fmod.r_lits.proof : float_fmod.r_lits.Stmt := by
  sorry

theorem float_fmod.r_default.proof : float_fmod.r_default.Stmt := by
  sorry

theorem float_min.r_lits.proof : float_min.r_lits.Stmt := by
  sorry

theorem float_min.r_default.proof : float_min.r_default.Stmt := by
  sorry

theorem float_max.r_lits.proof : float_max.r_lits.Stmt := by
  sorry

theorem float_max.r_default.proof : float_max.r_default.Stmt := by
  sorry

theorem float_sqrt.r_lit.proof : float_sqrt.r_lit.Stmt := by
  sorry

theorem float_sqrt.r_default.proof : float_sqrt.r_default.Stmt := by
  sorry

theorem float_round.r_lit.proof : float_round.r_lit.Stmt := by
  sorry

theorem float_round.r_default.proof : float_round.r_default.Stmt := by
  sorry

theorem ptr_loc.r_ptr.proof : ptr_loc.r_ptr.Stmt := by
  sorry

theorem ptr_loc.r_default.proof : ptr_loc.r_default.Stmt := by
  sorry

theorem ptr_ofs.r_ptr.proof : ptr_ofs.r_ptr.Stmt := by
  sorry

theorem ptr_ofs.r_default.proof : ptr_ofs.r_default.Stmt := by
  sorry

end Bvr
