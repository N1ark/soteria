import BitvecMod.Soundness.Laws
import BitvecMod.Statements.Bool.eq

/-! The arms that the bitvec module adds to `Bool.eq`, by `bveq_rule` (`Lib/Eq.lean`), which the
default tactic of the module (`bv_rule`) is not: the arms with an operand swapped are those of
the `main` arm, by the commutativity of `Eq` (`bveq_eq_swap`) or `Mul` (`bveq_mul_swap`). -/

namespace BitvecMod

open Lib.BvEq

@[kanon_arm] theorem Bool.eq.r_bvs.bitVec_bitVec.proof : Bool.eq.r_bvs.bitVec_bitVec.Stmt := by
  bveq_rule

@[kanon_arm] theorem Bool.eq.r_bvs.locLit_locLit.proof : Bool.eq.r_bvs.locLit_locLit.Stmt := by
  bveq_rule

@[kanon_arm] theorem Bool.eq.r_neg.main.proof : Bool.eq.r_neg.main.Stmt := by
  bveq_rule

@[kanon_arm] theorem Bool.eq.r_neg.swap.proof : Bool.eq.r_neg.swap.Stmt := by
  bveq_rule

@[kanon_arm] theorem Bool.eq.r_not.main.proof : Bool.eq.r_not.main.Stmt := by
  bveq_rule

@[kanon_arm] theorem Bool.eq.r_not.swap.proof : Bool.eq.r_not.swap.Stmt := by
  bveq_rule

@[kanon_arm] theorem Bool.eq.r_add_const.main.proof : Bool.eq.r_add_const.main.Stmt := by
  bveq_rule

@[kanon_arm] theorem Bool.eq.r_add_const.swap1.proof : Bool.eq.r_add_const.swap1.Stmt := by
  bveq_rule

@[kanon_arm] theorem Bool.eq.r_add_const.swap2.proof : Bool.eq.r_add_const.swap2.Stmt := by
  bveq_rule

@[kanon_arm] theorem Bool.eq.r_add_const.swap1_swap2.proof : Bool.eq.r_add_const.swap1_swap2.Stmt := by
  bveq_rule

@[kanon_arm] theorem Bool.eq.r_sub_const1.main.proof : Bool.eq.r_sub_const1.main.Stmt := by
  bveq_rule

@[kanon_arm] theorem Bool.eq.r_sub_const1.swap.proof : Bool.eq.r_sub_const1.swap.Stmt := by
  bveq_rule

@[kanon_arm] theorem Bool.eq.r_sub_const2.main.proof : Bool.eq.r_sub_const2.main.Stmt := by
  bveq_rule

@[kanon_arm] theorem Bool.eq.r_sub_const2.swap.proof : Bool.eq.r_sub_const2.swap.Stmt := by
  bveq_rule

@[kanon_arm] theorem Bool.eq.r_self_add.main.proof : Bool.eq.r_self_add.main.Stmt := by
  bveq_rule

@[kanon_arm] theorem Bool.eq.r_self_add.swap1.proof : Bool.eq.r_self_add.swap1.Stmt := by
  bveq_rule

@[kanon_arm] theorem Bool.eq.r_self_add.swap2.proof : Bool.eq.r_self_add.swap2.Stmt := by
  bveq_rule

@[kanon_arm] theorem Bool.eq.r_self_add.swap1_swap2.proof : Bool.eq.r_self_add.swap1_swap2.Stmt := by
  bveq_rule

@[kanon_arm] theorem Bool.eq.r_add_add.main.proof : Bool.eq.r_add_add.main.Stmt := by
  bveq_rule

@[kanon_arm] theorem Bool.eq.r_add_add.swap2.proof : Bool.eq.r_add_add.swap2.Stmt := by
  bveq_rule

@[kanon_arm] theorem Bool.eq.r_add_add.swap1.proof : Bool.eq.r_add_add.swap1.Stmt := by
  bveq_rule

@[kanon_arm] theorem Bool.eq.r_add_add.swap1_swap2.proof : Bool.eq.r_add_add.swap1_swap2.Stmt := by
  bveq_rule

@[kanon_arm] theorem Bool.eq.r_mul_const.main.proof : Bool.eq.r_mul_const.main.Stmt := by
  bveq_mul_const

@[kanon_arm] theorem Bool.eq.r_mul_const.swap1.proof : Bool.eq.r_mul_const.swap1.Stmt := by
  bveq_mul_swap Bool.eq.r_mul_const.main.proof

@[kanon_arm] theorem Bool.eq.r_mul_const.swap2.proof : Bool.eq.r_mul_const.swap2.Stmt := by
  bveq_eq_swap Bool.eq.r_mul_const.main.proof

@[kanon_arm] theorem Bool.eq.r_mul_const.swap1_swap2.proof : Bool.eq.r_mul_const.swap1_swap2.Stmt := by
  bveq_eq_mul_swap Bool.eq.r_mul_const.main.proof

@[kanon_arm] theorem Bool.eq.r_mul_cancel.main.proof : Bool.eq.r_mul_cancel.main.Stmt := by
  bveq_rule

@[kanon_arm] theorem Bool.eq.r_mul_cancel.swap2.proof : Bool.eq.r_mul_cancel.swap2.Stmt := by
  bveq_rule

@[kanon_arm] theorem Bool.eq.r_mul_cancel.swap1.proof : Bool.eq.r_mul_cancel.swap1.Stmt := by
  bveq_rule

@[kanon_arm] theorem Bool.eq.r_mul_cancel.swap1_swap2.proof : Bool.eq.r_mul_cancel.swap1_swap2.Stmt := by
  bveq_rule

@[kanon_arm] theorem Bool.eq.r_or_zero.main.proof : Bool.eq.r_or_zero.main.Stmt := by
  bveq_rule

@[kanon_arm] theorem Bool.eq.r_or_zero.swap.proof : Bool.eq.r_or_zero.swap.Stmt := by
  bveq_rule

@[kanon_arm] theorem Bool.eq.r_and_mask.main.proof : Bool.eq.r_and_mask.main.Stmt := by
  bveq_rule

@[kanon_arm] theorem Bool.eq.r_and_mask.swap1.proof : Bool.eq.r_and_mask.swap1.Stmt := by
  bveq_rule

@[kanon_arm] theorem Bool.eq.r_and_mask.swap2.proof : Bool.eq.r_and_mask.swap2.Stmt := by
  bveq_rule

@[kanon_arm] theorem Bool.eq.r_and_mask.swap1_swap2.proof : Bool.eq.r_and_mask.swap1_swap2.Stmt := by
  bveq_rule

@[kanon_arm] theorem Bool.eq.r_concat_const.main.proof : Bool.eq.r_concat_const.main.Stmt := by
  bveq_rule

@[kanon_arm] theorem Bool.eq.r_concat_const.swap.proof : Bool.eq.r_concat_const.swap.Stmt := by
  bveq_rule

@[kanon_arm] theorem Bool.eq.r_zext_const.main.proof : Bool.eq.r_zext_const.main.Stmt := by
  bveq_rule

@[kanon_arm] theorem Bool.eq.r_zext_const.swap.proof : Bool.eq.r_zext_const.swap.Stmt := by
  bveq_eq_swap Bool.eq.r_zext_const.main.proof

@[kanon_arm] theorem Bool.eq.r_ite_concat.main.proof : Bool.eq.r_ite_concat.main.Stmt := by
  bveq_rule_arith

@[kanon_arm] theorem Bool.eq.r_ite_concat.swap.proof : Bool.eq.r_ite_concat.swap.Stmt := by
  bveq_rule_arith

@[kanon_arm] theorem Bool.eq.r_concat_concat.main.proof : Bool.eq.r_concat_concat.main.Stmt := by
  bveq_rule

@[kanon_arm] theorem Bool.eq.r_ite_const.bitVec.proof : Bool.eq.r_ite_const.bitVec.Stmt := by
  bveq_rule

@[kanon_arm] theorem Bool.eq.r_ite_const.locLit.proof : Bool.eq.r_ite_const.locLit.Stmt := by
  bveq_rule

@[kanon_arm] theorem Bool.eq.r_ite_const.bitVec_swap.proof : Bool.eq.r_ite_const.bitVec_swap.Stmt := by
  bveq_rule

@[kanon_arm] theorem Bool.eq.r_ite_const.locLit_swap.proof : Bool.eq.r_ite_const.locLit_swap.Stmt := by
  bveq_rule

@[kanon_arm] theorem Bool.eq.r_of_bools.main.proof : Bool.eq.r_of_bools.main.Stmt := by
  bveq_rule

@[kanon_arm] theorem Bool.eq.r_of_bool_const.main.proof : Bool.eq.r_of_bool_const.main.Stmt := by
  bveq_rule

@[kanon_arm] theorem Bool.eq.r_of_bool_const.swap.proof : Bool.eq.r_of_bool_const.swap.Stmt := by
  bveq_rule

@[kanon_arm] theorem Bool.eq.r_msb.main.proof : Bool.eq.r_msb.main.Stmt := by
  bveq_rule_lift
  exact Refines.eq_low ‹_› ‹_› (le_zmax_left _ _) (le_zmax_right _ _) ‹_›

end BitvecMod
