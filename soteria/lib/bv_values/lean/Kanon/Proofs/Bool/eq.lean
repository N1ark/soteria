import Kanon.Lib.Eq
import Kanon.Statements.Bool.eq

/-! The arms of `Bool.eq` that the default tactics do not prove. -/

namespace Kanon

open Classical Lib SemEq

@[kanon_arm] theorem Bool.eq.r_mul_const.main.proof : Bool.eq.r_mul_const.main.Stmt := by
  kanon_rule_lift_side
  all_goals
    refine Refines.eq_mul_const (by simp only [Bitvec.is_checked, Bool.or_eq_true]; assumption)
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
    false_eq_decide_iff, BitVec.ofInt_emod_two_pow] at *
  all_goals first
    | (simp_all; done)
    | exact mulc_zero ‹_› ‹_›
    | exact mulc_fits hW ‹_› ‹_› (by simp_all)
    | exact mulc_nofit ‹_› ‹_› (by simp_all)
    | exact mulc_nodvd ‹_›

@[kanon_arm] theorem Bool.eq.r_mul_cancel.main.proof : Bool.eq.r_mul_cancel.main.Stmt := by
  kanon_rule_b_sem
  all_goals first
    | (rw [← mul_cancel_flags ‹_› ‹_› ‹_›]; assumption)
    | (rw [← mul_cancel_flags (b := ‹BitVec _›) ‹_› ‹_› ‹_›]; assumption)

@[kanon_arm] theorem Bool.eq.r_zext_const.main.proof : Bool.eq.r_zext_const.main.Stmt := by
  kanon_rule_b_sem
  all_goals simp_all [zext_mask, setWidth_eq_iff'] <;> omega

@[kanon_arm] theorem Bool.eq.r_ite_concat.main.proof : Bool.eq.r_ite_concat.main.Stmt := by
  kanon_rule_b_arith

@[kanon_arm] theorem Bool.eq.r_and_mask.main.proof : Bool.eq.r_and_mask.main.Stmt := by
  kanon_rule_b_sem
  all_goals exact ‹¬ z_land _ _ = 0› (land_lit_not_self ‹_› (BitVec.isLt _)) |>.elim

@[kanon_arm] theorem Bool.eq.r_and_mask.swap2.proof : Bool.eq.r_and_mask.swap2.Stmt := by
  kanon_rule_b_sem
  all_goals
    subst_vars
    simp only [BitVec.toNat_and] at *
    exact ‹¬ z_land _ _ = 0› (land_lit_not_self ‹_› (BitVec.isLt _)) |>.elim

@[kanon_arm] theorem Bool.eq.r_and_mask.swap1_swap2.proof : Bool.eq.r_and_mask.swap1_swap2.Stmt := by
  kanon_rule_b_sem
  all_goals
    subst_vars
    simp only [BitVec.toNat_and] at *
    exact ‹¬ z_land _ _ = 0› (land_lit_not_self' ‹_› (BitVec.isLt _)) |>.elim

end Kanon
