import BitvecMod.Lib.Rule
import BitvecMod.Soundness.Laws
import BitvecMod.Statements.Bitvec.leq

/-! The arms of `Bitvec.leq` that `bv_cmp` does not prove: `r_udiv_big`, whose
product `n * d` is zero when `d` is (`bv_cmp_mul_zero`), and
`r_mul_mul.swap1_swap2`, which is `r_mul_mul.main` up to the order of the
products (`kanon_comm`). -/

namespace BitvecMod

open Classical Kanon Kanon.Sem Lib

@[kanon_arm] theorem Bitvec.leq.r_udiv_big.main.proof : Bitvec.leq.r_udiv_big.main.Stmt := by
  intro _
  intros
  bv_rs_rule_lift_core
  bv_rule_apply
  all_goals bv_cmp_bools
  all_goals first
    | (bv_rs_wt; done)
    | (bv_cmp_sem
       all_goals bv_cmp_pre
       all_goals bv_cmp_pow_facts
       all_goals bv_cmp_gen_values
       all_goals bv_cmp_mul_zero
       all_goals omega)

@[kanon_arm] theorem Bitvec.leq.r_mul_mul.main.proof : Bitvec.leq.r_mul_mul.main.Stmt := by
  bv_cmp

@[kanon_arm] theorem Bitvec.leq.r_mul_mul.swap1_swap2.proof :
    Bitvec.leq.r_mul_mul.swap1_swap2.Stmt := by
  intro S _ _ B LBool LCore L _ _ _ O hO signed cl x a t5 cr y k t11 h
  refine Refines.trans ?_ (Bitvec.leq.r_mul_mul.main.proof L O hO signed cl a x t5 cr k y t11 h)
  simp only [kanon_spec]
  kanon_comm

end BitvecMod
