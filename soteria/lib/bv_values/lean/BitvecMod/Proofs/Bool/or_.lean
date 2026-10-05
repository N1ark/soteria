import BitvecMod.Lifts
import BitvecMod.Statements.Bool.or_

/-! The arms that the bitvec module adds to `Bool.or_`: the bounds by `bveq_rule_bounds`, the
others by `bveq_rule` (`Lib/Eq.lean`). -/

namespace BitvecMod

@[kanon_arm] theorem Bool.or_.r_lt_lt.main.proof : Bool.or_.r_lt_lt.main.Stmt := by
  bveq_rule

@[kanon_arm] theorem Bool.or_.r_lt_leq.main.proof : Bool.or_.r_lt_leq.main.Stmt := by
  bveq_rule

@[kanon_arm] theorem Bool.or_.r_lt_leq.swap.proof : Bool.or_.r_lt_leq.swap.Stmt := by
  bveq_rule

@[kanon_arm] theorem Bool.or_.r_complementary.lt_lt.proof : Bool.or_.r_complementary.lt_lt.Stmt := by
  bveq_rule_bounds

@[kanon_arm] theorem Bool.or_.r_complementary.lt_leq.proof : Bool.or_.r_complementary.lt_leq.Stmt := by
  bveq_rule_bounds

@[kanon_arm] theorem Bool.or_.r_complementary.leq_lt.proof : Bool.or_.r_complementary.leq_lt.Stmt := by
  bveq_rule_bounds

@[kanon_arm] theorem Bool.or_.r_complementary.leq_leq.proof : Bool.or_.r_complementary.leq_leq.Stmt := by
  bveq_rule_bounds

@[kanon_arm] theorem Bool.or_.r_complementary.lt_lt_swap.proof : Bool.or_.r_complementary.lt_lt_swap.Stmt := by
  bveq_rule_bounds

@[kanon_arm] theorem Bool.or_.r_complementary.leq_lt_swap.proof : Bool.or_.r_complementary.leq_lt_swap.Stmt := by
  bveq_rule_bounds

@[kanon_arm] theorem Bool.or_.r_complementary.lt_leq_swap.proof : Bool.or_.r_complementary.lt_leq_swap.Stmt := by
  bveq_rule_bounds

@[kanon_arm] theorem Bool.or_.r_complementary.leq_leq_swap.proof : Bool.or_.r_complementary.leq_leq_swap.Stmt := by
  bveq_rule_bounds

@[kanon_arm] theorem Bool.or_.r_upper_eq.lt.proof : Bool.or_.r_upper_eq.lt.Stmt := by
  bveq_rule_bounds

@[kanon_arm] theorem Bool.or_.r_upper_eq.lt_swap1.proof : Bool.or_.r_upper_eq.lt_swap1.Stmt := by
  bveq_rule_bounds

@[kanon_arm] theorem Bool.or_.r_upper_eq.leq.proof : Bool.or_.r_upper_eq.leq.Stmt := by
  bveq_rule_bounds

@[kanon_arm] theorem Bool.or_.r_upper_eq.leq_swap1.proof : Bool.or_.r_upper_eq.leq_swap1.Stmt := by
  bveq_rule_bounds

@[kanon_arm] theorem Bool.or_.r_upper_eq.lt_swap2.proof : Bool.or_.r_upper_eq.lt_swap2.Stmt := by
  bveq_rule_bounds

@[kanon_arm] theorem Bool.or_.r_upper_eq.leq_swap2.proof : Bool.or_.r_upper_eq.leq_swap2.Stmt := by
  bveq_rule_bounds

@[kanon_arm] theorem Bool.or_.r_upper_eq.lt_swap1_swap2.proof : Bool.or_.r_upper_eq.lt_swap1_swap2.Stmt := by
  bveq_rule_bounds

@[kanon_arm] theorem Bool.or_.r_upper_eq.leq_swap1_swap2.proof : Bool.or_.r_upper_eq.leq_swap1_swap2.Stmt := by
  bveq_rule_bounds

@[kanon_arm] theorem Bool.or_.r_lower_eq.lt.proof : Bool.or_.r_lower_eq.lt.Stmt := by
  bveq_rule_bounds

@[kanon_arm] theorem Bool.or_.r_lower_eq.lt_swap1.proof : Bool.or_.r_lower_eq.lt_swap1.Stmt := by
  bveq_rule_bounds

@[kanon_arm] theorem Bool.or_.r_lower_eq.leq.proof : Bool.or_.r_lower_eq.leq.Stmt := by
  bveq_rule_bounds

@[kanon_arm] theorem Bool.or_.r_lower_eq.leq_swap1.proof : Bool.or_.r_lower_eq.leq_swap1.Stmt := by
  bveq_rule_bounds

@[kanon_arm] theorem Bool.or_.r_lower_eq.lt_swap2.proof : Bool.or_.r_lower_eq.lt_swap2.Stmt := by
  bveq_rule_bounds

@[kanon_arm] theorem Bool.or_.r_lower_eq.leq_swap2.proof : Bool.or_.r_lower_eq.leq_swap2.Stmt := by
  bveq_rule_bounds

@[kanon_arm] theorem Bool.or_.r_lower_eq.lt_swap1_swap2.proof : Bool.or_.r_lower_eq.lt_swap1_swap2.Stmt := by
  bveq_rule_bounds

@[kanon_arm] theorem Bool.or_.r_lower_eq.leq_swap1_swap2.proof : Bool.or_.r_lower_eq.leq_swap1_swap2.Stmt := by
  bveq_rule_bounds

@[kanon_arm] theorem Bool.or_.r_upper_bounds.lt_lt.proof : Bool.or_.r_upper_bounds.lt_lt.Stmt := by
  bveq_rule_bounds

@[kanon_arm] theorem Bool.or_.r_upper_bounds.lt_leq.proof : Bool.or_.r_upper_bounds.lt_leq.Stmt := by
  bveq_rule_bounds

@[kanon_arm] theorem Bool.or_.r_upper_bounds.leq_lt.proof : Bool.or_.r_upper_bounds.leq_lt.Stmt := by
  bveq_rule_bounds

@[kanon_arm] theorem Bool.or_.r_upper_bounds.leq_leq.proof : Bool.or_.r_upper_bounds.leq_leq.Stmt := by
  bveq_rule_bounds

@[kanon_arm] theorem Bool.or_.r_lower_bounds.lt_lt.proof : Bool.or_.r_lower_bounds.lt_lt.Stmt := by
  bveq_rule_bounds

@[kanon_arm] theorem Bool.or_.r_lower_bounds.lt_leq.proof : Bool.or_.r_lower_bounds.lt_leq.Stmt := by
  bveq_rule_bounds

@[kanon_arm] theorem Bool.or_.r_lower_bounds.leq_lt.proof : Bool.or_.r_lower_bounds.leq_lt.Stmt := by
  bveq_rule_bounds

@[kanon_arm] theorem Bool.or_.r_lower_bounds.leq_leq.proof : Bool.or_.r_lower_bounds.leq_leq.Stmt := by
  bveq_rule_bounds

end BitvecMod
