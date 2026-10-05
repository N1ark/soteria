import BitvecMod.Lifts
import BitvecMod.Statements.Bool.and_

/-! The arms that the bitvec module adds to `Bool.and_`: the bounds by `bveq_rule_bounds`, the
others by `bveq_rule` (`Lib/Eq.lean`). -/

namespace BitvecMod

@[kanon_arm] theorem Bool.and_.r_eq_extracts.main.proof : Bool.and_.r_eq_extracts.main.Stmt := by
  bveq_rule

@[kanon_arm] theorem Bool.and_.r_eq_extracts.swap2.proof : Bool.and_.r_eq_extracts.swap2.Stmt := by
  bveq_rule

@[kanon_arm] theorem Bool.and_.r_eq_extracts.swap1.proof : Bool.and_.r_eq_extracts.swap1.Stmt := by
  bveq_rule

@[kanon_arm] theorem Bool.and_.r_eq_extracts.swap1_swap2.proof : Bool.and_.r_eq_extracts.swap1_swap2.Stmt := by
  bveq_rule

@[kanon_arm] theorem Bool.and_.r_upper_bounds.lt_lt.proof : Bool.and_.r_upper_bounds.lt_lt.Stmt := by
  bveq_rule_bounds

@[kanon_arm] theorem Bool.and_.r_upper_bounds.lt_leq.proof : Bool.and_.r_upper_bounds.lt_leq.Stmt := by
  bveq_rule_bounds

@[kanon_arm] theorem Bool.and_.r_upper_bounds.leq_lt.proof : Bool.and_.r_upper_bounds.leq_lt.Stmt := by
  bveq_rule_bounds

@[kanon_arm] theorem Bool.and_.r_upper_bounds.leq_leq.proof : Bool.and_.r_upper_bounds.leq_leq.Stmt := by
  bveq_rule_bounds

@[kanon_arm] theorem Bool.and_.r_lower_bounds.lt_lt.proof : Bool.and_.r_lower_bounds.lt_lt.Stmt := by
  bveq_rule_bounds

@[kanon_arm] theorem Bool.and_.r_lower_bounds.lt_leq.proof : Bool.and_.r_lower_bounds.lt_leq.Stmt := by
  bveq_rule_bounds

@[kanon_arm] theorem Bool.and_.r_lower_bounds.leq_lt.proof : Bool.and_.r_lower_bounds.leq_lt.Stmt := by
  bveq_rule_bounds

@[kanon_arm] theorem Bool.and_.r_lower_bounds.leq_leq.proof : Bool.and_.r_lower_bounds.leq_leq.Stmt := by
  bveq_rule_bounds

end BitvecMod
