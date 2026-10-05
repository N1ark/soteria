import BitvecMod.Lifts
import BitvecMod.Statements.Bool.not_

/-! The arms that the bitvec module adds to `Bool.not_`, by `bveq_rule` (`Lib/Eq.lean`). -/

namespace BitvecMod

@[kanon_arm] theorem Bool.not_.r_lt.main.proof : Bool.not_.r_lt.main.Stmt := by
  bveq_rule

@[kanon_arm] theorem Bool.not_.r_leq.main.proof : Bool.not_.r_leq.main.Stmt := by
  bveq_rule

@[kanon_arm] theorem Bool.not_.r_eq_bit.main.proof : Bool.not_.r_eq_bit.main.Stmt := by
  bveq_rule

@[kanon_arm] theorem Bool.not_.r_eq_bit.swap.proof : Bool.not_.r_eq_bit.swap.Stmt := by
  bveq_rule

end BitvecMod
