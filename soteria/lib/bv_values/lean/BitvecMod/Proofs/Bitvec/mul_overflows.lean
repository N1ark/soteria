import BitvecMod.Lifts
import BitvecMod.Statements.Bitvec.mul_overflows

/-! The arm of `Bitvec.mul_overflows` that `bveq_rule` does not prove. -/

namespace BitvecMod

open Lib.BvEq

/-- A multiplication of values of few significant bits does not overflow (`Sem.den_msb`). -/
@[kanon_arm] theorem Bitvec.mul_overflows.r_msb.main.proof :
    Bitvec.mul_overflows.r_msb.main.Stmt := by
  bveq_rule_lift
  exact Refines.mulOvf_msb ‹_›

end BitvecMod
