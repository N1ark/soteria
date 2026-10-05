import Kanon.Lib.Rule
import Kanon.Statements.Bitvec.sub_overflows

/-! The arm of `Bitvec.sub_overflows` that the default tactics do not prove. -/

namespace Kanon

open CoreMod

open Classical Lib

@[kanon_arm] theorem Bitvec.sub_overflows.r_unsigned.main.proof :
    Bitvec.sub_overflows.r_unsigned.main.Stmt := by
  kanon_rule_b
  all_goals simp_all [BitVec.usubOverflow, BitVec.ult]

end Kanon
