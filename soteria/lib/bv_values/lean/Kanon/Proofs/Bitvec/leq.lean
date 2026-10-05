import Kanon.Lib.Compare
import Kanon.Lib.Rule
import Kanon.Statements.Bitvec.leq

/-! The arms of `Bitvec.leq` that the default tactics do not prove. -/

namespace Kanon

open CoreMod

open Classical Lib

@[kanon_arm] theorem Bitvec.leq.r_udiv_big.main.proof : Bitvec.leq.r_udiv_big.main.Stmt := by
  kanon_cmp_using [smtUDiv_ule_of_umulOverflow]

end Kanon
