import Kanon.Lib.Bool
import Kanon.Statements.Bool.and_

/-! The arms of `Bool.and_` that the default tactics do not prove. -/

namespace Kanon

open CoreMod

open Classical Lib

@[kanon_arm] theorem Bool.and_.r_eq_extracts.main.proof : Bool.and_.r_eq_extracts.main.Stmt := by
  kanon_rule_sem
  all_goals first
    | omega
    | exact concat_eq_extract_of rfl rfl (by omega) (by omega)
    | exact concat_ne_extract ‹_› (by omega) (by omega)
    | exact concat_ne_extract' ‹_› (by omega) (by omega)

end Kanon
