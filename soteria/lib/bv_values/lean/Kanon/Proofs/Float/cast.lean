import Kanon.Lib.Resize
import Kanon.Statements.Float.cast

/-! The arms of `Float.cast` that the default tactics do not prove. -/

namespace Kanon

open Classical Lib

@[kanon_arm] theorem Float.cast.r_lit.main.proof : Float.cast.r_lit.main.Stmt := by
  intro FS O hO rm fp f T
  refine Refines.lit_of_unop_prec (fun w => ?_) (fun hf => (hO.orc.convert rm fp f hf).2.2)
  have := hO.orc.convert rm fp f (Float.WF_of_WT (WT_op1.1 w).2)
  exact ⟨by rw [this.1], this.2.1⟩

end Kanon
