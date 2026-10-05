import Kanon.Lib.Resize
import Kanon.Statements.Float.abs

/-! The arms of `Float.abs` that the default tactics do not prove. -/

namespace Kanon

open CoreMod

open Classical Lib

@[kanon_arm] theorem Float.abs.r_abs.main.proof : Float.abs.r_abs.main.Stmt := by
  intro FS O hO a T
  exact Refines.funop_idem fun v => by
    rcases v with _ | ⟨_ | _ | _ | ⟨p, x⟩ | _ | _⟩ <;> simp [evOp1, FBits.abs_abs]

end Kanon
