import Kanon.Lib.Resize
import Kanon.Statements.Float.neg

/-! The arms of `Float.neg` that the default tactics do not prove. -/

namespace Kanon

open Classical Lib

@[kanon_arm] theorem Float.neg.r_neg.main.proof : Float.neg.r_neg.main.Stmt := by
  intro FS O hO a T
  exact Refines.funop_invol (by simp) fun v r => by
    rcases v with _ | ⟨_ | _ | _ | ⟨p, x⟩ | _ | _⟩ <;> simp [evOp1, FBits.neg_neg]

end Kanon
