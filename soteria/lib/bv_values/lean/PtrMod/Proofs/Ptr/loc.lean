import PtrMod.Statements.Ptr.loc
import PtrMod.Lib.Rule

/-! The location of a pointer is its location (`Lib.Refines.loc_ptr`). -/

namespace PtrMod

@[kanon_arm] theorem Ptr.loc.r_ptr.main.proof : Ptr.loc.r_ptr.main.Stmt := by
  intro S _ _ B LBool LCore LBitvec L _ _ _ _ O hO l o t
  exact Lib.Refines.loc_ptr

end PtrMod
