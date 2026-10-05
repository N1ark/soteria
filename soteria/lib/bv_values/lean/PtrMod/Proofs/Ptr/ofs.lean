import PtrMod.Statements.Ptr.ofs
import PtrMod.Lib.Rule

/-! The offset of a pointer is its offset (`Lib.Refines.ofs_ptr`). -/

namespace PtrMod

@[kanon_arm] theorem Ptr.ofs.r_ptr.main.proof : Ptr.ofs.r_ptr.main.Stmt := by
  intro S _ _ B LBool LCore LBitvec L _ _ _ _ O hO l o t
  exact Lib.Refines.ofs_ptr

end PtrMod
