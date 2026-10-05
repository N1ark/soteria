import Kanon.Lib.Compare
import Kanon.Statements.Bitvec.add

/-! The arms of `Bitvec.add` that the default tactics do not prove. -/

namespace Kanon

open CoreMod

open Classical Lib

@[kanon_arm] theorem Bitvec.add.r_default.main.proof : Bitvec.add.r_default.main.Stmt := by
  intro FS O hO checked v1 v2
  simp only [Bitvec.add.spec, mk_commut_binop]
  refine Sem.Refines.trans Refines.add_no_wrap ?_
  split
  · exact Sem.Refines.refl
  · exact Refines.comm (by simp [Op2.Comm]) (fun _ => rfl)

end Kanon
