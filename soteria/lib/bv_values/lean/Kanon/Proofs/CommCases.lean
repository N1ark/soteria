import Kanon.Lib.Cases

/-! The commutativity of the operators that the bool module does not own: the
operands of `Add`, `Mul`, `AddOvf`, `MulOvf`, `BitAnd`, `BitOr`, `BitXor` and
`FEq` can be swapped, by `Lib.Refines.comm` (the value of each is symmetric,
`Lib.evOp2_comm`). -/

namespace Kanon

open Lib

@[kanon_arm] theorem Op2.Add.comm.proof : Op2.Add.comm.Stmt :=
  fun _ _ _ _ _ => Refines.comm (by simp [Op2.Comm]) fun _ => rfl

@[kanon_arm] theorem Op2.Mul.comm.proof : Op2.Mul.comm.Stmt :=
  fun _ _ _ _ _ => Refines.comm (by simp [Op2.Comm]) fun _ => rfl

@[kanon_arm] theorem Op2.AddOvf.comm.proof : Op2.AddOvf.comm.Stmt :=
  fun _ _ _ _ _ => Refines.comm (by simp [Op2.Comm]) fun _ => rfl

@[kanon_arm] theorem Op2.MulOvf.comm.proof : Op2.MulOvf.comm.Stmt :=
  fun _ _ _ _ _ => Refines.comm (by simp [Op2.Comm]) fun _ => rfl

@[kanon_arm] theorem Op2.BitAnd.comm.proof : Op2.BitAnd.comm.Stmt :=
  fun _ _ _ _ => Refines.comm (by simp [Op2.Comm]) fun _ => rfl

@[kanon_arm] theorem Op2.BitOr.comm.proof : Op2.BitOr.comm.Stmt :=
  fun _ _ _ _ => Refines.comm (by simp [Op2.Comm]) fun _ => rfl

@[kanon_arm] theorem Op2.BitXor.comm.proof : Op2.BitXor.comm.Stmt :=
  fun _ _ _ _ => Refines.comm (by simp [Op2.Comm]) fun _ => rfl

@[kanon_arm] theorem Op2.FEq.comm.proof : Op2.FEq.comm.Stmt :=
  fun _ _ _ _ => Refines.comm (by simp [Op2.Comm]) fun _ => rfl

end Kanon
