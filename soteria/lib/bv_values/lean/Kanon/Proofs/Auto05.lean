import Kanon.Proofs.CommCases
import Kanon.Proofs.ArithCases
import Kanon.Proofs.EqCases
import Kanon.Proofs.BitwiseCases
import Kanon.Proofs.ResizeCases
import Kanon.Proofs.CompareCases
import Kanon.Proofs.BoolCases
import Kanon.Lib.Rule
import Kanon.Statements

/-! The alternatives that Kanon's default tactics prove (`kanon_proof%`), a few per module so
that each is elaborated on its own (the whole of `Soundness` does not fit in memory). -/

set_option maxHeartbeats 4000000

noncomputable section

namespace Kanon

open Classical Kanon

@[kanon_arm] theorem sem_eq.r_or_zero.swap.proof : sem_eq.r_or_zero.swap.Stmt := kanon_proof% sem_eq.r_or_zero.swap

@[kanon_arm] theorem sem_eq.r_concat_const.main.proof : sem_eq.r_concat_const.main.Stmt := kanon_proof% sem_eq.r_concat_const.main

@[kanon_arm] theorem sem_eq.r_concat_concat.main.proof : sem_eq.r_concat_concat.main.Stmt := kanon_proof% sem_eq.r_concat_concat.main

@[kanon_arm] theorem sem_eq.r_ite_const.bitVec.proof : sem_eq.r_ite_const.bitVec.Stmt := kanon_proof% sem_eq.r_ite_const.bitVec

@[kanon_arm] theorem sem_eq.r_ite_const.locLit.proof : sem_eq.r_ite_const.locLit.Stmt := kanon_proof% sem_eq.r_ite_const.locLit

@[kanon_arm] theorem sem_eq.r_of_bools.main.proof : sem_eq.r_of_bools.main.Stmt := kanon_proof% sem_eq.r_of_bools.main

@[kanon_arm] theorem sem_eq.r_of_bool_const.main.proof : sem_eq.r_of_bool_const.main.Stmt := kanon_proof% sem_eq.r_of_bool_const.main

@[kanon_arm] theorem sem_eq.r_msb.main.proof : sem_eq.r_msb.main.Stmt := kanon_proof% sem_eq.r_msb.main

@[kanon_arm] theorem sem_eq.r_floats.main.proof : sem_eq.r_floats.main.Stmt := kanon_proof% sem_eq.r_floats.main

@[kanon_arm] theorem sem_eq.r_ptrs.main.proof : sem_eq.r_ptrs.main.Stmt := kanon_proof% sem_eq.r_ptrs.main

end Kanon
