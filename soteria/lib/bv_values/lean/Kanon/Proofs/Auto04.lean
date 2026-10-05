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

@[kanon_arm] theorem sem_eq.r_bvs.bitVec_bitVec.proof : sem_eq.r_bvs.bitVec_bitVec.Stmt := kanon_proof% sem_eq.r_bvs.bitVec_bitVec

@[kanon_arm] theorem sem_eq.r_bvs.locLit_locLit.proof : sem_eq.r_bvs.locLit_locLit.Stmt := kanon_proof% sem_eq.r_bvs.locLit_locLit

@[kanon_arm] theorem sem_eq.r_neg.main.proof : sem_eq.r_neg.main.Stmt := kanon_proof% sem_eq.r_neg.main

@[kanon_arm] theorem sem_eq.r_not.main.proof : sem_eq.r_not.main.Stmt := kanon_proof% sem_eq.r_not.main

@[kanon_arm] theorem sem_eq.r_add_const.main.proof : sem_eq.r_add_const.main.Stmt := kanon_proof% sem_eq.r_add_const.main

@[kanon_arm] theorem sem_eq.r_sub_const1.main.proof : sem_eq.r_sub_const1.main.Stmt := kanon_proof% sem_eq.r_sub_const1.main

@[kanon_arm] theorem sem_eq.r_sub_const2.main.proof : sem_eq.r_sub_const2.main.Stmt := kanon_proof% sem_eq.r_sub_const2.main

@[kanon_arm] theorem sem_eq.r_self_add.main.proof : sem_eq.r_self_add.main.Stmt := kanon_proof% sem_eq.r_self_add.main

@[kanon_arm] theorem sem_eq.r_add_add.main.proof : sem_eq.r_add_add.main.Stmt := kanon_proof% sem_eq.r_add_add.main

@[kanon_arm] theorem sem_eq.r_or_zero.main.proof : sem_eq.r_or_zero.main.Stmt := kanon_proof% sem_eq.r_or_zero.main

end Kanon
