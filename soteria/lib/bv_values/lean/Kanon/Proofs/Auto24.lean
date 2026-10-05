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

@[kanon_arm] theorem bv_lt.r_const_add.swap.proof : bv_lt.r_const_add.swap.Stmt := kanon_proof% bv_lt.r_const_add.swap

@[kanon_arm] theorem bv_lt.r_add_const.main.proof : bv_lt.r_add_const.main.Stmt := kanon_proof% bv_lt.r_add_const.main

@[kanon_arm] theorem bv_lt.r_add_const.swap.proof : bv_lt.r_add_const.swap.Stmt := kanon_proof% bv_lt.r_add_const.swap

@[kanon_arm] theorem bv_lt.r_self_add_r.main.proof : bv_lt.r_self_add_r.main.Stmt := kanon_proof% bv_lt.r_self_add_r.main

@[kanon_arm] theorem bv_lt.r_self_add_l.main.proof : bv_lt.r_self_add_l.main.Stmt := kanon_proof% bv_lt.r_self_add_l.main

@[kanon_arm] theorem bv_lt.r_add_add.main.proof : bv_lt.r_add_add.main.Stmt := kanon_proof% bv_lt.r_add_add.main

@[kanon_arm] theorem bv_lt.r_add_add.swap2.proof : bv_lt.r_add_add.swap2.Stmt := kanon_proof% bv_lt.r_add_add.swap2

@[kanon_arm] theorem bv_lt.r_add_add.swap1.proof : bv_lt.r_add_add.swap1.Stmt := kanon_proof% bv_lt.r_add_add.swap1

@[kanon_arm] theorem bv_lt.r_add_add.swap1_swap2.proof : bv_lt.r_add_add.swap1_swap2.Stmt := kanon_proof% bv_lt.r_add_add.swap1_swap2

@[kanon_arm] theorem bv_lt.r_one.main.proof : bv_lt.r_one.main.Stmt := kanon_proof% bv_lt.r_one.main

end Kanon
