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

@[kanon_arm] theorem bv_add.r_not_one.main.proof : bv_add.r_not_one.main.Stmt := kanon_proof% bv_add.r_not_one.main

@[kanon_arm] theorem bv_add.r_add_const.main.proof : bv_add.r_add_const.main.Stmt := kanon_proof% bv_add.r_add_const.main

@[kanon_arm] theorem bv_add.r_add_const.swap2.proof : bv_add.r_add_const.swap2.Stmt := kanon_proof% bv_add.r_add_const.swap2

@[kanon_arm] theorem bv_add.r_add_const.swap1_swap2.proof : bv_add.r_add_const.swap1_swap2.Stmt := kanon_proof% bv_add.r_add_const.swap1_swap2

@[kanon_arm] theorem bv_add.r_sub_const_r.main.proof : bv_add.r_sub_const_r.main.Stmt := kanon_proof% bv_add.r_sub_const_r.main

@[kanon_arm] theorem bv_add.r_sub_const_r.swap.proof : bv_add.r_sub_const_r.swap.Stmt := kanon_proof% bv_add.r_sub_const_r.swap

@[kanon_arm] theorem bv_add.r_sub_const_l.main.proof : bv_add.r_sub_const_l.main.Stmt := kanon_proof% bv_add.r_sub_const_l.main

@[kanon_arm] theorem bv_add.r_sub_const_l.swap.proof : bv_add.r_sub_const_l.swap.Stmt := kanon_proof% bv_add.r_sub_const_l.swap

@[kanon_arm] theorem bv_add.r_sub_cancel.main.proof : bv_add.r_sub_cancel.main.Stmt := kanon_proof% bv_add.r_sub_cancel.main

@[kanon_arm] theorem bv_add.r_add_sub.main.proof : bv_add.r_add_sub.main.Stmt := kanon_proof% bv_add.r_add_sub.main

end Kanon
