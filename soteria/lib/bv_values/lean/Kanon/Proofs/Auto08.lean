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

@[kanon_arm] theorem bv_add.r_factor.main.proof : bv_add.r_factor.main.Stmt := kanon_proof% bv_add.r_factor.main

@[kanon_arm] theorem bv_add.r_factor_const.main.proof : bv_add.r_factor_const.main.Stmt := kanon_proof% bv_add.r_factor_const.main

@[kanon_arm] theorem bv_add.r_ite.main.proof : bv_add.r_ite.main.Stmt := kanon_proof% bv_add.r_ite.main

@[kanon_arm] theorem bv_sub.r_lits.main.proof : bv_sub.r_lits.main.Stmt := kanon_proof% bv_sub.r_lits.main

@[kanon_arm] theorem bv_sub.r_zero_r.main.proof : bv_sub.r_zero_r.main.Stmt := kanon_proof% bv_sub.r_zero_r.main

@[kanon_arm] theorem bv_sub.r_zero_l.main.proof : bv_sub.r_zero_l.main.Stmt := kanon_proof% bv_sub.r_zero_l.main

@[kanon_arm] theorem bv_sub.r_same.main.proof : bv_sub.r_same.main.Stmt := kanon_proof% bv_sub.r_same.main

@[kanon_arm] theorem bv_sub.r_neg_r.main.proof : bv_sub.r_neg_r.main.Stmt := kanon_proof% bv_sub.r_neg_r.main

@[kanon_arm] theorem bv_sub.r_sub_const_l.main.proof : bv_sub.r_sub_const_l.main.Stmt := kanon_proof% bv_sub.r_sub_const_l.main

@[kanon_arm] theorem bv_sub.r_sub_const_r.main.proof : bv_sub.r_sub_const_r.main.Stmt := kanon_proof% bv_sub.r_sub_const_r.main

end Kanon
