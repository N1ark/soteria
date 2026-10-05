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

@[kanon_arm] theorem bv_add_overflows.r_of_bool.swap.proof : bv_add_overflows.r_of_bool.swap.Stmt := kanon_proof% bv_add_overflows.r_of_bool.swap

@[kanon_arm] theorem bv_add_overflows.r_default.main.proof : bv_add_overflows.r_default.main.Stmt := kanon_proof% bv_add_overflows.r_default.main

@[kanon_arm] theorem bv_mul_overflows.r_lits.main.proof : bv_mul_overflows.r_lits.main.Stmt := kanon_proof% bv_mul_overflows.r_lits.main

@[kanon_arm] theorem bv_mul_overflows.r_size1.main.proof : bv_mul_overflows.r_size1.main.Stmt := kanon_proof% bv_mul_overflows.r_size1.main

@[kanon_arm] theorem bv_mul_overflows.r_msb.main.proof : bv_mul_overflows.r_msb.main.Stmt := kanon_proof% bv_mul_overflows.r_msb.main

@[kanon_arm] theorem bv_mul_overflows.r_const.main.proof : bv_mul_overflows.r_const.main.Stmt := kanon_proof% bv_mul_overflows.r_const.main

@[kanon_arm] theorem bv_mul_overflows.r_const.swap.proof : bv_mul_overflows.r_const.swap.Stmt := kanon_proof% bv_mul_overflows.r_const.swap

@[kanon_arm] theorem bv_mul_overflows.r_div.main.proof : bv_mul_overflows.r_div.main.Stmt := kanon_proof% bv_mul_overflows.r_div.main

@[kanon_arm] theorem bv_mul_overflows.r_default.main.proof : bv_mul_overflows.r_default.main.Stmt := kanon_proof% bv_mul_overflows.r_default.main

@[kanon_arm] theorem bv_neg_overflows.r_main.main.proof : bv_neg_overflows.r_main.main.Stmt := kanon_proof% bv_neg_overflows.r_main.main

end Kanon
