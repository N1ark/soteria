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

@[kanon_arm] theorem bv_div.r_mul_lits.main.proof : bv_div.r_mul_lits.main.Stmt := kanon_proof% bv_div.r_mul_lits.main

@[kanon_arm] theorem bv_div.r_mul_div.main.proof : bv_div.r_mul_div.main.Stmt := kanon_proof% bv_div.r_mul_div.main

@[kanon_arm] theorem bv_div.r_mul_div.swap.proof : bv_div.r_mul_div.swap.Stmt := kanon_proof% bv_div.r_mul_div.swap

@[kanon_arm] theorem bv_div.r_div_mul.main.proof : bv_div.r_div_mul.main.Stmt := kanon_proof% bv_div.r_div_mul.main

@[kanon_arm] theorem bv_div.r_div_mul.swap.proof : bv_div.r_div_mul.swap.Stmt := kanon_proof% bv_div.r_div_mul.swap

@[kanon_arm] theorem bv_div.r_div_div.main.proof : bv_div.r_div_div.main.Stmt := kanon_proof% bv_div.r_div_div.main

@[kanon_arm] theorem bv_div.r_default.main.proof : bv_div.r_default.main.Stmt := kanon_proof% bv_div.r_default.main

@[kanon_arm] theorem bv_lt_zero.r_sext.main.proof : bv_lt_zero.r_sext.main.Stmt := kanon_proof% bv_lt_zero.r_sext.main

@[kanon_arm] theorem bv_lt_zero.r_zext.main.proof : bv_lt_zero.r_zext.main.Stmt := kanon_proof% bv_lt_zero.r_zext.main

@[kanon_arm] theorem bv_lt_zero.r_srem.main.proof : bv_lt_zero.r_srem.main.Stmt := kanon_proof% bv_lt_zero.r_srem.main

end Kanon
