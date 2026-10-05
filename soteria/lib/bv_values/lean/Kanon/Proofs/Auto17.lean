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

@[kanon_arm] theorem bv_extract.r_mul_pow2.main.proof : bv_extract.r_mul_pow2.main.Stmt := kanon_proof% bv_extract.r_mul_pow2.main

@[kanon_arm] theorem bv_extract.r_mul_low.main.proof : bv_extract.r_mul_low.main.Stmt := kanon_proof% bv_extract.r_mul_low.main

@[kanon_arm] theorem bv_extract.r_urem.main.proof : bv_extract.r_urem.main.Stmt := kanon_proof% bv_extract.r_urem.main

@[kanon_arm] theorem bv_extract.r_default.main.proof : bv_extract.r_default.main.Stmt := kanon_proof% bv_extract.r_default.main

@[kanon_arm] theorem bv_extend.r_zero.main.proof : bv_extend.r_zero.main.Stmt := kanon_proof% bv_extend.r_zero.main

@[kanon_arm] theorem bv_extend.r_lit.main.proof : bv_extend.r_lit.main.Stmt := kanon_proof% bv_extend.r_lit.main

@[kanon_arm] theorem bv_extend.r_extend.main.proof : bv_extend.r_extend.main.Stmt := kanon_proof% bv_extend.r_extend.main

@[kanon_arm] theorem bv_extend.r_ite.main.proof : bv_extend.r_ite.main.Stmt := kanon_proof% bv_extend.r_ite.main

@[kanon_arm] theorem bv_extend.r_of_bool.main.proof : bv_extend.r_of_bool.main.Stmt := kanon_proof% bv_extend.r_of_bool.main

@[kanon_arm] theorem bv_extend.r_default.main.proof : bv_extend.r_default.main.Stmt := kanon_proof% bv_extend.r_default.main

end Kanon
