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

@[kanon_arm] theorem bv_lshr.r_or_mask.main.proof : bv_lshr.r_or_mask.main.Stmt := kanon_proof% bv_lshr.r_or_mask.main

@[kanon_arm] theorem bv_lshr.r_default.main.proof : bv_lshr.r_default.main.Stmt := kanon_proof% bv_lshr.r_default.main

@[kanon_arm] theorem bv_ashr.r_lits.main.proof : bv_ashr.r_lits.main.Stmt := kanon_proof% bv_ashr.r_lits.main

@[kanon_arm] theorem bv_ashr.r_zero.main.proof : bv_ashr.r_zero.main.Stmt := kanon_proof% bv_ashr.r_zero.main

@[kanon_arm] theorem bv_ashr.r_big.main.proof : bv_ashr.r_big.main.Stmt := kanon_proof% bv_ashr.r_big.main

@[kanon_arm] theorem bv_ashr.r_ashr.main.proof : bv_ashr.r_ashr.main.Stmt := kanon_proof% bv_ashr.r_ashr.main

@[kanon_arm] theorem bv_ashr.r_default.main.proof : bv_ashr.r_default.main.Stmt := kanon_proof% bv_ashr.r_default.main

@[kanon_arm] theorem bv_mul.r_lits.main.proof : bv_mul.r_lits.main.Stmt := kanon_proof% bv_mul.r_lits.main

@[kanon_arm] theorem bv_mul.r_one.main.proof : bv_mul.r_one.main.Stmt := kanon_proof% bv_mul.r_one.main

@[kanon_arm] theorem bv_mul.r_zero.main.proof : bv_mul.r_zero.main.Stmt := kanon_proof% bv_mul.r_zero.main

end Kanon
