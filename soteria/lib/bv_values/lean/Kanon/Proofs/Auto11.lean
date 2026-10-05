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

@[kanon_arm] theorem bv_rem.r_lits.main.proof : bv_rem.r_lits.main.Stmt := kanon_proof% bv_rem.r_lits.main

@[kanon_arm] theorem bv_rem.r_zero_r.main.proof : bv_rem.r_zero_r.main.Stmt := kanon_proof% bv_rem.r_zero_r.main

@[kanon_arm] theorem bv_rem.r_zero_l.main.proof : bv_rem.r_zero_l.main.Stmt := kanon_proof% bv_rem.r_zero_l.main

@[kanon_arm] theorem bv_rem.r_one_r.main.proof : bv_rem.r_one_r.main.Stmt := kanon_proof% bv_rem.r_one_r.main

@[kanon_arm] theorem bv_rem.r_pow2.main.proof : bv_rem.r_pow2.main.Stmt := kanon_proof% bv_rem.r_pow2.main

@[kanon_arm] theorem bv_rem.r_add.main.proof : bv_rem.r_add.main.Stmt := kanon_proof% bv_rem.r_add.main

@[kanon_arm] theorem bv_rem.r_add.swap.proof : bv_rem.r_add.swap.Stmt := kanon_proof% bv_rem.r_add.swap

@[kanon_arm] theorem bv_rem.r_rem_rem.main.proof : bv_rem.r_rem_rem.main.Stmt := kanon_proof% bv_rem.r_rem_rem.main

@[kanon_arm] theorem bv_rem.r_default.main.proof : bv_rem.r_default.main.Stmt := kanon_proof% bv_rem.r_default.main

@[kanon_arm] theorem bv_not.r_lit.main.proof : bv_not.r_lit.main.Stmt := kanon_proof% bv_not.r_lit.main

end Kanon
