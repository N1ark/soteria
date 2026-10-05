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

@[kanon_arm] theorem bv_of_bool.r_true_.main.proof : bv_of_bool.r_true_.main.Stmt := kanon_proof% bv_of_bool.r_true_.main

@[kanon_arm] theorem bv_of_bool.r_false_.main.proof : bv_of_bool.r_false_.main.Stmt := kanon_proof% bv_of_bool.r_false_.main

@[kanon_arm] theorem bv_of_bool.r_default.main.proof : bv_of_bool.r_default.main.Stmt := kanon_proof% bv_of_bool.r_default.main

@[kanon_arm] theorem bv_to_bool.r_of_bool.main.proof : bv_to_bool.r_of_bool.main.Stmt := kanon_proof% bv_to_bool.r_of_bool.main

@[kanon_arm] theorem bv_to_bool.r_default.main.proof : bv_to_bool.r_default.main.Stmt := kanon_proof% bv_to_bool.r_default.main

@[kanon_arm] theorem bv_not_bool.r_of_bool.main.proof : bv_not_bool.r_of_bool.main.Stmt := kanon_proof% bv_not_bool.r_of_bool.main

@[kanon_arm] theorem bv_not_bool.r_default.main.proof : bv_not_bool.r_default.main.Stmt := kanon_proof% bv_not_bool.r_default.main

@[kanon_arm] theorem bv_add.r_lits.main.proof : bv_add.r_lits.main.Stmt := kanon_proof% bv_add.r_lits.main

@[kanon_arm] theorem bv_add.r_neg.main.proof : bv_add.r_neg.main.Stmt := kanon_proof% bv_add.r_neg.main

@[kanon_arm] theorem bv_add.r_zero.main.proof : bv_add.r_zero.main.Stmt := kanon_proof% bv_add.r_zero.main

end Kanon
