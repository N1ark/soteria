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

@[kanon_arm] theorem float_add.r_default.main.proof : float_add.r_default.main.Stmt := kanon_proof% float_add.r_default.main

@[kanon_arm] theorem float_sub.r_lits.main.proof : float_sub.r_lits.main.Stmt := kanon_proof% float_sub.r_lits.main

@[kanon_arm] theorem float_sub.r_default.main.proof : float_sub.r_default.main.Stmt := kanon_proof% float_sub.r_default.main

@[kanon_arm] theorem float_div.r_lits.main.proof : float_div.r_lits.main.Stmt := kanon_proof% float_div.r_lits.main

@[kanon_arm] theorem float_div.r_default.main.proof : float_div.r_default.main.Stmt := kanon_proof% float_div.r_default.main

@[kanon_arm] theorem float_mul.r_lits.main.proof : float_mul.r_lits.main.Stmt := kanon_proof% float_mul.r_lits.main

@[kanon_arm] theorem float_mul.r_default.main.proof : float_mul.r_default.main.Stmt := kanon_proof% float_mul.r_default.main

@[kanon_arm] theorem float_rem.r_lits.main.proof : float_rem.r_lits.main.Stmt := kanon_proof% float_rem.r_lits.main

@[kanon_arm] theorem float_rem.r_default.main.proof : float_rem.r_default.main.Stmt := kanon_proof% float_rem.r_default.main

@[kanon_arm] theorem float_abs.r_lit.main.proof : float_abs.r_lit.main.Stmt := kanon_proof% float_abs.r_lit.main

end Kanon
