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

@[kanon_arm] theorem float_is_negative.r_default.main.proof : float_is_negative.r_default.main.Stmt := kanon_proof% float_is_negative.r_default.main

@[kanon_arm] theorem float_is_positive.r_lit.main.proof : float_is_positive.r_lit.main.Stmt := kanon_proof% float_is_positive.r_lit.main

@[kanon_arm] theorem float_is_positive.r_default.main.proof : float_is_positive.r_default.main.Stmt := kanon_proof% float_is_positive.r_default.main

@[kanon_arm] theorem float_cast.r_default.main.proof : float_cast.r_default.main.Stmt := kanon_proof% float_cast.r_default.main

@[kanon_arm] theorem float_eq.r_lits.main.proof : float_eq.r_lits.main.Stmt := kanon_proof% float_eq.r_lits.main

@[kanon_arm] theorem float_lt.r_lits.main.proof : float_lt.r_lits.main.Stmt := kanon_proof% float_lt.r_lits.main

@[kanon_arm] theorem float_lt.r_default.main.proof : float_lt.r_default.main.Stmt := kanon_proof% float_lt.r_default.main

@[kanon_arm] theorem float_leq.r_lits.main.proof : float_leq.r_lits.main.Stmt := kanon_proof% float_leq.r_lits.main

@[kanon_arm] theorem float_leq.r_default.main.proof : float_leq.r_default.main.Stmt := kanon_proof% float_leq.r_default.main

@[kanon_arm] theorem float_add.r_lits.main.proof : float_add.r_lits.main.Stmt := kanon_proof% float_add.r_lits.main

end Kanon
