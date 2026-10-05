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

@[kanon_arm] theorem float_abs.r_default.main.proof : float_abs.r_default.main.Stmt := kanon_proof% float_abs.r_default.main

@[kanon_arm] theorem float_neg.r_lit.main.proof : float_neg.r_lit.main.Stmt := kanon_proof% float_neg.r_lit.main

@[kanon_arm] theorem float_neg.r_default.main.proof : float_neg.r_default.main.Stmt := kanon_proof% float_neg.r_default.main

@[kanon_arm] theorem float_fma.r_default.main.proof : float_fma.r_default.main.Stmt := kanon_proof% float_fma.r_default.main

@[kanon_arm] theorem float_fmod_of_rem.r_main.main.proof : float_fmod_of_rem.r_main.main.Stmt := kanon_proof% float_fmod_of_rem.r_main.main

@[kanon_arm] theorem float_fmod.r_default.main.proof : float_fmod.r_default.main.Stmt := kanon_proof% float_fmod.r_default.main

@[kanon_arm] theorem float_min.r_lits.main.proof : float_min.r_lits.main.Stmt := kanon_proof% float_min.r_lits.main

@[kanon_arm] theorem float_min.r_default.main.proof : float_min.r_default.main.Stmt := kanon_proof% float_min.r_default.main

@[kanon_arm] theorem float_max.r_lits.main.proof : float_max.r_lits.main.Stmt := kanon_proof% float_max.r_lits.main

@[kanon_arm] theorem float_max.r_default.main.proof : float_max.r_default.main.Stmt := kanon_proof% float_max.r_default.main

end Kanon
