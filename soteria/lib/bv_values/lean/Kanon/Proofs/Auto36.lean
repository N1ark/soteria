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

@[kanon_arm] theorem float_sqrt.r_lit.main.proof : float_sqrt.r_lit.main.Stmt := kanon_proof% float_sqrt.r_lit.main

@[kanon_arm] theorem float_sqrt.r_default.main.proof : float_sqrt.r_default.main.Stmt := kanon_proof% float_sqrt.r_default.main

@[kanon_arm] theorem float_round.r_lit.main.proof : float_round.r_lit.main.Stmt := kanon_proof% float_round.r_lit.main

@[kanon_arm] theorem float_round.r_default.main.proof : float_round.r_default.main.Stmt := kanon_proof% float_round.r_default.main

@[kanon_arm] theorem ptr_loc.r_ptr.main.proof : ptr_loc.r_ptr.main.Stmt := kanon_proof% ptr_loc.r_ptr.main

@[kanon_arm] theorem ptr_loc.r_default.main.proof : ptr_loc.r_default.main.Stmt := kanon_proof% ptr_loc.r_default.main

@[kanon_arm] theorem ptr_ofs.r_ptr.main.proof : ptr_ofs.r_ptr.main.Stmt := kanon_proof% ptr_ofs.r_ptr.main

@[kanon_arm] theorem ptr_ofs.r_default.main.proof : ptr_ofs.r_default.main.Stmt := kanon_proof% ptr_ofs.r_default.main

end Kanon
