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

@[kanon_arm] theorem bv_xor.r_lits.main.proof : bv_xor.r_lits.main.Stmt := kanon_proof% bv_xor.r_lits.main

@[kanon_arm] theorem bv_xor.r_zero.main.proof : bv_xor.r_zero.main.Stmt := kanon_proof% bv_xor.r_zero.main

@[kanon_arm] theorem bv_xor.r_of_bools.main.proof : bv_xor.r_of_bools.main.Stmt := kanon_proof% bv_xor.r_of_bools.main

@[kanon_arm] theorem bv_xor.r_default.main.proof : bv_xor.r_default.main.Stmt := kanon_proof% bv_xor.r_default.main

@[kanon_arm] theorem bv_extract.r_lit.main.proof : bv_extract.r_lit.main.Stmt := kanon_proof% bv_extract.r_lit.main

@[kanon_arm] theorem bv_extract.r_full.main.proof : bv_extract.r_full.main.Stmt := kanon_proof% bv_extract.r_full.main

@[kanon_arm] theorem bv_extract.r_and_.main.proof : bv_extract.r_and_.main.Stmt := kanon_proof% bv_extract.r_and_.main

@[kanon_arm] theorem bv_extract.r_or_.main.proof : bv_extract.r_or_.main.Stmt := kanon_proof% bv_extract.r_or_.main

@[kanon_arm] theorem bv_extract.r_xor.main.proof : bv_extract.r_xor.main.Stmt := kanon_proof% bv_extract.r_xor.main

@[kanon_arm] theorem bv_extract.r_shl.main.proof : bv_extract.r_shl.main.Stmt := kanon_proof% bv_extract.r_shl.main

end Kanon
