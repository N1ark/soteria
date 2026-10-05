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

@[kanon_arm] theorem bv_concat.r_lits.main.proof : bv_concat.r_lits.main.Stmt := kanon_proof% bv_concat.r_lits.main

@[kanon_arm] theorem bv_concat.r_extracts.main.proof : bv_concat.r_extracts.main.Stmt := kanon_proof% bv_concat.r_extracts.main

@[kanon_arm] theorem bv_concat.r_extract_extracts.main.proof : bv_concat.r_extract_extracts.main.Stmt := kanon_proof% bv_concat.r_extract_extracts.main

@[kanon_arm] theorem bv_concat.r_assoc_l.main.proof : bv_concat.r_assoc_l.main.Stmt := kanon_proof% bv_concat.r_assoc_l.main

@[kanon_arm] theorem bv_concat.r_assoc_r.main.proof : bv_concat.r_assoc_r.main.Stmt := kanon_proof% bv_concat.r_assoc_r.main

@[kanon_arm] theorem bv_concat.r_ites.main.proof : bv_concat.r_ites.main.Stmt := kanon_proof% bv_concat.r_ites.main

@[kanon_arm] theorem bv_concat.r_default.main.proof : bv_concat.r_default.main.Stmt := kanon_proof% bv_concat.r_default.main

@[kanon_arm] theorem bv_shl.r_lits.main.proof : bv_shl.r_lits.main.Stmt := kanon_proof% bv_shl.r_lits.main

@[kanon_arm] theorem bv_shl.r_zero.main.proof : bv_shl.r_zero.main.Stmt := kanon_proof% bv_shl.r_zero.main

@[kanon_arm] theorem bv_shl.r_big.main.proof : bv_shl.r_big.main.Stmt := kanon_proof% bv_shl.r_big.main

end Kanon
