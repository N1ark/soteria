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

@[kanon_arm] theorem bv_and.r_default.main.proof : bv_and.r_default.main.Stmt := kanon_proof% bv_and.r_default.main

@[kanon_arm] theorem bv_or.r_lits.main.proof : bv_or.r_lits.main.Stmt := kanon_proof% bv_or.r_lits.main

@[kanon_arm] theorem bv_or.r_zero.main.proof : bv_or.r_zero.main.Stmt := kanon_proof% bv_or.r_zero.main

@[kanon_arm] theorem bv_or.r_same.main.proof : bv_or.r_same.main.Stmt := kanon_proof% bv_or.r_same.main

@[kanon_arm] theorem bv_or.r_mask_and.main.proof : bv_or.r_mask_and.main.Stmt := kanon_proof% bv_or.r_mask_and.main

@[kanon_arm] theorem bv_or.r_masks.main.proof : bv_or.r_masks.main.Stmt := kanon_proof% bv_or.r_masks.main

@[kanon_arm] theorem bv_or.r_masks.swap2.proof : bv_or.r_masks.swap2.Stmt := kanon_proof% bv_or.r_masks.swap2

@[kanon_arm] theorem bv_or.r_masks.swap1_swap2.proof : bv_or.r_masks.swap1_swap2.Stmt := kanon_proof% bv_or.r_masks.swap1_swap2

@[kanon_arm] theorem bv_or.r_of_bools.main.proof : bv_or.r_of_bools.main.Stmt := kanon_proof% bv_or.r_of_bools.main

@[kanon_arm] theorem bv_or.r_default.main.proof : bv_or.r_default.main.Stmt := kanon_proof% bv_or.r_default.main

end Kanon
