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

@[kanon_arm] theorem bv_and.r_masks.main.proof : bv_and.r_masks.main.Stmt := kanon_proof% bv_and.r_masks.main

@[kanon_arm] theorem bv_and.r_masks.swap2.proof : bv_and.r_masks.swap2.Stmt := kanon_proof% bv_and.r_masks.swap2

@[kanon_arm] theorem bv_and.r_masks.swap1_swap2.proof : bv_and.r_masks.swap1_swap2.Stmt := kanon_proof% bv_and.r_masks.swap1_swap2

@[kanon_arm] theorem bv_and.r_mask_or_mask.main.proof : bv_and.r_mask_or_mask.main.Stmt := kanon_proof% bv_and.r_mask_or_mask.main

@[kanon_arm] theorem bv_and.r_mask_or.main.proof : bv_and.r_mask_or.main.Stmt := kanon_proof% bv_and.r_mask_or.main

@[kanon_arm] theorem bv_and.r_mask_or_disj.main.proof : bv_and.r_mask_or_disj.main.Stmt := kanon_proof% bv_and.r_mask_or_disj.main

@[kanon_arm] theorem bv_and.r_right_mask.main.proof : bv_and.r_right_mask.main.Stmt := kanon_proof% bv_and.r_right_mask.main

@[kanon_arm] theorem bv_and.r_of_bool.main.proof : bv_and.r_of_bool.main.Stmt := kanon_proof% bv_and.r_of_bool.main

@[kanon_arm] theorem bv_and.r_of_bools.main.proof : bv_and.r_of_bools.main.Stmt := kanon_proof% bv_and.r_of_bools.main

@[kanon_arm] theorem bv_and.r_ites.main.proof : bv_and.r_ites.main.Stmt := kanon_proof% bv_and.r_ites.main

end Kanon
