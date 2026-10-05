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

@[kanon_arm] theorem Bitvec.and_.r_lshr_mask.main.proof : Bitvec.and_.r_lshr_mask.main.Stmt := kanon_proof% Bitvec.and_.r_lshr_mask.main

@[kanon_arm] theorem Bitvec.and_.r_ite.main.proof : Bitvec.and_.r_ite.main.Stmt := kanon_proof% Bitvec.and_.r_ite.main

@[kanon_arm] theorem Bitvec.and_.r_masks.main.proof : Bitvec.and_.r_masks.main.Stmt := kanon_proof% Bitvec.and_.r_masks.main

@[kanon_arm] theorem Bitvec.and_.r_mask_or_mask.main.proof : Bitvec.and_.r_mask_or_mask.main.Stmt := kanon_proof% Bitvec.and_.r_mask_or_mask.main

@[kanon_arm] theorem Bitvec.and_.r_mask_or.main.proof : Bitvec.and_.r_mask_or.main.Stmt := kanon_proof% Bitvec.and_.r_mask_or.main

@[kanon_arm] theorem Bitvec.and_.r_mask_or_disj.main.proof : Bitvec.and_.r_mask_or_disj.main.Stmt := kanon_proof% Bitvec.and_.r_mask_or_disj.main

@[kanon_arm] theorem Bitvec.and_.r_right_mask.main.proof : Bitvec.and_.r_right_mask.main.Stmt := kanon_proof% Bitvec.and_.r_right_mask.main

@[kanon_arm] theorem Bitvec.and_.r_of_bool.main.proof : Bitvec.and_.r_of_bool.main.Stmt := kanon_proof% Bitvec.and_.r_of_bool.main

@[kanon_arm] theorem Bitvec.and_.r_of_bools.main.proof : Bitvec.and_.r_of_bools.main.Stmt := kanon_proof% Bitvec.and_.r_of_bools.main

@[kanon_arm] theorem Bitvec.and_.r_ites.main.proof : Bitvec.and_.r_ites.main.Stmt := kanon_proof% Bitvec.and_.r_ites.main
