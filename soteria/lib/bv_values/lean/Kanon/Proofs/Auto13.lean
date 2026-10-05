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

@[kanon_arm] theorem Bitvec.and_.r_default.main.proof : Bitvec.and_.r_default.main.Stmt := kanon_proof% Bitvec.and_.r_default.main

@[kanon_arm] theorem Bitvec.or_.r_lits.main.proof : Bitvec.or_.r_lits.main.Stmt := kanon_proof% Bitvec.or_.r_lits.main

@[kanon_arm] theorem Bitvec.or_.r_zero.main.proof : Bitvec.or_.r_zero.main.Stmt := kanon_proof% Bitvec.or_.r_zero.main

@[kanon_arm] theorem Bitvec.or_.r_same.main.proof : Bitvec.or_.r_same.main.Stmt := kanon_proof% Bitvec.or_.r_same.main

@[kanon_arm] theorem Bitvec.or_.r_mask_and.main.proof : Bitvec.or_.r_mask_and.main.Stmt := kanon_proof% Bitvec.or_.r_mask_and.main

@[kanon_arm] theorem Bitvec.or_.r_masks.main.proof : Bitvec.or_.r_masks.main.Stmt := kanon_proof% Bitvec.or_.r_masks.main

@[kanon_arm] theorem Bitvec.or_.r_of_bools.main.proof : Bitvec.or_.r_of_bools.main.Stmt := kanon_proof% Bitvec.or_.r_of_bools.main

@[kanon_arm] theorem Bitvec.or_.r_default.main.proof : Bitvec.or_.r_default.main.Stmt := kanon_proof% Bitvec.or_.r_default.main

@[kanon_arm] theorem Bitvec.xor.r_lits.main.proof : Bitvec.xor.r_lits.main.Stmt := kanon_proof% Bitvec.xor.r_lits.main

@[kanon_arm] theorem Bitvec.xor.r_zero.main.proof : Bitvec.xor.r_zero.main.Stmt := kanon_proof% Bitvec.xor.r_zero.main
