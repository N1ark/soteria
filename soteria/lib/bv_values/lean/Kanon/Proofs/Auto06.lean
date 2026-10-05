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

@[kanon_arm] theorem Bitvec.of_bool.r_false_.main.proof : Bitvec.of_bool.r_false_.main.Stmt := kanon_proof% Bitvec.of_bool.r_false_.main

@[kanon_arm] theorem Bitvec.of_bool.r_default.main.proof : Bitvec.of_bool.r_default.main.Stmt := kanon_proof% Bitvec.of_bool.r_default.main

@[kanon_arm] theorem Bitvec.to_bool.r_of_bool.main.proof : Bitvec.to_bool.r_of_bool.main.Stmt := kanon_proof% Bitvec.to_bool.r_of_bool.main

@[kanon_arm] theorem Bitvec.to_bool.r_default.main.proof : Bitvec.to_bool.r_default.main.Stmt := kanon_proof% Bitvec.to_bool.r_default.main

@[kanon_arm] theorem Bitvec.not_bool.r_of_bool.main.proof : Bitvec.not_bool.r_of_bool.main.Stmt := kanon_proof% Bitvec.not_bool.r_of_bool.main

@[kanon_arm] theorem Bitvec.not_bool.r_default.main.proof : Bitvec.not_bool.r_default.main.Stmt := kanon_proof% Bitvec.not_bool.r_default.main

@[kanon_arm] theorem Bitvec.add.r_lits.main.proof : Bitvec.add.r_lits.main.Stmt := kanon_proof% Bitvec.add.r_lits.main

@[kanon_arm] theorem Bitvec.add.r_neg.main.proof : Bitvec.add.r_neg.main.Stmt := kanon_proof% Bitvec.add.r_neg.main

@[kanon_arm] theorem Bitvec.add.r_zero.main.proof : Bitvec.add.r_zero.main.Stmt := kanon_proof% Bitvec.add.r_zero.main

@[kanon_arm] theorem Bitvec.add.r_not_one.main.proof : Bitvec.add.r_not_one.main.Stmt := kanon_proof% Bitvec.add.r_not_one.main
