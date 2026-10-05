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

@[kanon_arm] theorem Bitvec.xor.r_of_bools.main.proof : Bitvec.xor.r_of_bools.main.Stmt := kanon_proof% Bitvec.xor.r_of_bools.main

@[kanon_arm] theorem Bitvec.xor.r_default.main.proof : Bitvec.xor.r_default.main.Stmt := kanon_proof% Bitvec.xor.r_default.main

@[kanon_arm] theorem Bitvec.extract.r_lit.main.proof : Bitvec.extract.r_lit.main.Stmt := kanon_proof% Bitvec.extract.r_lit.main

@[kanon_arm] theorem Bitvec.extract.r_full.main.proof : Bitvec.extract.r_full.main.Stmt := kanon_proof% Bitvec.extract.r_full.main

@[kanon_arm] theorem Bitvec.extract.r_and_.main.proof : Bitvec.extract.r_and_.main.Stmt := kanon_proof% Bitvec.extract.r_and_.main

@[kanon_arm] theorem Bitvec.extract.r_or_.main.proof : Bitvec.extract.r_or_.main.Stmt := kanon_proof% Bitvec.extract.r_or_.main

@[kanon_arm] theorem Bitvec.extract.r_xor.main.proof : Bitvec.extract.r_xor.main.Stmt := kanon_proof% Bitvec.extract.r_xor.main

@[kanon_arm] theorem Bitvec.extract.r_shl.main.proof : Bitvec.extract.r_shl.main.Stmt := kanon_proof% Bitvec.extract.r_shl.main

@[kanon_arm] theorem Bitvec.extract.r_lshr.main.proof : Bitvec.extract.r_lshr.main.Stmt := kanon_proof% Bitvec.extract.r_lshr.main

@[kanon_arm] theorem Bitvec.extract.r_ite.main.proof : Bitvec.extract.r_ite.main.Stmt := kanon_proof% Bitvec.extract.r_ite.main
