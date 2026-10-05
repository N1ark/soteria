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

@[kanon_arm] theorem Bitvec.extract.r_urem.main.proof : Bitvec.extract.r_urem.main.Stmt := kanon_proof% Bitvec.extract.r_urem.main

@[kanon_arm] theorem Bitvec.extract.r_default.main.proof : Bitvec.extract.r_default.main.Stmt := kanon_proof% Bitvec.extract.r_default.main

@[kanon_arm] theorem Bitvec.extend_.r_zero.main.proof : Bitvec.extend_.r_zero.main.Stmt := kanon_proof% Bitvec.extend_.r_zero.main

@[kanon_arm] theorem Bitvec.extend_.r_lit.main.proof : Bitvec.extend_.r_lit.main.Stmt := kanon_proof% Bitvec.extend_.r_lit.main

@[kanon_arm] theorem Bitvec.extend_.r_extend.main.proof : Bitvec.extend_.r_extend.main.Stmt := kanon_proof% Bitvec.extend_.r_extend.main

@[kanon_arm] theorem Bitvec.extend_.r_ite.main.proof : Bitvec.extend_.r_ite.main.Stmt := kanon_proof% Bitvec.extend_.r_ite.main

@[kanon_arm] theorem Bitvec.extend_.r_of_bool.main.proof : Bitvec.extend_.r_of_bool.main.Stmt := kanon_proof% Bitvec.extend_.r_of_bool.main

@[kanon_arm] theorem Bitvec.extend_.r_default.main.proof : Bitvec.extend_.r_default.main.Stmt := kanon_proof% Bitvec.extend_.r_default.main

@[kanon_arm] theorem Bitvec.concat.r_lits.main.proof : Bitvec.concat.r_lits.main.Stmt := kanon_proof% Bitvec.concat.r_lits.main

@[kanon_arm] theorem Bitvec.concat.r_extracts.main.proof : Bitvec.concat.r_extracts.main.Stmt := kanon_proof% Bitvec.concat.r_extracts.main
