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

@[kanon_arm] theorem Bitvec.mul.r_ite.main.proof : Bitvec.mul.r_ite.main.Stmt := kanon_proof% Bitvec.mul.r_ite.main

@[kanon_arm] theorem Bitvec.mul.r_default.main.proof : Bitvec.mul.r_default.main.Stmt := kanon_proof% Bitvec.mul.r_default.main

@[kanon_arm] theorem Bitvec.div.r_lits.main.proof : Bitvec.div.r_lits.main.Stmt := kanon_proof% Bitvec.div.r_lits.main

@[kanon_arm] theorem Bitvec.div.r_one.main.proof : Bitvec.div.r_one.main.Stmt := kanon_proof% Bitvec.div.r_one.main

@[kanon_arm] theorem Bitvec.div.r_mul_lits.main.proof : Bitvec.div.r_mul_lits.main.Stmt := kanon_proof% Bitvec.div.r_mul_lits.main

@[kanon_arm] theorem Bitvec.div.r_mul_div.main.proof : Bitvec.div.r_mul_div.main.Stmt := kanon_proof% Bitvec.div.r_mul_div.main

@[kanon_arm] theorem Bitvec.div.r_mul_div.swap.proof : Bitvec.div.r_mul_div.swap.Stmt := kanon_proof% Bitvec.div.r_mul_div.swap

@[kanon_arm] theorem Bitvec.div.r_div_mul.main.proof : Bitvec.div.r_div_mul.main.Stmt := kanon_proof% Bitvec.div.r_div_mul.main

@[kanon_arm] theorem Bitvec.div.r_div_mul.swap.proof : Bitvec.div.r_div_mul.swap.Stmt := kanon_proof% Bitvec.div.r_div_mul.swap

@[kanon_arm] theorem Bitvec.div.r_div_div.main.proof : Bitvec.div.r_div_div.main.Stmt := kanon_proof% Bitvec.div.r_div_div.main
