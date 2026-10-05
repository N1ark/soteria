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

@[kanon_arm] theorem Bitvec.add.r_add_const.main.proof : Bitvec.add.r_add_const.main.Stmt := kanon_proof% Bitvec.add.r_add_const.main

@[kanon_arm] theorem Bitvec.add.r_sub_const_r.main.proof : Bitvec.add.r_sub_const_r.main.Stmt := kanon_proof% Bitvec.add.r_sub_const_r.main

@[kanon_arm] theorem Bitvec.add.r_sub_const_l.main.proof : Bitvec.add.r_sub_const_l.main.Stmt := kanon_proof% Bitvec.add.r_sub_const_l.main

@[kanon_arm] theorem Bitvec.add.r_sub_cancel.main.proof : Bitvec.add.r_sub_cancel.main.Stmt := kanon_proof% Bitvec.add.r_sub_cancel.main

@[kanon_arm] theorem Bitvec.add.r_add_sub.main.proof : Bitvec.add.r_add_sub.main.Stmt := kanon_proof% Bitvec.add.r_add_sub.main

@[kanon_arm] theorem Bitvec.add.r_factor.main.proof : Bitvec.add.r_factor.main.Stmt := kanon_proof% Bitvec.add.r_factor.main

@[kanon_arm] theorem Bitvec.add.r_factor_const.main.proof : Bitvec.add.r_factor_const.main.Stmt := kanon_proof% Bitvec.add.r_factor_const.main

@[kanon_arm] theorem Bitvec.add.r_ite.main.proof : Bitvec.add.r_ite.main.Stmt := kanon_proof% Bitvec.add.r_ite.main

@[kanon_arm] theorem Bitvec.sub.r_lits.main.proof : Bitvec.sub.r_lits.main.Stmt := kanon_proof% Bitvec.sub.r_lits.main

@[kanon_arm] theorem Bitvec.sub.r_zero_r.main.proof : Bitvec.sub.r_zero_r.main.Stmt := kanon_proof% Bitvec.sub.r_zero_r.main
