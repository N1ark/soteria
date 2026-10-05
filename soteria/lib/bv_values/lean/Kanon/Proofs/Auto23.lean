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

@[kanon_arm] theorem bv_lt_zero.r_concat.main.proof : bv_lt_zero.r_concat.main.Stmt := kanon_proof% bv_lt_zero.r_concat.main

@[kanon_arm] theorem bv_lt_zero.r_not.main.proof : bv_lt_zero.r_not.main.Stmt := kanon_proof% bv_lt_zero.r_not.main

@[kanon_arm] theorem bv_lt_zero.r_of_bool.main.proof : bv_lt_zero.r_of_bool.main.Stmt := kanon_proof% bv_lt_zero.r_of_bool.main

@[kanon_arm] theorem bv_lt_zero.r_default.main.proof : bv_lt_zero.r_default.main.Stmt := kanon_proof% bv_lt_zero.r_default.main

@[kanon_arm] theorem bv_lt.r_lits.main.proof : bv_lt.r_lits.main.Stmt := kanon_proof% bv_lt.r_lits.main

@[kanon_arm] theorem bv_lt.r_same.main.proof : bv_lt.r_same.main.Stmt := kanon_proof% bv_lt.r_same.main

@[kanon_arm] theorem bv_lt.r_negs.main.proof : bv_lt.r_negs.main.Stmt := kanon_proof% bv_lt.r_negs.main

@[kanon_arm] theorem bv_lt.r_neg_l.main.proof : bv_lt.r_neg_l.main.Stmt := kanon_proof% bv_lt.r_neg_l.main

@[kanon_arm] theorem bv_lt.r_neg_r.main.proof : bv_lt.r_neg_r.main.Stmt := kanon_proof% bv_lt.r_neg_r.main

@[kanon_arm] theorem bv_lt.r_const_add.main.proof : bv_lt.r_const_add.main.Stmt := kanon_proof% bv_lt.r_const_add.main

end Kanon
