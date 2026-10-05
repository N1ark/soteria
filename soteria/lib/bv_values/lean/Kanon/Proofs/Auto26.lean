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

@[kanon_arm] theorem bv_lt.r_mul_mul.main.proof : bv_lt.r_mul_mul.main.Stmt := kanon_proof% bv_lt.r_mul_mul.main

@[kanon_arm] theorem bv_lt.r_const_sub1.main.proof : bv_lt.r_const_sub1.main.Stmt := kanon_proof% bv_lt.r_const_sub1.main

@[kanon_arm] theorem bv_lt.r_const_sub2.main.proof : bv_lt.r_const_sub2.main.Stmt := kanon_proof% bv_lt.r_const_sub2.main

@[kanon_arm] theorem bv_lt.r_sub_const1.main.proof : bv_lt.r_sub_const1.main.Stmt := kanon_proof% bv_lt.r_sub_const1.main

@[kanon_arm] theorem bv_lt.r_sub_const2.main.proof : bv_lt.r_sub_const2.main.Stmt := kanon_proof% bv_lt.r_sub_const2.main

@[kanon_arm] theorem bv_lt.r_ub_r.main.proof : bv_lt.r_ub_r.main.Stmt := kanon_proof% bv_lt.r_ub_r.main

@[kanon_arm] theorem bv_lt.r_ub_l.main.proof : bv_lt.r_ub_l.main.Stmt := kanon_proof% bv_lt.r_ub_l.main

@[kanon_arm] theorem bv_lt.r_to_unsigned_l.main.proof : bv_lt.r_to_unsigned_l.main.Stmt := kanon_proof% bv_lt.r_to_unsigned_l.main

@[kanon_arm] theorem bv_lt.r_to_unsigned_r.main.proof : bv_lt.r_to_unsigned_r.main.Stmt := kanon_proof% bv_lt.r_to_unsigned_r.main

@[kanon_arm] theorem bv_lt.r_default.main.proof : bv_lt.r_default.main.Stmt := kanon_proof% bv_lt.r_default.main

end Kanon
