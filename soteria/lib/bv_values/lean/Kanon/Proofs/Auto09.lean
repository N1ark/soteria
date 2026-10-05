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

@[kanon_arm] theorem bv_lt.r_of_bool.main.proof : bv_lt.r_of_bool.main.Stmt := kanon_proof% bv_lt.r_of_bool.main

@[kanon_arm] theorem bv_lt.r_ite_l.main.proof : bv_lt.r_ite_l.main.Stmt := kanon_proof% bv_lt.r_ite_l.main

@[kanon_arm] theorem bv_lt.r_ite_r.main.proof : bv_lt.r_ite_r.main.Stmt := kanon_proof% bv_lt.r_ite_r.main

@[kanon_arm] theorem bv_lt.r_lt_zero.main.proof : bv_lt.r_lt_zero.main.Stmt := kanon_proof% bv_lt.r_lt_zero.main

@[kanon_arm] theorem bv_lt.r_max_l.main.proof : bv_lt.r_max_l.main.Stmt := kanon_proof% bv_lt.r_max_l.main

@[kanon_arm] theorem bv_lt.r_min_r.main.proof : bv_lt.r_min_r.main.Stmt := kanon_proof% bv_lt.r_min_r.main

@[kanon_arm] theorem bv_lt.r_min_l.main.proof : bv_lt.r_min_l.main.Stmt := kanon_proof% bv_lt.r_min_l.main

@[kanon_arm] theorem bv_lt.r_max_r.main.proof : bv_lt.r_max_r.main.Stmt := kanon_proof% bv_lt.r_max_r.main

@[kanon_arm] theorem bv_lt.r_const_mul.main.proof : bv_lt.r_const_mul.main.Stmt := kanon_proof% bv_lt.r_const_mul.main

@[kanon_arm] theorem bv_lt.r_mul_const.main.proof : bv_lt.r_mul_const.main.Stmt := kanon_proof% bv_lt.r_mul_const.main

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

@[kanon_arm] theorem bv_leq.r_same.main.proof : bv_leq.r_same.main.Stmt := kanon_proof% bv_leq.r_same.main

@[kanon_arm] theorem bv_leq.r_lits.main.proof : bv_leq.r_lits.main.Stmt := kanon_proof% bv_leq.r_lits.main

@[kanon_arm] theorem bv_leq.r_negs.main.proof : bv_leq.r_negs.main.Stmt := kanon_proof% bv_leq.r_negs.main

@[kanon_arm] theorem bv_leq.r_neg_l.main.proof : bv_leq.r_neg_l.main.Stmt := kanon_proof% bv_leq.r_neg_l.main

@[kanon_arm] theorem bv_leq.r_neg_r.main.proof : bv_leq.r_neg_r.main.Stmt := kanon_proof% bv_leq.r_neg_r.main

@[kanon_arm] theorem bv_leq.r_const_add.main.proof : bv_leq.r_const_add.main.Stmt := kanon_proof% bv_leq.r_const_add.main

@[kanon_arm] theorem bv_leq.r_const_add.swap.proof : bv_leq.r_const_add.swap.Stmt := kanon_proof% bv_leq.r_const_add.swap

@[kanon_arm] theorem bv_leq.r_add_const.main.proof : bv_leq.r_add_const.main.Stmt := kanon_proof% bv_leq.r_add_const.main

@[kanon_arm] theorem bv_leq.r_add_const.swap.proof : bv_leq.r_add_const.swap.Stmt := kanon_proof% bv_leq.r_add_const.swap

@[kanon_arm] theorem bv_leq.r_add_add.main.proof : bv_leq.r_add_add.main.Stmt := kanon_proof% bv_leq.r_add_add.main

end Kanon
