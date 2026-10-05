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

@[kanon_arm] theorem sem_eq.r_bvs.bitVec_bitVec.proof : sem_eq.r_bvs.bitVec_bitVec.Stmt := kanon_proof% sem_eq.r_bvs.bitVec_bitVec

@[kanon_arm] theorem sem_eq.r_bvs.locLit_locLit.proof : sem_eq.r_bvs.locLit_locLit.Stmt := kanon_proof% sem_eq.r_bvs.locLit_locLit

@[kanon_arm] theorem sem_eq.r_neg.main.proof : sem_eq.r_neg.main.Stmt := kanon_proof% sem_eq.r_neg.main

@[kanon_arm] theorem sem_eq.r_not.main.proof : sem_eq.r_not.main.Stmt := kanon_proof% sem_eq.r_not.main

@[kanon_arm] theorem sem_eq.r_add_const.main.proof : sem_eq.r_add_const.main.Stmt := kanon_proof% sem_eq.r_add_const.main

@[kanon_arm] theorem sem_eq.r_sub_const1.main.proof : sem_eq.r_sub_const1.main.Stmt := kanon_proof% sem_eq.r_sub_const1.main

@[kanon_arm] theorem sem_eq.r_sub_const2.main.proof : sem_eq.r_sub_const2.main.Stmt := kanon_proof% sem_eq.r_sub_const2.main

@[kanon_arm] theorem sem_eq.r_self_add.main.proof : sem_eq.r_self_add.main.Stmt := kanon_proof% sem_eq.r_self_add.main

@[kanon_arm] theorem sem_eq.r_add_add.main.proof : sem_eq.r_add_add.main.Stmt := kanon_proof% sem_eq.r_add_add.main

@[kanon_arm] theorem sem_eq.r_or_zero.main.proof : sem_eq.r_or_zero.main.Stmt := kanon_proof% sem_eq.r_or_zero.main

@[kanon_arm] theorem sem_eq.r_or_zero.swap.proof : sem_eq.r_or_zero.swap.Stmt := kanon_proof% sem_eq.r_or_zero.swap

@[kanon_arm] theorem sem_eq.r_concat_const.main.proof : sem_eq.r_concat_const.main.Stmt := kanon_proof% sem_eq.r_concat_const.main

@[kanon_arm] theorem sem_eq.r_concat_concat.main.proof : sem_eq.r_concat_concat.main.Stmt := kanon_proof% sem_eq.r_concat_concat.main

@[kanon_arm] theorem sem_eq.r_ite_const.bitVec.proof : sem_eq.r_ite_const.bitVec.Stmt := kanon_proof% sem_eq.r_ite_const.bitVec

@[kanon_arm] theorem sem_eq.r_ite_const.locLit.proof : sem_eq.r_ite_const.locLit.Stmt := kanon_proof% sem_eq.r_ite_const.locLit

@[kanon_arm] theorem sem_eq.r_of_bools.main.proof : sem_eq.r_of_bools.main.Stmt := kanon_proof% sem_eq.r_of_bools.main

@[kanon_arm] theorem sem_eq.r_of_bool_const.main.proof : sem_eq.r_of_bool_const.main.Stmt := kanon_proof% sem_eq.r_of_bool_const.main

@[kanon_arm] theorem sem_eq.r_msb.main.proof : sem_eq.r_msb.main.Stmt := kanon_proof% sem_eq.r_msb.main

@[kanon_arm] theorem sem_eq.r_floats.main.proof : sem_eq.r_floats.main.Stmt := kanon_proof% sem_eq.r_floats.main

@[kanon_arm] theorem sem_eq.r_ptrs.main.proof : sem_eq.r_ptrs.main.Stmt := kanon_proof% sem_eq.r_ptrs.main

@[kanon_arm] theorem bv_of_bool.r_true_.main.proof : bv_of_bool.r_true_.main.Stmt := kanon_proof% bv_of_bool.r_true_.main

@[kanon_arm] theorem bv_of_bool.r_false_.main.proof : bv_of_bool.r_false_.main.Stmt := kanon_proof% bv_of_bool.r_false_.main

@[kanon_arm] theorem bv_of_bool.r_default.main.proof : bv_of_bool.r_default.main.Stmt := kanon_proof% bv_of_bool.r_default.main

@[kanon_arm] theorem bv_to_bool.r_of_bool.main.proof : bv_to_bool.r_of_bool.main.Stmt := kanon_proof% bv_to_bool.r_of_bool.main

@[kanon_arm] theorem bv_to_bool.r_default.main.proof : bv_to_bool.r_default.main.Stmt := kanon_proof% bv_to_bool.r_default.main

@[kanon_arm] theorem bv_not_bool.r_of_bool.main.proof : bv_not_bool.r_of_bool.main.Stmt := kanon_proof% bv_not_bool.r_of_bool.main

@[kanon_arm] theorem bv_not_bool.r_default.main.proof : bv_not_bool.r_default.main.Stmt := kanon_proof% bv_not_bool.r_default.main

@[kanon_arm] theorem bv_add.r_lits.main.proof : bv_add.r_lits.main.Stmt := kanon_proof% bv_add.r_lits.main

@[kanon_arm] theorem bv_add.r_neg.main.proof : bv_add.r_neg.main.Stmt := kanon_proof% bv_add.r_neg.main

@[kanon_arm] theorem bv_add.r_zero.main.proof : bv_add.r_zero.main.Stmt := kanon_proof% bv_add.r_zero.main

end Kanon
