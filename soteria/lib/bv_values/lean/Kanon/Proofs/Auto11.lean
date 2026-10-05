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

@[kanon_arm] theorem bv_add_overflows.r_of_bool.swap.proof : bv_add_overflows.r_of_bool.swap.Stmt := kanon_proof% bv_add_overflows.r_of_bool.swap

@[kanon_arm] theorem bv_add_overflows.r_default.main.proof : bv_add_overflows.r_default.main.Stmt := kanon_proof% bv_add_overflows.r_default.main

@[kanon_arm] theorem bv_mul_overflows.r_lits.main.proof : bv_mul_overflows.r_lits.main.Stmt := kanon_proof% bv_mul_overflows.r_lits.main

@[kanon_arm] theorem bv_mul_overflows.r_size1.main.proof : bv_mul_overflows.r_size1.main.Stmt := kanon_proof% bv_mul_overflows.r_size1.main

@[kanon_arm] theorem bv_mul_overflows.r_msb.main.proof : bv_mul_overflows.r_msb.main.Stmt := kanon_proof% bv_mul_overflows.r_msb.main

@[kanon_arm] theorem bv_mul_overflows.r_const.main.proof : bv_mul_overflows.r_const.main.Stmt := kanon_proof% bv_mul_overflows.r_const.main

@[kanon_arm] theorem bv_mul_overflows.r_const.swap.proof : bv_mul_overflows.r_const.swap.Stmt := kanon_proof% bv_mul_overflows.r_const.swap

@[kanon_arm] theorem bv_mul_overflows.r_div.main.proof : bv_mul_overflows.r_div.main.Stmt := kanon_proof% bv_mul_overflows.r_div.main

@[kanon_arm] theorem bv_mul_overflows.r_default.main.proof : bv_mul_overflows.r_default.main.Stmt := kanon_proof% bv_mul_overflows.r_default.main

@[kanon_arm] theorem bv_neg_overflows.r_main.main.proof : bv_neg_overflows.r_main.main.Stmt := kanon_proof% bv_neg_overflows.r_main.main

@[kanon_arm] theorem bv_sub_overflows.r_lits.main.proof : bv_sub_overflows.r_lits.main.Stmt := kanon_proof% bv_sub_overflows.r_lits.main

@[kanon_arm] theorem bv_sub_overflows.r_same.main.proof : bv_sub_overflows.r_same.main.Stmt := kanon_proof% bv_sub_overflows.r_same.main

@[kanon_arm] theorem bv_sub_overflows.r_unsigned.main.proof : bv_sub_overflows.r_unsigned.main.Stmt := kanon_proof% bv_sub_overflows.r_unsigned.main

@[kanon_arm] theorem bv_sub_overflows.r_default.main.proof : bv_sub_overflows.r_default.main.Stmt := kanon_proof% bv_sub_overflows.r_default.main

@[kanon_arm] theorem bv_of_float.r_default.main.proof : bv_of_float.r_default.main.Stmt := kanon_proof% bv_of_float.r_default.main

@[kanon_arm] theorem bv_to_float.r_default.main.proof : bv_to_float.r_default.main.Stmt := kanon_proof% bv_to_float.r_default.main

@[kanon_arm] theorem bv_to_float_raw.r_default.main.proof : bv_to_float_raw.r_default.main.Stmt := kanon_proof% bv_to_float_raw.r_default.main

@[kanon_arm] theorem float_is_floatclass.r_lit.main.proof : float_is_floatclass.r_lit.main.Stmt := kanon_proof% float_is_floatclass.r_lit.main

@[kanon_arm] theorem float_is_floatclass.r_default.main.proof : float_is_floatclass.r_default.main.Stmt := kanon_proof% float_is_floatclass.r_default.main

@[kanon_arm] theorem float_is_negative.r_lit.main.proof : float_is_negative.r_lit.main.Stmt := kanon_proof% float_is_negative.r_lit.main

@[kanon_arm] theorem float_is_negative.r_default.main.proof : float_is_negative.r_default.main.Stmt := kanon_proof% float_is_negative.r_default.main

@[kanon_arm] theorem float_is_positive.r_lit.main.proof : float_is_positive.r_lit.main.Stmt := kanon_proof% float_is_positive.r_lit.main

@[kanon_arm] theorem float_is_positive.r_default.main.proof : float_is_positive.r_default.main.Stmt := kanon_proof% float_is_positive.r_default.main

@[kanon_arm] theorem float_cast.r_default.main.proof : float_cast.r_default.main.Stmt := kanon_proof% float_cast.r_default.main

@[kanon_arm] theorem float_eq.r_lits.main.proof : float_eq.r_lits.main.Stmt := kanon_proof% float_eq.r_lits.main

@[kanon_arm] theorem float_lt.r_lits.main.proof : float_lt.r_lits.main.Stmt := kanon_proof% float_lt.r_lits.main

@[kanon_arm] theorem float_lt.r_default.main.proof : float_lt.r_default.main.Stmt := kanon_proof% float_lt.r_default.main

@[kanon_arm] theorem float_leq.r_lits.main.proof : float_leq.r_lits.main.Stmt := kanon_proof% float_leq.r_lits.main

@[kanon_arm] theorem float_leq.r_default.main.proof : float_leq.r_default.main.Stmt := kanon_proof% float_leq.r_default.main

end Kanon
