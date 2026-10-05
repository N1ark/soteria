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

@[kanon_arm] theorem bv_extract.r_lshr.main.proof : bv_extract.r_lshr.main.Stmt := kanon_proof% bv_extract.r_lshr.main

@[kanon_arm] theorem bv_extract.r_ite.main.proof : bv_extract.r_ite.main.Stmt := kanon_proof% bv_extract.r_ite.main

@[kanon_arm] theorem bv_extract.r_zext_high.main.proof : bv_extract.r_zext_high.main.Stmt := kanon_proof% bv_extract.r_zext_high.main

@[kanon_arm] theorem bv_extract.r_sext_bit.main.proof : bv_extract.r_sext_bit.main.Stmt := kanon_proof% bv_extract.r_sext_bit.main

@[kanon_arm] theorem bv_extract.r_ext_low.main.proof : bv_extract.r_ext_low.main.Stmt := kanon_proof% bv_extract.r_ext_low.main

@[kanon_arm] theorem bv_extract.r_ext_orig.main.proof : bv_extract.r_ext_orig.main.Stmt := kanon_proof% bv_extract.r_ext_orig.main

@[kanon_arm] theorem bv_extract.r_extract.main.proof : bv_extract.r_extract.main.Stmt := kanon_proof% bv_extract.r_extract.main

@[kanon_arm] theorem bv_extract.r_concat.main.proof : bv_extract.r_concat.main.Stmt := kanon_proof% bv_extract.r_concat.main

@[kanon_arm] theorem bv_extract.r_add_low.main.proof : bv_extract.r_add_low.main.Stmt := kanon_proof% bv_extract.r_add_low.main

@[kanon_arm] theorem bv_extract.r_add_const.main.proof : bv_extract.r_add_const.main.Stmt := kanon_proof% bv_extract.r_add_const.main

@[kanon_arm] theorem bv_extract.r_mul_pow2.main.proof : bv_extract.r_mul_pow2.main.Stmt := kanon_proof% bv_extract.r_mul_pow2.main

@[kanon_arm] theorem bv_extract.r_mul_low.main.proof : bv_extract.r_mul_low.main.Stmt := kanon_proof% bv_extract.r_mul_low.main

@[kanon_arm] theorem bv_extract.r_urem.main.proof : bv_extract.r_urem.main.Stmt := kanon_proof% bv_extract.r_urem.main

@[kanon_arm] theorem bv_extract.r_default.main.proof : bv_extract.r_default.main.Stmt := kanon_proof% bv_extract.r_default.main

@[kanon_arm] theorem bv_extend.r_zero.main.proof : bv_extend.r_zero.main.Stmt := kanon_proof% bv_extend.r_zero.main

@[kanon_arm] theorem bv_extend.r_lit.main.proof : bv_extend.r_lit.main.Stmt := kanon_proof% bv_extend.r_lit.main

@[kanon_arm] theorem bv_extend.r_extend.main.proof : bv_extend.r_extend.main.Stmt := kanon_proof% bv_extend.r_extend.main

@[kanon_arm] theorem bv_extend.r_ite.main.proof : bv_extend.r_ite.main.Stmt := kanon_proof% bv_extend.r_ite.main

@[kanon_arm] theorem bv_extend.r_of_bool.main.proof : bv_extend.r_of_bool.main.Stmt := kanon_proof% bv_extend.r_of_bool.main

@[kanon_arm] theorem bv_extend.r_default.main.proof : bv_extend.r_default.main.Stmt := kanon_proof% bv_extend.r_default.main

@[kanon_arm] theorem bv_concat.r_lits.main.proof : bv_concat.r_lits.main.Stmt := kanon_proof% bv_concat.r_lits.main

@[kanon_arm] theorem bv_concat.r_extracts.main.proof : bv_concat.r_extracts.main.Stmt := kanon_proof% bv_concat.r_extracts.main

@[kanon_arm] theorem bv_concat.r_extract_extracts.main.proof : bv_concat.r_extract_extracts.main.Stmt := kanon_proof% bv_concat.r_extract_extracts.main

@[kanon_arm] theorem bv_concat.r_assoc_l.main.proof : bv_concat.r_assoc_l.main.Stmt := kanon_proof% bv_concat.r_assoc_l.main

@[kanon_arm] theorem bv_concat.r_assoc_r.main.proof : bv_concat.r_assoc_r.main.Stmt := kanon_proof% bv_concat.r_assoc_r.main

@[kanon_arm] theorem bv_concat.r_ites.main.proof : bv_concat.r_ites.main.Stmt := kanon_proof% bv_concat.r_ites.main

@[kanon_arm] theorem bv_concat.r_default.main.proof : bv_concat.r_default.main.Stmt := kanon_proof% bv_concat.r_default.main

@[kanon_arm] theorem bv_shl.r_lits.main.proof : bv_shl.r_lits.main.Stmt := kanon_proof% bv_shl.r_lits.main

@[kanon_arm] theorem bv_shl.r_zero.main.proof : bv_shl.r_zero.main.Stmt := kanon_proof% bv_shl.r_zero.main

@[kanon_arm] theorem bv_shl.r_big.main.proof : bv_shl.r_big.main.Stmt := kanon_proof% bv_shl.r_big.main

end Kanon
