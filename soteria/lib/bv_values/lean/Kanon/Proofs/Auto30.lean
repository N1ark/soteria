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

@[kanon_arm] theorem bv_leq.r_default.main.proof : bv_leq.r_default.main.Stmt := kanon_proof% bv_leq.r_default.main

@[kanon_arm] theorem bv_add_overflows.r_lits.main.proof : bv_add_overflows.r_lits.main.Stmt := kanon_proof% bv_add_overflows.r_lits.main

@[kanon_arm] theorem bv_add_overflows.r_zero.main.proof : bv_add_overflows.r_zero.main.Stmt := kanon_proof% bv_add_overflows.r_zero.main

@[kanon_arm] theorem bv_add_overflows.r_size1.main.proof : bv_add_overflows.r_size1.main.Stmt := kanon_proof% bv_add_overflows.r_size1.main

@[kanon_arm] theorem bv_add_overflows.r_unsigned.main.proof : bv_add_overflows.r_unsigned.main.Stmt := kanon_proof% bv_add_overflows.r_unsigned.main

@[kanon_arm] theorem bv_add_overflows.r_unsigned.swap.proof : bv_add_overflows.r_unsigned.swap.Stmt := kanon_proof% bv_add_overflows.r_unsigned.swap

@[kanon_arm] theorem bv_add_overflows.r_signed.main.proof : bv_add_overflows.r_signed.main.Stmt := kanon_proof% bv_add_overflows.r_signed.main

@[kanon_arm] theorem bv_add_overflows.r_signed.swap.proof : bv_add_overflows.r_signed.swap.Stmt := kanon_proof% bv_add_overflows.r_signed.swap

@[kanon_arm] theorem bv_add_overflows.r_of_bools.main.proof : bv_add_overflows.r_of_bools.main.Stmt := kanon_proof% bv_add_overflows.r_of_bools.main

@[kanon_arm] theorem bv_add_overflows.r_of_bool.main.proof : bv_add_overflows.r_of_bool.main.Stmt := kanon_proof% bv_add_overflows.r_of_bool.main

end Kanon
