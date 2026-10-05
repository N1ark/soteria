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

@[kanon_arm] theorem b_and.r_upper_bounds.lt_lt.proof : b_and.r_upper_bounds.lt_lt.Stmt := kanon_proof% b_and.r_upper_bounds.lt_lt

@[kanon_arm] theorem b_and.r_upper_bounds.lt_leq.proof : b_and.r_upper_bounds.lt_leq.Stmt := kanon_proof% b_and.r_upper_bounds.lt_leq

@[kanon_arm] theorem b_and.r_upper_bounds.leq_lt.proof : b_and.r_upper_bounds.leq_lt.Stmt := kanon_proof% b_and.r_upper_bounds.leq_lt

@[kanon_arm] theorem b_and.r_upper_bounds.leq_leq.proof : b_and.r_upper_bounds.leq_leq.Stmt := kanon_proof% b_and.r_upper_bounds.leq_leq

@[kanon_arm] theorem b_and.r_lower_bounds.lt_lt.proof : b_and.r_lower_bounds.lt_lt.Stmt := kanon_proof% b_and.r_lower_bounds.lt_lt

@[kanon_arm] theorem b_and.r_lower_bounds.lt_leq.proof : b_and.r_lower_bounds.lt_leq.Stmt := kanon_proof% b_and.r_lower_bounds.lt_leq

@[kanon_arm] theorem b_and.r_lower_bounds.leq_lt.proof : b_and.r_lower_bounds.leq_lt.Stmt := kanon_proof% b_and.r_lower_bounds.leq_lt

@[kanon_arm] theorem b_and.r_lower_bounds.leq_leq.proof : b_and.r_lower_bounds.leq_leq.Stmt := kanon_proof% b_and.r_lower_bounds.leq_leq

@[kanon_arm] theorem b_or.r_lt_lt.main.proof : b_or.r_lt_lt.main.Stmt := kanon_proof% b_or.r_lt_lt.main

@[kanon_arm] theorem b_or.r_lt_leq.main.proof : b_or.r_lt_leq.main.Stmt := kanon_proof% b_or.r_lt_leq.main

@[kanon_arm] theorem b_or.r_complementary.lt_lt.proof : b_or.r_complementary.lt_lt.Stmt := kanon_proof% b_or.r_complementary.lt_lt

@[kanon_arm] theorem b_or.r_complementary.lt_leq.proof : b_or.r_complementary.lt_leq.Stmt := kanon_proof% b_or.r_complementary.lt_leq

@[kanon_arm] theorem b_or.r_complementary.leq_lt.proof : b_or.r_complementary.leq_lt.Stmt := kanon_proof% b_or.r_complementary.leq_lt

@[kanon_arm] theorem b_or.r_complementary.leq_leq.proof : b_or.r_complementary.leq_leq.Stmt := kanon_proof% b_or.r_complementary.leq_leq

@[kanon_arm] theorem b_or.r_upper_eq.lt.proof : b_or.r_upper_eq.lt.Stmt := kanon_proof% b_or.r_upper_eq.lt

@[kanon_arm] theorem b_or.r_upper_eq.leq.proof : b_or.r_upper_eq.leq.Stmt := kanon_proof% b_or.r_upper_eq.leq

@[kanon_arm] theorem b_or.r_lower_eq.lt.proof : b_or.r_lower_eq.lt.Stmt := kanon_proof% b_or.r_lower_eq.lt

@[kanon_arm] theorem b_or.r_lower_eq.leq.proof : b_or.r_lower_eq.leq.Stmt := kanon_proof% b_or.r_lower_eq.leq

@[kanon_arm] theorem b_or.r_upper_bounds.lt_lt.proof : b_or.r_upper_bounds.lt_lt.Stmt := kanon_proof% b_or.r_upper_bounds.lt_lt

@[kanon_arm] theorem b_or.r_upper_bounds.lt_leq.proof : b_or.r_upper_bounds.lt_leq.Stmt := kanon_proof% b_or.r_upper_bounds.lt_leq

@[kanon_arm] theorem b_or.r_upper_bounds.leq_lt.proof : b_or.r_upper_bounds.leq_lt.Stmt := kanon_proof% b_or.r_upper_bounds.leq_lt

@[kanon_arm] theorem b_or.r_upper_bounds.leq_leq.proof : b_or.r_upper_bounds.leq_leq.Stmt := kanon_proof% b_or.r_upper_bounds.leq_leq

@[kanon_arm] theorem b_or.r_lower_bounds.lt_lt.proof : b_or.r_lower_bounds.lt_lt.Stmt := kanon_proof% b_or.r_lower_bounds.lt_lt

@[kanon_arm] theorem b_or.r_lower_bounds.lt_leq.proof : b_or.r_lower_bounds.lt_leq.Stmt := kanon_proof% b_or.r_lower_bounds.lt_leq

@[kanon_arm] theorem b_or.r_lower_bounds.leq_lt.proof : b_or.r_lower_bounds.leq_lt.Stmt := kanon_proof% b_or.r_lower_bounds.leq_lt

@[kanon_arm] theorem b_or.r_lower_bounds.leq_leq.proof : b_or.r_lower_bounds.leq_leq.Stmt := kanon_proof% b_or.r_lower_bounds.leq_leq

@[kanon_arm] theorem b_not.r_lt.main.proof : b_not.r_lt.main.Stmt := kanon_proof% b_not.r_lt.main

@[kanon_arm] theorem b_not.r_leq.main.proof : b_not.r_leq.main.Stmt := kanon_proof% b_not.r_leq.main

@[kanon_arm] theorem b_not.r_eq_bit.main.proof : b_not.r_eq_bit.main.Stmt := kanon_proof% b_not.r_eq_bit.main

@[kanon_arm] theorem b_ite.r_bv_of_bool.main.proof : b_ite.r_bv_of_bool.main.Stmt := kanon_proof% b_ite.r_bv_of_bool.main

end Kanon
