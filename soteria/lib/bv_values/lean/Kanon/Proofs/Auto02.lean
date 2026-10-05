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

@[kanon_arm] theorem Bool.or_.r_complementary.lt_lt.proof : Bool.or_.r_complementary.lt_lt.Stmt := kanon_proof% Bool.or_.r_complementary.lt_lt

@[kanon_arm] theorem Bool.or_.r_complementary.lt_leq.proof : Bool.or_.r_complementary.lt_leq.Stmt := kanon_proof% Bool.or_.r_complementary.lt_leq

@[kanon_arm] theorem Bool.or_.r_complementary.leq_lt.proof : Bool.or_.r_complementary.leq_lt.Stmt := kanon_proof% Bool.or_.r_complementary.leq_lt

@[kanon_arm] theorem Bool.or_.r_complementary.leq_leq.proof : Bool.or_.r_complementary.leq_leq.Stmt := kanon_proof% Bool.or_.r_complementary.leq_leq

@[kanon_arm] theorem Bool.or_.r_upper_eq.lt.proof : Bool.or_.r_upper_eq.lt.Stmt := kanon_proof% Bool.or_.r_upper_eq.lt

@[kanon_arm] theorem Bool.or_.r_upper_eq.leq.proof : Bool.or_.r_upper_eq.leq.Stmt := kanon_proof% Bool.or_.r_upper_eq.leq

@[kanon_arm] theorem Bool.or_.r_lower_eq.lt.proof : Bool.or_.r_lower_eq.lt.Stmt := kanon_proof% Bool.or_.r_lower_eq.lt

@[kanon_arm] theorem Bool.or_.r_lower_eq.leq.proof : Bool.or_.r_lower_eq.leq.Stmt := kanon_proof% Bool.or_.r_lower_eq.leq

@[kanon_arm] theorem Bool.or_.r_upper_bounds.lt_lt.proof : Bool.or_.r_upper_bounds.lt_lt.Stmt := kanon_proof% Bool.or_.r_upper_bounds.lt_lt

@[kanon_arm] theorem Bool.or_.r_upper_bounds.lt_leq.proof : Bool.or_.r_upper_bounds.lt_leq.Stmt := kanon_proof% Bool.or_.r_upper_bounds.lt_leq
