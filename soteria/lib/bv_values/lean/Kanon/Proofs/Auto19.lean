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

@[kanon_arm] theorem Bitvec.ashr.r_lits.main.proof : Bitvec.ashr.r_lits.main.Stmt := by
  first | (kanon_shift; done) | kanon_auto

@[kanon_arm] theorem Bitvec.ashr.r_zero.main.proof : Bitvec.ashr.r_zero.main.Stmt := by
  first | (kanon_shift; done) | kanon_auto

@[kanon_arm] theorem Bitvec.ashr.r_big.main.proof : Bitvec.ashr.r_big.main.Stmt := by
  first | (kanon_shift; done) | kanon_auto

@[kanon_arm] theorem Bitvec.ashr.r_ashr.main.proof : Bitvec.ashr.r_ashr.main.Stmt := by
  first | (kanon_shift; done) | kanon_auto

@[kanon_arm] theorem Bitvec.ashr.r_default.main.proof : Bitvec.ashr.r_default.main.Stmt := by
  first | (kanon_shift; done) | kanon_auto

@[kanon_arm] theorem Bitvec.mul.r_lits.main.proof : Bitvec.mul.r_lits.main.Stmt := kanon_proof% Bitvec.mul.r_lits.main

@[kanon_arm] theorem Bitvec.mul.r_one.main.proof : Bitvec.mul.r_one.main.Stmt := kanon_proof% Bitvec.mul.r_one.main

@[kanon_arm] theorem Bitvec.mul.r_zero.main.proof : Bitvec.mul.r_zero.main.Stmt := kanon_proof% Bitvec.mul.r_zero.main

@[kanon_arm] theorem Bitvec.mul.r_neg.main.proof : Bitvec.mul.r_neg.main.Stmt := kanon_proof% Bitvec.mul.r_neg.main

@[kanon_arm] theorem Bitvec.mul.r_mul_const.main.proof : Bitvec.mul.r_mul_const.main.Stmt := kanon_proof% Bitvec.mul.r_mul_const.main
