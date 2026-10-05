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

@[kanon_arm] theorem Bitvec.add_overflows.r_of_bools.main.proof : Bitvec.add_overflows.r_of_bools.main.Stmt := by
  first | (kanon_rule_b; done) | kanon_auto

@[kanon_arm] theorem Bitvec.add_overflows.r_of_bool.main.proof : Bitvec.add_overflows.r_of_bool.main.Stmt := by
  first | (kanon_rule_b; done) | kanon_auto

@[kanon_arm] theorem Bitvec.add_overflows.r_default.main.proof : Bitvec.add_overflows.r_default.main.Stmt := by
  first | (kanon_rule_b; done) | kanon_auto

@[kanon_arm] theorem Bitvec.mul_overflows.r_lits.main.proof : Bitvec.mul_overflows.r_lits.main.Stmt := by
  first | (kanon_rule_b; done) | kanon_auto

@[kanon_arm] theorem Bitvec.mul_overflows.r_size1.main.proof : Bitvec.mul_overflows.r_size1.main.Stmt := by
  first | (kanon_rule_b; done) | kanon_auto

@[kanon_arm] theorem Bitvec.mul_overflows.r_msb.main.proof : Bitvec.mul_overflows.r_msb.main.Stmt := by
  first | (kanon_rule_b; done) | kanon_auto

@[kanon_arm] theorem Bitvec.mul_overflows.r_const.main.proof : Bitvec.mul_overflows.r_const.main.Stmt := by
  first | (kanon_rule_b; done) | kanon_auto

@[kanon_arm] theorem Bitvec.mul_overflows.r_div.main.proof : Bitvec.mul_overflows.r_div.main.Stmt := by
  first | (kanon_rule_b; done) | kanon_auto

@[kanon_arm] theorem Bitvec.mul_overflows.r_default.main.proof : Bitvec.mul_overflows.r_default.main.Stmt := by
  first | (kanon_rule_b; done) | kanon_auto

@[kanon_arm] theorem Bitvec.neg_overflows.r_main.main.proof : Bitvec.neg_overflows.r_main.main.Stmt := by
  first | (kanon_rule_b; done) | kanon_auto
