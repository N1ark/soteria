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

@[kanon_arm] theorem Bitvec.neg.r_of_bool.main.proof : Bitvec.neg.r_of_bool.main.Stmt := by
  first | (kanon_rule_b; done) | kanon_auto

@[kanon_arm] theorem Bitvec.neg.r_default.main.proof : Bitvec.neg.r_default.main.Stmt := by
  first | (kanon_rule_b; done) | kanon_auto

@[kanon_arm] theorem Bitvec.mod_.r_lits.main.proof : Bitvec.mod_.r_lits.main.Stmt := by
  first | (kanon_rule_b; done) | kanon_auto

@[kanon_arm] theorem Bitvec.mod_.r_zero_r.main.proof : Bitvec.mod_.r_zero_r.main.Stmt := by
  first | (kanon_rule_b; done) | kanon_auto

@[kanon_arm] theorem Bitvec.mod_.r_default.main.proof : Bitvec.mod_.r_default.main.Stmt := by
  first | (kanon_rule_b; done) | kanon_auto

@[kanon_arm] theorem Bitvec.rem.r_lits.main.proof : Bitvec.rem.r_lits.main.Stmt := by
  first | (kanon_rule_b; done) | kanon_auto

@[kanon_arm] theorem Bitvec.rem.r_zero_r.main.proof : Bitvec.rem.r_zero_r.main.Stmt := by
  first | (kanon_rule_b; done) | kanon_auto

@[kanon_arm] theorem Bitvec.rem.r_zero_l.main.proof : Bitvec.rem.r_zero_l.main.Stmt := by
  first | (kanon_rule_b; done) | kanon_auto

@[kanon_arm] theorem Bitvec.rem.r_one_r.main.proof : Bitvec.rem.r_one_r.main.Stmt := by
  first | (kanon_rule_b; done) | kanon_auto

@[kanon_arm] theorem Bitvec.rem.r_pow2.main.proof : Bitvec.rem.r_pow2.main.Stmt := by
  first | (kanon_rule_b; done) | kanon_auto
