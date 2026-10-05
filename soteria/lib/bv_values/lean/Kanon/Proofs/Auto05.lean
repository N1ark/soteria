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

@[kanon_arm] theorem Bool.eq.r_concat_const.main.proof : Bool.eq.r_concat_const.main.Stmt := by
  first | (kanon_rule_b; done) | kanon_auto

@[kanon_arm] theorem Bool.eq.r_concat_concat.main.proof : Bool.eq.r_concat_concat.main.Stmt := by
  first | (kanon_rule_b; done) | kanon_auto

@[kanon_arm] theorem Bool.eq.r_ite_const.bitVec.proof : Bool.eq.r_ite_const.bitVec.Stmt := by
  first | (kanon_rule_b; done) | kanon_auto

@[kanon_arm] theorem Bool.eq.r_ite_const.locLit.proof : Bool.eq.r_ite_const.locLit.Stmt := by
  first | (kanon_rule_b; done) | kanon_auto

@[kanon_arm] theorem Bool.eq.r_of_bools.main.proof : Bool.eq.r_of_bools.main.Stmt := by
  first | (kanon_rule_b; done) | kanon_auto

@[kanon_arm] theorem Bool.eq.r_of_bool_const.main.proof : Bool.eq.r_of_bool_const.main.Stmt := by
  first | (kanon_rule_b; done) | kanon_auto

@[kanon_arm] theorem Bool.eq.r_msb.main.proof : Bool.eq.r_msb.main.Stmt := by
  first | (kanon_rule_b; done) | kanon_auto

@[kanon_arm] theorem Bool.eq.r_floats.main.proof : Bool.eq.r_floats.main.Stmt := by
  first | (kanon_rule_b; done) | kanon_auto

@[kanon_arm] theorem Bool.eq.r_ptrs.main.proof : Bool.eq.r_ptrs.main.Stmt := by
  first | (kanon_rule_b; done) | kanon_auto

@[kanon_arm] theorem Bitvec.of_bool.r_true_.main.proof : Bitvec.of_bool.r_true_.main.Stmt := kanon_proof% Bitvec.of_bool.r_true_.main
