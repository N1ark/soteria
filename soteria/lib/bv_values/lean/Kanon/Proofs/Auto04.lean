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

@[kanon_arm] theorem Bool.eq.r_bvs.bitVec_bitVec.proof : Bool.eq.r_bvs.bitVec_bitVec.Stmt := by
  first | (kanon_rule_b; done) | kanon_auto

@[kanon_arm] theorem Bool.eq.r_bvs.locLit_locLit.proof : Bool.eq.r_bvs.locLit_locLit.Stmt := by
  first | (kanon_rule_b; done) | kanon_auto

@[kanon_arm] theorem Bool.eq.r_neg.main.proof : Bool.eq.r_neg.main.Stmt := by
  first | (kanon_rule_b; done) | kanon_auto

@[kanon_arm] theorem Bool.eq.r_not.main.proof : Bool.eq.r_not.main.Stmt := by
  first | (kanon_rule_b; done) | kanon_auto

@[kanon_arm] theorem Bool.eq.r_add_const.main.proof : Bool.eq.r_add_const.main.Stmt := by
  first | (kanon_rule_b; done) | kanon_auto

@[kanon_arm] theorem Bool.eq.r_sub_const1.main.proof : Bool.eq.r_sub_const1.main.Stmt := by
  first | (kanon_rule_b; done) | kanon_auto

@[kanon_arm] theorem Bool.eq.r_sub_const2.main.proof : Bool.eq.r_sub_const2.main.Stmt := by
  first | (kanon_rule_b; done) | kanon_auto

@[kanon_arm] theorem Bool.eq.r_self_add.main.proof : Bool.eq.r_self_add.main.Stmt := by
  first | (kanon_rule_b; done) | kanon_auto

@[kanon_arm] theorem Bool.eq.r_add_add.main.proof : Bool.eq.r_add_add.main.Stmt := by
  first | (kanon_rule_b; done) | kanon_auto

@[kanon_arm] theorem Bool.eq.r_or_zero.main.proof : Bool.eq.r_or_zero.main.Stmt := by
  first | (kanon_rule_b; done) | kanon_auto
