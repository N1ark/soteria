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

@[kanon_arm] theorem Bitvec.sub_overflows.r_lits.main.proof : Bitvec.sub_overflows.r_lits.main.Stmt := by
  first | (kanon_rule_b; done) | kanon_auto

@[kanon_arm] theorem Bitvec.sub_overflows.r_same.main.proof : Bitvec.sub_overflows.r_same.main.Stmt := by
  first | (kanon_rule_b; done) | kanon_auto

@[kanon_arm] theorem Bitvec.sub_overflows.r_unsigned.main.proof : Bitvec.sub_overflows.r_unsigned.main.Stmt := by
  first | (kanon_rule_b; done) | kanon_auto

@[kanon_arm] theorem Bitvec.sub_overflows.r_default.main.proof : Bitvec.sub_overflows.r_default.main.Stmt := by
  first | (kanon_rule_b; done) | kanon_auto

@[kanon_arm] theorem Bitvec.of_float.r_default.main.proof : Bitvec.of_float.r_default.main.Stmt := kanon_proof% Bitvec.of_float.r_default.main

@[kanon_arm] theorem Bitvec.to_float.r_default.main.proof : Bitvec.to_float.r_default.main.Stmt := kanon_proof% Bitvec.to_float.r_default.main

@[kanon_arm] theorem Float.is_floatclass.r_lit.main.proof : Float.is_floatclass.r_lit.main.Stmt := by
  first | (kanon_float; done) | kanon_auto

@[kanon_arm] theorem Float.is_floatclass.r_default.main.proof : Float.is_floatclass.r_default.main.Stmt := by
  first | (kanon_float; done) | kanon_auto

@[kanon_arm] theorem Float.is_negative.r_lit.main.proof : Float.is_negative.r_lit.main.Stmt := by
  first | (kanon_float; done) | kanon_auto

@[kanon_arm] theorem Float.is_negative.r_default.main.proof : Float.is_negative.r_default.main.Stmt := by
  first | (kanon_float; done) | kanon_auto
