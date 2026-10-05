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

@[kanon_arm] theorem Bitvec.div.r_default.main.proof : Bitvec.div.r_default.main.Stmt := kanon_proof% Bitvec.div.r_default.main

@[kanon_arm] theorem Bitvec.lt_zero.r_sext.main.proof : Bitvec.lt_zero.r_sext.main.Stmt := by
  first | (kanon_msb; done) | kanon_auto

@[kanon_arm] theorem Bitvec.lt_zero.r_zext.main.proof : Bitvec.lt_zero.r_zext.main.Stmt := by
  first | (kanon_msb; done) | kanon_auto

@[kanon_arm] theorem Bitvec.lt_zero.r_srem.main.proof : Bitvec.lt_zero.r_srem.main.Stmt := by
  first | (kanon_msb; done) | kanon_auto

@[kanon_arm] theorem Bitvec.lt_zero.r_concat.main.proof : Bitvec.lt_zero.r_concat.main.Stmt := by
  first | (kanon_msb; done) | kanon_auto

@[kanon_arm] theorem Bitvec.lt_zero.r_not.main.proof : Bitvec.lt_zero.r_not.main.Stmt := by
  first | (kanon_msb; done) | kanon_auto

@[kanon_arm] theorem Bitvec.lt_zero.r_of_bool.main.proof : Bitvec.lt_zero.r_of_bool.main.Stmt := by
  first | (kanon_msb; done) | kanon_auto

@[kanon_arm] theorem Bitvec.lt_zero.r_default.main.proof : Bitvec.lt_zero.r_default.main.Stmt := by
  first | (kanon_msb; done) | kanon_auto

@[kanon_arm] theorem Bitvec.lt.r_lits.main.proof : Bitvec.lt.r_lits.main.Stmt := by
  first | (kanon_cmp; done) | kanon_auto

@[kanon_arm] theorem Bitvec.lt.r_same.main.proof : Bitvec.lt.r_same.main.Stmt := by
  first | (kanon_cmp; done) | kanon_auto
