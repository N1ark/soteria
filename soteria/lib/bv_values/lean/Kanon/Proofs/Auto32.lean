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

@[kanon_arm] theorem Float.add.r_default.main.proof : Float.add.r_default.main.Stmt := by
  first | (kanon_float; done) | kanon_auto

@[kanon_arm] theorem Float.sub.r_lits.main.proof : Float.sub.r_lits.main.Stmt := by
  first | (kanon_float; done) | kanon_auto

@[kanon_arm] theorem Float.sub.r_default.main.proof : Float.sub.r_default.main.Stmt := by
  first | (kanon_float; done) | kanon_auto

@[kanon_arm] theorem Float.div.r_lits.main.proof : Float.div.r_lits.main.Stmt := by
  first | (kanon_float; done) | kanon_auto

@[kanon_arm] theorem Float.div.r_default.main.proof : Float.div.r_default.main.Stmt := by
  first | (kanon_float; done) | kanon_auto

@[kanon_arm] theorem Float.mul.r_lits.main.proof : Float.mul.r_lits.main.Stmt := by
  first | (kanon_float; done) | kanon_auto

@[kanon_arm] theorem Float.mul.r_default.main.proof : Float.mul.r_default.main.Stmt := by
  first | (kanon_float; done) | kanon_auto

@[kanon_arm] theorem Float.rem.r_lits.main.proof : Float.rem.r_lits.main.Stmt := by
  first | (kanon_float; done) | kanon_auto

@[kanon_arm] theorem Float.rem.r_default.main.proof : Float.rem.r_default.main.Stmt := by
  first | (kanon_float; done) | kanon_auto

@[kanon_arm] theorem Float.abs.r_lit.main.proof : Float.abs.r_lit.main.Stmt := by
  first | (kanon_float; done) | kanon_auto
