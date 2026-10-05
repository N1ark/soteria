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

@[kanon_arm] theorem Float.is_positive.r_lit.main.proof : Float.is_positive.r_lit.main.Stmt := by
  first | (kanon_float; done) | kanon_auto

@[kanon_arm] theorem Float.is_positive.r_default.main.proof : Float.is_positive.r_default.main.Stmt := by
  first | (kanon_float; done) | kanon_auto

@[kanon_arm] theorem Float.cast.r_default.main.proof : Float.cast.r_default.main.Stmt := by
  first | (kanon_float; done) | kanon_auto

@[kanon_arm] theorem Float.eq.r_lits.main.proof : Float.eq.r_lits.main.Stmt := by
  first | (kanon_float; done) | kanon_auto

@[kanon_arm] theorem Float.lt.r_lits.main.proof : Float.lt.r_lits.main.Stmt := by
  first | (kanon_float; done) | kanon_auto

@[kanon_arm] theorem Float.lt.r_default.main.proof : Float.lt.r_default.main.Stmt := by
  first | (kanon_float; done) | kanon_auto

@[kanon_arm] theorem Float.leq.r_lits.main.proof : Float.leq.r_lits.main.Stmt := by
  first | (kanon_float; done) | kanon_auto

@[kanon_arm] theorem Float.leq.r_default.main.proof : Float.leq.r_default.main.Stmt := by
  first | (kanon_float; done) | kanon_auto

@[kanon_arm] theorem Float.add.r_lits.main.proof : Float.add.r_lits.main.Stmt := by
  first | (kanon_float; done) | kanon_auto

@[kanon_arm] theorem Float.add.r_default.main.proof : Float.add.r_default.main.Stmt := by
  first | (kanon_float; done) | kanon_auto
