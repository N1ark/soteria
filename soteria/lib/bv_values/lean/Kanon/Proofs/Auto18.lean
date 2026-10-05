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

@[kanon_arm] theorem Bitvec.shl.r_and_mask.main.proof : Bitvec.shl.r_and_mask.main.Stmt := by
  first | (kanon_shift; done) | kanon_auto

@[kanon_arm] theorem Bitvec.shl.r_or_mask.main.proof : Bitvec.shl.r_or_mask.main.Stmt := by
  first | (kanon_shift; done) | kanon_auto

@[kanon_arm] theorem Bitvec.shl.r_default.main.proof : Bitvec.shl.r_default.main.Stmt := by
  first | (kanon_shift; done) | kanon_auto

@[kanon_arm] theorem Bitvec.lshr.r_lits.main.proof : Bitvec.lshr.r_lits.main.Stmt := by
  first | (kanon_shift; done) | kanon_auto

@[kanon_arm] theorem Bitvec.lshr.r_zero.main.proof : Bitvec.lshr.r_zero.main.Stmt := by
  first | (kanon_shift; done) | kanon_auto

@[kanon_arm] theorem Bitvec.lshr.r_big.main.proof : Bitvec.lshr.r_big.main.Stmt := by
  first | (kanon_shift; done) | kanon_auto

@[kanon_arm] theorem Bitvec.lshr.r_lshr.main.proof : Bitvec.lshr.r_lshr.main.Stmt := by
  first | (kanon_shift; done) | kanon_auto

@[kanon_arm] theorem Bitvec.lshr.r_and_mask.main.proof : Bitvec.lshr.r_and_mask.main.Stmt := by
  first | (kanon_shift; done) | kanon_auto

@[kanon_arm] theorem Bitvec.lshr.r_or_mask.main.proof : Bitvec.lshr.r_or_mask.main.Stmt := by
  first | (kanon_shift; done) | kanon_auto

@[kanon_arm] theorem Bitvec.lshr.r_default.main.proof : Bitvec.lshr.r_default.main.Stmt := by
  first | (kanon_shift; done) | kanon_auto
