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

@[kanon_arm] theorem Bitvec.concat.r_extract_extracts.main.proof : Bitvec.concat.r_extract_extracts.main.Stmt := kanon_proof% Bitvec.concat.r_extract_extracts.main

@[kanon_arm] theorem Bitvec.concat.r_assoc_l.main.proof : Bitvec.concat.r_assoc_l.main.Stmt := kanon_proof% Bitvec.concat.r_assoc_l.main

@[kanon_arm] theorem Bitvec.concat.r_assoc_r.main.proof : Bitvec.concat.r_assoc_r.main.Stmt := kanon_proof% Bitvec.concat.r_assoc_r.main

@[kanon_arm] theorem Bitvec.concat.r_ites.main.proof : Bitvec.concat.r_ites.main.Stmt := kanon_proof% Bitvec.concat.r_ites.main

@[kanon_arm] theorem Bitvec.concat.r_default.main.proof : Bitvec.concat.r_default.main.Stmt := kanon_proof% Bitvec.concat.r_default.main

@[kanon_arm] theorem Bitvec.shl.r_lits.main.proof : Bitvec.shl.r_lits.main.Stmt := by
  first | (kanon_shift; done) | kanon_auto

@[kanon_arm] theorem Bitvec.shl.r_zero.main.proof : Bitvec.shl.r_zero.main.Stmt := by
  first | (kanon_shift; done) | kanon_auto

@[kanon_arm] theorem Bitvec.shl.r_big.main.proof : Bitvec.shl.r_big.main.Stmt := by
  first | (kanon_shift; done) | kanon_auto

@[kanon_arm] theorem Bitvec.shl.r_shl.main.proof : Bitvec.shl.r_shl.main.Stmt := by
  first | (kanon_shift; done) | kanon_auto

@[kanon_arm] theorem Bitvec.shl.r_lshr.main.proof : Bitvec.shl.r_lshr.main.Stmt := by
  first | (kanon_shift; done) | kanon_auto
