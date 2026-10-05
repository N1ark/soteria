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

@[kanon_arm] theorem Float.sqrt.r_default.main.proof : Float.sqrt.r_default.main.Stmt := by
  first | (kanon_float; done) | kanon_auto

@[kanon_arm] theorem Float.round.r_lit.main.proof : Float.round.r_lit.main.Stmt := by
  first | (kanon_float; done) | kanon_auto

@[kanon_arm] theorem Float.round.r_default.main.proof : Float.round.r_default.main.Stmt := by
  first | (kanon_float; done) | kanon_auto

@[kanon_arm] theorem Ptr.loc.r_ptr.main.proof : Ptr.loc.r_ptr.main.Stmt := by
  first | (kanon_ptr Ptr.loc.spec; done) | kanon_auto

@[kanon_arm] theorem Ptr.loc.r_default.main.proof : Ptr.loc.r_default.main.Stmt := by
  first | (kanon_ptr Ptr.loc.spec; done) | kanon_auto

@[kanon_arm] theorem Ptr.ofs.r_ptr.main.proof : Ptr.ofs.r_ptr.main.Stmt := by
  first | (kanon_ptr Ptr.ofs.spec; done) | kanon_auto

@[kanon_arm] theorem Ptr.ofs.r_default.main.proof : Ptr.ofs.r_default.main.Stmt := by
  first | (kanon_ptr Ptr.ofs.spec; done) | kanon_auto

@[kanon_arm] theorem Bitvec.to_float_bits.r_default.main.proof : Bitvec.to_float_bits.r_default.main.Stmt := kanon_proof% Bitvec.to_float_bits.r_default.main
