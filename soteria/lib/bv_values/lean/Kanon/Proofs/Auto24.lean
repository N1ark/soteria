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

@[kanon_arm] theorem Bitvec.lt.r_min_l.main.proof : Bitvec.lt.r_min_l.main.Stmt := by
  first | (kanon_cmp; done) | kanon_auto

@[kanon_arm] theorem Bitvec.lt.r_max_r.main.proof : Bitvec.lt.r_max_r.main.Stmt := by
  first | (kanon_cmp; done) | kanon_auto

@[kanon_arm] theorem Bitvec.lt.r_const_mul.main.proof : Bitvec.lt.r_const_mul.main.Stmt := by
  first | (kanon_cmp; done) | kanon_auto

@[kanon_arm] theorem Bitvec.lt.r_mul_const.main.proof : Bitvec.lt.r_mul_const.main.Stmt := by
  first | (kanon_cmp; done) | kanon_auto

@[kanon_arm] theorem Bitvec.lt.r_mul_mul.main.proof : Bitvec.lt.r_mul_mul.main.Stmt := by
  first | (kanon_cmp; done) | kanon_auto

@[kanon_arm] theorem Bitvec.lt.r_const_sub1.main.proof : Bitvec.lt.r_const_sub1.main.Stmt := by
  first | (kanon_cmp; done) | kanon_auto

@[kanon_arm] theorem Bitvec.lt.r_const_sub2.main.proof : Bitvec.lt.r_const_sub2.main.Stmt := by
  first | (kanon_cmp; done) | kanon_auto

@[kanon_arm] theorem Bitvec.lt.r_sub_const1.main.proof : Bitvec.lt.r_sub_const1.main.Stmt := by
  first | (kanon_cmp; done) | kanon_auto

@[kanon_arm] theorem Bitvec.lt.r_sub_const2.main.proof : Bitvec.lt.r_sub_const2.main.Stmt := by
  first | (kanon_cmp; done) | kanon_auto

@[kanon_arm] theorem Bitvec.lt.r_ub_r.main.proof : Bitvec.lt.r_ub_r.main.Stmt := by
  first | (kanon_cmp; done) | kanon_auto
