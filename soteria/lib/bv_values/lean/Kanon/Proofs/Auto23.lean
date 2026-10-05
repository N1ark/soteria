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

@[kanon_arm] theorem Bitvec.lt.r_add_add.swap2.proof : Bitvec.lt.r_add_add.swap2.Stmt := by
  first | (kanon_cmp; done) | kanon_auto

@[kanon_arm] theorem Bitvec.lt.r_add_add.swap1.proof : Bitvec.lt.r_add_add.swap1.Stmt := by
  first | (kanon_cmp; done) | kanon_auto

@[kanon_arm] theorem Bitvec.lt.r_add_add.swap1_swap2.proof : Bitvec.lt.r_add_add.swap1_swap2.Stmt := by
  first | (kanon_cmp; done) | kanon_auto

@[kanon_arm] theorem Bitvec.lt.r_one.main.proof : Bitvec.lt.r_one.main.Stmt := by
  first | (kanon_cmp; done) | kanon_auto

@[kanon_arm] theorem Bitvec.lt.r_of_bool.main.proof : Bitvec.lt.r_of_bool.main.Stmt := by
  first | (kanon_cmp; done) | kanon_auto

@[kanon_arm] theorem Bitvec.lt.r_ite_l.main.proof : Bitvec.lt.r_ite_l.main.Stmt := by
  first | (kanon_cmp; done) | kanon_auto

@[kanon_arm] theorem Bitvec.lt.r_ite_r.main.proof : Bitvec.lt.r_ite_r.main.Stmt := by
  first | (kanon_cmp; done) | kanon_auto

@[kanon_arm] theorem Bitvec.lt.r_lt_zero.main.proof : Bitvec.lt.r_lt_zero.main.Stmt := by
  first | (kanon_cmp; done) | kanon_auto

@[kanon_arm] theorem Bitvec.lt.r_max_l.main.proof : Bitvec.lt.r_max_l.main.Stmt := by
  first | (kanon_cmp; done) | kanon_auto

@[kanon_arm] theorem Bitvec.lt.r_min_r.main.proof : Bitvec.lt.r_min_r.main.Stmt := by
  first | (kanon_cmp; done) | kanon_auto
