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

@[kanon_arm] theorem Bitvec.lt.r_negs.main.proof : Bitvec.lt.r_negs.main.Stmt := by
  first | (kanon_cmp; done) | kanon_auto

@[kanon_arm] theorem Bitvec.lt.r_neg_l.main.proof : Bitvec.lt.r_neg_l.main.Stmt := by
  first | (kanon_cmp; done) | kanon_auto

@[kanon_arm] theorem Bitvec.lt.r_neg_r.main.proof : Bitvec.lt.r_neg_r.main.Stmt := by
  first | (kanon_cmp; done) | kanon_auto

@[kanon_arm] theorem Bitvec.lt.r_const_add.main.proof : Bitvec.lt.r_const_add.main.Stmt := by
  first | (kanon_cmp; done) | kanon_auto

@[kanon_arm] theorem Bitvec.lt.r_const_add.swap.proof : Bitvec.lt.r_const_add.swap.Stmt := by
  first | (kanon_cmp; done) | kanon_auto

@[kanon_arm] theorem Bitvec.lt.r_add_const.main.proof : Bitvec.lt.r_add_const.main.Stmt := by
  first | (kanon_cmp; done) | kanon_auto

@[kanon_arm] theorem Bitvec.lt.r_add_const.swap.proof : Bitvec.lt.r_add_const.swap.Stmt := by
  first | (kanon_cmp; done) | kanon_auto

@[kanon_arm] theorem Bitvec.lt.r_self_add_r.main.proof : Bitvec.lt.r_self_add_r.main.Stmt := by
  first | (kanon_cmp; done) | kanon_auto

@[kanon_arm] theorem Bitvec.lt.r_self_add_l.main.proof : Bitvec.lt.r_self_add_l.main.Stmt := by
  first | (kanon_cmp; done) | kanon_auto

@[kanon_arm] theorem Bitvec.lt.r_add_add.main.proof : Bitvec.lt.r_add_add.main.Stmt := by
  first | (kanon_cmp; done) | kanon_auto
