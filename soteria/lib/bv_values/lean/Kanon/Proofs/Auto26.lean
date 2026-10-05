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

@[kanon_arm] theorem Bitvec.leq.r_const_add.swap.proof : Bitvec.leq.r_const_add.swap.Stmt := by
  first | (kanon_cmp; done) | kanon_auto

@[kanon_arm] theorem Bitvec.leq.r_add_const.main.proof : Bitvec.leq.r_add_const.main.Stmt := by
  first | (kanon_cmp; done) | kanon_auto

@[kanon_arm] theorem Bitvec.leq.r_add_const.swap.proof : Bitvec.leq.r_add_const.swap.Stmt := by
  first | (kanon_cmp; done) | kanon_auto

@[kanon_arm] theorem Bitvec.leq.r_add_add.main.proof : Bitvec.leq.r_add_add.main.Stmt := by
  first | (kanon_cmp; done) | kanon_auto

@[kanon_arm] theorem Bitvec.leq.r_add_add.swap2.proof : Bitvec.leq.r_add_add.swap2.Stmt := by
  first | (kanon_cmp; done) | kanon_auto

@[kanon_arm] theorem Bitvec.leq.r_add_add.swap1.proof : Bitvec.leq.r_add_add.swap1.Stmt := by
  first | (kanon_cmp; done) | kanon_auto

@[kanon_arm] theorem Bitvec.leq.r_add_add.swap1_swap2.proof : Bitvec.leq.r_add_add.swap1_swap2.Stmt := by
  first | (kanon_cmp; done) | kanon_auto

@[kanon_arm] theorem Bitvec.leq.r_self_add_r.main.proof : Bitvec.leq.r_self_add_r.main.Stmt := by
  first | (kanon_cmp; done) | kanon_auto

@[kanon_arm] theorem Bitvec.leq.r_self_add_l.main.proof : Bitvec.leq.r_self_add_l.main.Stmt := by
  first | (kanon_cmp; done) | kanon_auto

@[kanon_arm] theorem Bitvec.leq.r_min_l.main.proof : Bitvec.leq.r_min_l.main.Stmt := by
  first | (kanon_cmp; done) | kanon_auto
